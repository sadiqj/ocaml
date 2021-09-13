/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*                          Sadiq Jaffer, Opsian                          */
/*                                                                        */
/*   Copyright 2021 Opsian Ltd                                            */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#define CAML_INTERNALS

#include "caml/custom.h"
#include "caml/fail.h"
#include "caml/mlvalues.h"
#include "caml/memory.h"
#include "caml/osdeps.h"
#include "caml/eventring.h"

#include <fcntl.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <string.h>

#ifdef _WIN32
#include <wtypes.h>
#include <process.h>
#elif defined(HAS_UNISTD)
#include <unistd.h>
#endif

#ifdef HAS_MACH_ABSOLUTE_TIME
#include <mach/mach_time.h>
#elif HAS_POSIX_MONOTONIC_CLOCK
#include <time.h>
#endif

#define RING_FILE_NAME_LEN 4096
#define RING_BUFFER_SIZE (1 << 18)

typedef enum
{
  EV_RUNTIME,
  EV_USER
} ev_category;

struct ring_buffer_header
{
  uint64_t version;
  atomic_uint_fast64_t ring_size; /* Ring size in 64-bit elements */
  atomic_uint_fast64_t ring_tail; /* New messages are written at the tail */
  atomic_uint_fast64_t ring_head; /* The oldest message starts at the head */
};

/* event header fields (for runtime events):
| -- length (10 bits) -- | runtime or user event (1 bit) | event type (4 bits) | event id (13 bits)
*/

#define RING_ITEM_LENGTH(header) (((header) >> 54) & ((1UL << 10) - 1))
#define RING_ITEM_IS_RUNTIME(header) !((header) | (1UL << 53))
#define RING_ITEM_IS_USER(header) ((header) | (1UL << 53))
#define RING_ITEM_TYPE(header) (((header) >> 49) & ((1UL << 4) - 1))
#define RING_ITEM_ID(header) (((header) >> 36) & ((1UL << 13) - 1))

static char* eventring_path;
static struct ring_buffer_header *ring_header = NULL;
static uint64_t *ring_ptr = NULL;
static char *ring_buffer_loc = NULL;
static size_t ring_total_file_size = RING_BUFFER_SIZE * sizeof(uint64_t) + sizeof(struct ring_buffer_header);

static int64_t time_counter(void)
{
#ifdef _WIN32
  static double clock_freq = 0;
  static LARGE_INTEGER now;

  if (clock_freq == 0)
  {
    LARGE_INTEGER f;
    if (!QueryPerformanceFrequency(&f))
      return 0;
    clock_freq = (1000000000.0 / f.QuadPart);
  };

  if (!QueryPerformanceCounter(&now))
    return 0;
  return (int64_t)(now.QuadPart * clock_freq);

#elif defined(HAS_MACH_ABSOLUTE_TIME)
  static mach_timebase_info_data_t time_base = {0};
  uint64_t now;

  if (time_base.denom == 0)
  {
    if (mach_timebase_info(&time_base) != KERN_SUCCESS)
      return 0;

    if (time_base.denom == 0)
      return 0;
  }

  now = mach_absolute_time();
  return (int64_t)((now * time_base.numer) / time_base.denom);

#elif defined(HAS_POSIX_MONOTONIC_CLOCK)
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (int64_t)t.tv_sec * (int64_t)1000000000 +
         (int64_t)t.tv_nsec;

#endif
}

static void write_to_ring(ev_category category, ev_message_type type, int event_id, int event_length, uint64_t *content, int word_offset);

static void teardown_eventring(void)
{
  // We should only preserve the eventring if the OCAMLRUNPARAM
  // parameter tells us to do so
  munmap(ring_header, ring_total_file_size);

  ring_ptr = NULL;
  ring_header = NULL;
}

void caml_eventring_init()
{
  eventring_path = caml_secure_getenv(T("OCAML_EVENTRING_PATH"));

  if( caml_secure_getenv(T("OCAML_EVENTRING_ENABLED")) ) {
    caml_eventring_start();
  }
}

void caml_eventring_destroy()
{
  if( ring_ptr ) {
    write_to_ring(EV_RUNTIME, EV_LIFECYCLE, EV_STOP, 0, NULL, 0);

    Caml_state->eventlog_enabled = 0;

    teardown_eventring();
  }
}

CAMLprim value caml_eventring_start()
{ 
  if( !ring_ptr ) {
    int ring_fd, ret;

    ring_buffer_loc = caml_stat_alloc(RING_FILE_NAME_LEN);

    Caml_state->eventlog_startup_pid = getpid();

    if( eventring_path ) {
      snprintf_os(ring_buffer_loc, RING_FILE_NAME_LEN, T("%s/%ld.eventring"), eventring_path, Caml_state->eventlog_startup_pid);
    }
    else
    {
      snprintf_os(ring_buffer_loc, RING_FILE_NAME_LEN, T("%ld.eventring"), Caml_state->eventlog_startup_pid);
    }

    ring_total_file_size = RING_BUFFER_SIZE * sizeof(uint64_t) + sizeof(struct ring_buffer_header);

    ring_fd = open(ring_buffer_loc, O_RDWR | O_CREAT, (S_IRUSR | S_IWUSR));
    caml_stat_free(ring_buffer_loc);

    if (ring_fd < 0)
    {
      caml_fatal_error("Couldn't open ring buffer loc: %s", ring_buffer_loc);
    }

    ret = ftruncate(ring_fd, ring_total_file_size);

    if (ret < 0)
    {
      caml_fatal_error("Can't resize ring buffer");
    }

    ring_header = mmap(NULL, ring_total_file_size, PROT_READ | PROT_WRITE, MAP_SHARED, ring_fd, 0);

    ring_ptr = (uint64_t *)(ring_header + 1);

    ring_header->version = 1;
    ring_header->ring_size = RING_BUFFER_SIZE;
    ring_header->ring_head = 0;
    ring_header->ring_tail = 0;

    close(ring_fd);

    Caml_state->eventlog_enabled = 1;
    Caml_state->eventlog_paused = 0;

    write_to_ring(EV_RUNTIME, EV_LIFECYCLE, EV_START, 0, NULL, 0);

    atexit(&teardown_eventring);
  }

  return Val_unit;
}

void caml_eventring_pause()
{
  if( Caml_state->eventlog_enabled && !Caml_state->eventlog_paused ) {
    write_to_ring(EV_RUNTIME, EV_LIFECYCLE, EV_PAUSE, 0, NULL, 0);
    Caml_state->eventlog_paused = 1;
  }
}

void caml_eventring_resume()
{
  if( Caml_state->eventlog_enabled && Caml_state->eventlog_paused ) {
    write_to_ring(EV_RUNTIME, EV_LIFECYCLE, EV_RESUME, 0, NULL, 0);
    Caml_state->eventlog_paused = 0;
  }
}


static void write_to_ring(ev_category category, ev_message_type type, int event_id, int event_length, uint64_t *content, int word_offset)
{
  /* account for header and timestamp */
  uint64_t length_with_header_ts = event_length + 2;
  uint64_t ring_head = atomic_load_explicit(&ring_header->ring_head, memory_order_acquire);
  uint64_t ring_tail = atomic_load_explicit(&ring_header->ring_tail, memory_order_acquire);
  uint64_t ring_tail_offset = ring_tail % ring_header->ring_size;
  uint64_t ring_distance_to_end = ring_header->ring_size - ring_tail_offset;
  uint64_t padding_required = 0;

  /* length must be less than 2^10 */
  CAMLassert(event_length < (1 << 10));
  /* Runtime event with type EV_INTERNAL and id 0 is reserved for padding */
  CAMLassert(!(category == EV_RUNTIME && type == EV_INTERNAL && event_id == 0));

  // Work out if padding is required
  if( ring_distance_to_end < length_with_header_ts ) {
    padding_required = ring_distance_to_end;
  }

  // First we check if a write would take us over the head
  while ((ring_tail + length_with_header_ts + padding_required) - ring_head >= RING_BUFFER_SIZE)
  {
    // The write would over-write some old bit of data. Need to advance the head.
    uint64_t head_header = ring_ptr[ring_head % ring_header->ring_size];

    ring_head += RING_ITEM_LENGTH(head_header);

    atomic_store_explicit(&ring_header->ring_head, ring_head, memory_order_release); // advance the ring head
  }

  if ( padding_required > 0 )
  {
    ring_ptr[ring_tail_offset] = (ring_distance_to_end << 54); // Padding header with size ring_distance_to_end
                                                               // Readers will skip the message and go straight
                                                               // to the beginning of the ring.

    ring_tail += ring_distance_to_end;

    atomic_store_explicit(&ring_header->ring_tail, ring_tail, memory_order_release);

    ring_tail_offset = 0;
  }

  // Write header
  ring_ptr[ring_tail_offset++] = (((uint64_t)length_with_header_ts) << 54) | ((category == EV_RUNTIME) ? 0 : (1ULL << 53)) | ((uint64_t)type) << 49 | ((uint64_t)event_id) << 36;
  ring_ptr[ring_tail_offset++] = time_counter();
  if (content != NULL)
  {
    memcpy(&ring_ptr[ring_tail_offset], content + word_offset, event_length * sizeof(uint64_t));
  }
  atomic_store_explicit(&ring_header->ring_tail, ring_tail + length_with_header_ts, memory_order_release);
}

/* Functions for putting runtime data on to the eventring */

void caml_ev_begin(ev_runtime_phase phase)
{
  if (Caml_state->eventlog_enabled && !Caml_state->eventlog_paused && ring_ptr != NULL)
  {
    write_to_ring(EV_RUNTIME, EV_BEGIN, phase, 0, NULL, 0);
  }
}

void caml_ev_end(ev_runtime_phase phase)
{
  if (Caml_state->eventlog_enabled && !Caml_state->eventlog_paused && ring_ptr != NULL)
  {
    write_to_ring(EV_RUNTIME, EV_EXIT, phase, 0, NULL, 0);
  }
}

void caml_ev_counter(ev_runtime_counter counter, uint64_t val)
{
  if (Caml_state->eventlog_enabled && !Caml_state->eventlog_paused && ring_ptr != NULL)
  {
    uint64_t buf[1];
    buf[0] = val;

    write_to_ring(EV_RUNTIME, EV_COUNTER, counter, 1, buf, 0);
  }
}

#define NUM_BUCKETS 20
static uint64_t alloc_buckets[NUM_BUCKETS] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

/* This function records allocations in caml_alloc_shr_aux in given bucket sizes
   These buckets are meant to be flushed explicitly by the caller through the
   caml_ev_alloc_flush function. Until then the buckets are just updated until
   flushed.
*/
void caml_ev_alloc(uint64_t sz)
{
  if (!Caml_state->eventlog_enabled)
    return;
  if (Caml_state->eventlog_paused)
    return;

  if (sz < (NUM_BUCKETS/2))
  {
    ++alloc_buckets[sz];
  }
  else if (sz < (NUM_BUCKETS*10/2))
  {
    ++alloc_buckets[sz / (NUM_BUCKETS/2) + (NUM_BUCKETS/2-1)];
  }
  else
  {
    ++alloc_buckets[NUM_BUCKETS-1];
  }
}

/*  Note that this function does not trigger an actual disk flush, it just
    pushes events in the event buffer.
*/
void caml_ev_alloc_flush()
{
  int i;

  if (!Caml_state->eventlog_enabled)
    return;
  if (Caml_state->eventlog_paused)
    return;

  write_to_ring(EV_RUNTIME, EV_ALLOC, 0, NUM_BUCKETS, alloc_buckets, 0);

  for (i = 1; i < NUM_BUCKETS; i++)
  {
    alloc_buckets[i] = 0;
  }
}

void caml_ev_flush()
{
  // This is a no-op for eventring
}

CAMLprim value caml_eventlog_resume(value v)
{
  if( Caml_state->eventlog_enabled && Caml_state->eventlog_paused ) {
    write_to_ring(EV_RUNTIME, EV_LIFECYCLE, EV_RESUME, 0, NULL, 0);
    Caml_state->eventlog_paused = 0;
  }
  return Val_unit;
}

CAMLprim value caml_eventlog_pause(value v)
{
  if( Caml_state->eventlog_enabled && !Caml_state->eventlog_paused ) {
    write_to_ring(EV_RUNTIME, EV_LIFECYCLE, EV_PAUSE, 0, NULL, 0);
    Caml_state->eventlog_paused = 1;
  }
  return Val_unit;
}

struct caml_eventring_cursor
{
  int cursor_open;
  uint64_t *ring_ptr;
  struct ring_buffer_header *ring_header;
  uint64_t current_pos;
  size_t ring_total_file_size;
};

/* C-API for reading from an eventring */

/* [eventring_path] is a path to a directory containing eventrings. [pid] is the
    process id (or equivalent) of the startup OCaml process. This function will
    return a cursor which can we be used with caml_eventring_read_poll to read
    events from the eventrings. */
struct caml_eventring_cursor *caml_eventring_create_cursor(char *eventring_path,
                                                      int pid)
{
  int ring_fd, ret;
  struct stat tmp_stat;
  struct caml_eventring_cursor *cursor = caml_stat_alloc(
      sizeof(struct caml_eventring_cursor));
  char *eventring_loc;

  eventring_loc = caml_stat_alloc(RING_FILE_NAME_LEN);

  /* TODO: We should do something more sensible here and avoid duplicating
  with earlier code. */
  if( eventring_path ) {
    ret = snprintf_os(eventring_loc, RING_FILE_NAME_LEN,
                    T("%s/%d.eventring"), eventring_path, pid);
  }
  else
  {
    ret = snprintf_os(eventring_loc, RING_FILE_NAME_LEN,
                    T("%d.eventring"), pid);
  }

  if (ret < 0)
  {
    /* TODO: We should report an error here.
      Also free the cursor and eventring_loc. */
    return 0;
  }

  ring_fd = open(eventring_loc, O_RDONLY, 0);
  ret = fstat(ring_fd, &tmp_stat);

  if (ret < 0)
  {
    /* TODO: Should at least log what happened here.
      Also free the cursor and eventring_loc. */
    return 0;
  }

  cursor->ring_total_file_size = tmp_stat.st_size;
  cursor->ring_header = mmap(NULL, cursor->ring_total_file_size, PROT_READ, MAP_SHARED,
                             ring_fd, 0);
  cursor->ring_ptr = (uint64_t *)(ring_header + 1);
  cursor->current_pos = 0;
  cursor->cursor_open = 1;

  return cursor;
}

/* frees a cursor obtained from caml_eventring_reader_create */
void caml_eventring_free_cursor(struct caml_eventring_cursor *cursor)
{
  if( cursor->cursor_open ) {
    cursor->cursor_open = 0;
    munmap(ring_header, cursor->ring_total_file_size);
    caml_stat_free(cursor);
  }
}

/* polls the eventring pointed to by [cursor] and calls the appropriate callback
    provided in [callbacks] for each new event. Returns the number of events
    consumed. */
int caml_eventring_read_poll(struct caml_eventring_cursor *cursor,
                             struct caml_eventring_callbacks *callbacks,
                             void* callback_data)
{
  int events_consumed = 0;
  uint64_t ring_head, ring_tail;

  if (!cursor->cursor_open)
  {
    /* Should probably log something here as well */
    return 0;
  }

  do
  {
    ring_head = atomic_load_explicit(&ring_header->ring_head, memory_order_acquire);
    ring_tail = atomic_load_explicit(&ring_header->ring_tail, memory_order_acquire);

    if (ring_head > cursor->current_pos)
    {
      if( callbacks->ev_lost_events )
      {
        callbacks->ev_lost_events(callback_data, ring_head - cursor->current_pos);
      }
      cursor->current_pos = ring_head;
    }

    while (cursor->current_pos < ring_tail)
    {
      uint64_t buf[1024];
      uint64_t ring_size = ring_header->ring_size;
      uint64_t header = ring_ptr[cursor->current_pos % ring_size];

      uint64_t msg_length = RING_ITEM_LENGTH(header);

      if (msg_length > (1 << 10))
      {
        // TODO: fatal error here, the stream is corrupt or our position is
        // wrong. Free buf
      }

      memcpy(buf, ring_ptr + (cursor->current_pos % ring_size), msg_length * sizeof(uint64_t));

      ring_head = atomic_load_explicit(&ring_header->ring_head, memory_order_acquire);

      /* Check the message we've read hasn't been overwritten by the writer */
      if (ring_head > cursor->current_pos)
      {
        /* It potentially has, retry for the next one after we've notified
             the callbacks about lost messages. */
        if( callbacks->ev_lost_events )
        {
          callbacks->ev_lost_events(callback_data, ring_head - cursor->current_pos);
        }
        cursor->current_pos = ring_head;
        break;
      }

      switch (RING_ITEM_TYPE(header))
      {
      case EV_BEGIN:
        if (callbacks->ev_runtime_begin)
        {
          callbacks->ev_runtime_begin(callback_data, buf[1], RING_ITEM_ID(header));
        }
        break;
      case EV_EXIT:
        if (callbacks->ev_runtime_end)
        {
          callbacks->ev_runtime_end(callback_data, buf[1], RING_ITEM_ID(header));
        }
        break;
      case EV_COUNTER:
        if (callbacks->ev_runtime_counter)
        {
          callbacks->ev_runtime_counter(callback_data, buf[1], buf[2], RING_ITEM_ID(header));
        }
        break;
      case EV_ALLOC:
        if (callbacks->ev_alloc)
        {
          callbacks->ev_alloc(callback_data, buf[1], &buf[2]);
        }
        break;
      case EV_LIFECYCLE:
        if (callbacks->ev_lifecycle)
        {
          callbacks->ev_lifecycle(callback_data, buf[1], RING_ITEM_ID(header));
        }
      }

      if (RING_ITEM_TYPE(header) != EV_INTERNAL)
      {
        events_consumed++;
      }

      cursor->current_pos += msg_length;
    }

  }
  while( ring_tail < atomic_load_explicit(&ring_header->ring_tail, memory_order_acquire) );


  return events_consumed;
}

static void finalise_cursor(value v) {

}

static struct custom_operations cursor_operations = {
  "eventring.cursor",
  finalise_cursor,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default,
  custom_compare_ext_default,
  custom_fixed_length_default
};

#define Cursor_val(v) (*((struct caml_eventring_cursor**)Data_custom_val(v)))

CAMLprim value caml_eventring_create_wrapped_cursor(value eventring_path, value pid) {
  CAMLparam0();
  CAMLlocal1(wrapper);
  
  wrapper = caml_alloc_custom(&cursor_operations, sizeof(struct caml_eventring_cursor
*), 0, 1);

  struct caml_eventring_cursor* cursor = caml_eventring_create_cursor(String_val(eventring_path), Int_val(pid));

  if( cursor == NULL ) {
    // TODO: Raise an actual exception here
    caml_failwith("Could not obtain cursor");
  }

  Cursor_val(wrapper) = cursor;

  return wrapper;
}

CAMLprim value caml_eventring_free_wrapped_cursor(value wrapped_cursor) {
  CAMLparam1(wrapped_cursor);

  struct caml_eventring_cursor* cursor = Cursor_val(wrapped_cursor);

  if( cursor != NULL ) {
    caml_eventring_free_cursor(cursor);
    Cursor_val(wrapped_cursor) = NULL;
  }

  return Val_unit;
};

CAMLprim value caml_eventring_read_poll_wrapped(value wrapped_cursor, value callbacks) {
  return Val_unit;
};