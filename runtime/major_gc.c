/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*              Damien Doligez, projet Para, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#define CAML_INTERNALS

#include <limits.h>
#include <math.h>

#include "caml/addrmap.h"
#include "caml/compact.h"
#include "caml/custom.h"
#include "caml/config.h"
#include "caml/fail.h"
#include "caml/finalise.h"
#include "caml/freelist.h"
#include "caml/gc.h"
#include "caml/gc_ctrl.h"
#include "caml/major_gc.h"
#include "caml/misc.h"
#include "caml/mlvalues.h"
#include "caml/roots.h"
#include "caml/signals.h"
#include "caml/weak.h"
#include "caml/memprof.h"
#include "caml/eventlog.h"

#if defined (NATIVE_CODE) && defined (NO_NAKED_POINTERS)
#define NATIVE_CODE_AND_NO_NAKED_POINTERS
#else
#undef NATIVE_CODE_AND_NO_NAKED_POINTERS
#endif

#ifdef _MSC_VER
Caml_inline double fmin(double a, double b) {
  return (a < b) ? a : b;
}
#endif

#define MARK_STACK_INIT_SIZE 2048

typedef struct {
  value block;
  uintnat offset;
} mark_entry;

struct mark_stack {
  mark_entry* stack;
  uintnat count;
  uintnat size;
};

uintnat caml_percent_free;
uintnat caml_major_heap_increment;
CAMLexport char *caml_heap_start;
char *caml_gc_sweep_hp;
int caml_gc_phase;        /* always Phase_mark, Pase_clean,
                             Phase_sweep, or Phase_idle */
uintnat caml_allocated_words;
uintnat caml_dependent_size, caml_dependent_allocated;
double caml_extra_heap_resources;
uintnat caml_fl_wsz_at_phase_change = 0;

extern char *caml_fl_merge;  /* Defined in freelist.c. */

static char *sweep_chunk, *sweep_limit;
static char* rescan_chunk = NULL; /* chunk being rescanned, if NULL no rescanning required */
static double p_backlog = 0.0; /* backlog for the gc speedup parameter */

int caml_gc_subphase;     /* Subphase_{mark_roots,mark_main,mark_final} */

/**
   Ephemerons:
   During mark phase the list caml_ephe_list_head of ephemerons
   is iterated by different pointers that follow the invariants:
   caml_ephe_list_head ->* ephes_checked_if_pure ->* ephes_to_check ->* null
                        |                         |                  |
                       (1)                       (2)                (3)

    At the start of mark phase, (1) and (2) are empty.

    In mark phase:
      - the ephemerons in (1) have a data alive or none
        (nb: new ephemerons are added in this part by weak.c)
      - the ephemerons in (2) have at least a white key or are white
        if ephe_list_pure is true, otherwise they are in an unknown state and
        must be checked again.
      - the ephemerons in (3) are in an unknown state and must be checked

    At the end of mark phase, (3) is empty and ephe_list_pure is true.
    The ephemeron in (1) and (2) will be cleaned (white keys and data
    replaced by none or the ephemeron is removed from the list if it is white)
    in clean phase.

    In clean phase:
    caml_ephe_list_head ->*                           ephes_to_check ->* null
                         |                                            |
                        (1)                                          (3)

    In clean phase, (2) is not used, ephes_to_check is initialized at
    caml_ephe_list_head:
    - the ephemerons in (1) are clean.
    - the ephemerons in (3) should be cleaned or removed if white.

 */
static int ephe_list_pure;
/** The ephemerons is pure if since the start of its iteration
    no value have been darkened. */
static value *ephes_checked_if_pure;
static value *ephes_to_check;

int caml_major_window = 1;
double caml_major_ring[Max_major_window] = { 0. };
int caml_major_ring_index = 0;
double caml_major_work_credit = 0.0;
double caml_gc_clock = 0.0;

#ifdef DEBUG
static unsigned long major_gc_counter = 0;
#endif

void (*caml_major_gc_hook)(void) = NULL;

#define HEAP_RANGE_SIZE_BITS 20
#define HEAP_RANGE_SIZE (1 << HEAP_RANGE_SIZE_BITS)

struct heap_range {
  value heap_range;
  int occurs;
};

static int heap_range_count_cmp(const void* a, const void* b)
{
  const struct heap_range* p = a;
  const struct heap_range* q = b;
  return p->occurs - q->occurs;
}

static int heap_range_addr_cmp(const void* a, const void* b)
{
  const struct heap_range* p = a;
  const struct heap_range* q = b;

  if( p->heap_range > q->heap_range ) {
    return 1;
  } else if ( p->heap_range < q->heap_range ) {
    return -1;
  } else {
    return 0;
  }
}

static value range_of_block(value block) {
  CAMLassert(Is_block(block) && !Is_young(block));

  return (value)Hp_bp(block) & ~(HEAP_RANGE_SIZE -1);
}

static void mark_stack_prune (struct mark_stack* stk)
{
  struct addrmap t = ADDRMAP_INIT;
  int count = 0, entry, chunks_postponed = 0;
  addrmap_iterator i;
  uintnat mark_stack_count = stk->count;
  mark_entry* mark_stack = stk->stack;
  /* space used by the computations below */
  uintnat table_max = mark_stack_count / 100;
  /* amount of space we want to free up */
  int entries_to_free = (uintnat)(mark_stack_count * 0.50);
  
  char* heap_chunk = caml_heap_start;
  struct heap_range* heap_ranges;
  int pos = 0, start, total = 0, out = 0;


  if (table_max < 1000) table_max = 1000;

  /* We compress the mark stack by removing all of the objects from a
     subset of chunks, which are rescanned later. For efficiency, we
     want to select those chunks which occur most frequently, so that
     we need to rescan as few chunks as possible. However, we do not
     have space to build a complete histogram.

     Using ~1% of the mark stack's space, we can find all of the
     elements that occur at least 100 times using the Misra-Gries
     heavy hitter algorithm (see J. Misra and D. Gries, "Finding
     repeated elements", 1982). */

  for (entry = 0; entry < mark_stack_count; entry++) {
    value p = range_of_block(mark_stack[entry].block);
    if (caml_addrmap_contains(&t, p)) {
      /* if it's already present, increase the count */
      (*caml_addrmap_insert_pos(&t, p)) ++;
    } else if (count < table_max) {
      /* if there's space, insert it with count 1 */
      *caml_addrmap_insert_pos(&t, p) = 1;
      count++;
    } else {
      /* otherwise, decrease all entries by 1 */
      struct addrmap s = ADDRMAP_INIT;
      int scount = 0;
      for (i = caml_addrmap_iterator(&t);
           caml_addrmap_iter_ok(&t, i);
           i = caml_addrmap_next(&t, i)) {
        value k = caml_addrmap_iter_key(&t, i);
        value v = caml_addrmap_iter_value(&t, i);
        if (v > 1) {
          *caml_addrmap_insert_pos(&s, k) = v - 1;
          scount++;
        }
      }
      caml_addrmap_clear(&t);
      t = s;
      count = scount;
    }
  }

  /* t now contains all heap ranges that occur at least 100 times.
     If no heap ranges occur at least 100 times, t is some arbitrary subset of heap ranges.
     Next, we get an accurate count of the occurrences of the heap ranges in t */

  for (i = caml_addrmap_iterator(&t);
       caml_addrmap_iter_ok(&t, i);
       i = caml_addrmap_next(&t, i)) {
    *caml_addrmap_iter_val_pos(&t, i) = 0;
  }
  for (entry = 0; entry < mark_stack_count; entry++) {
    value p = range_of_block(mark_stack[entry].block);
    if (caml_addrmap_contains(&t, p))
      (*caml_addrmap_insert_pos(&t, p))++;
  }

  /* Next, find a subset of those heap ranges that cover enough entries */

  heap_ranges = caml_stat_alloc(count * sizeof(struct heap_range));

  for (i = caml_addrmap_iterator(&t);
       caml_addrmap_iter_ok(&t, i);
       i = caml_addrmap_next(&t, i)) {
    struct heap_range* p = &heap_ranges[pos++];
    p->heap_range = caml_addrmap_iter_key(&t, i);
    p->occurs = (int)caml_addrmap_iter_value(&t, i);
  }
  CAMLassert(pos == count);
  caml_addrmap_clear(&t);

  qsort(heap_ranges, count, sizeof(struct heap_range), &heap_range_count_cmp);

  start = count;

  while (start > 0 && total < entries_to_free) {
    start--;
    total += heap_ranges[start].occurs;
  }

  for (i = start; i < count; i++) {
    *caml_addrmap_insert_pos(&t, (value)heap_ranges[i].heap_range) = 1;
  }

  qsort(heap_ranges + start, (count - start), sizeof(struct heap_range), &heap_range_addr_cmp);

  i = start;

  do {
    asize_t size = Chunk_size(heap_chunk);
    char* chunk_start = heap_chunk;
    char* chunk_end = heap_chunk + size;
    char* heap_range_addr = (char*)heap_ranges[i].heap_range;

    /* Walk the heap ranges and chunks in tandem, exploting that they are both sorted */
    if( heap_range_addr < chunk_end ) { /* heap ranges could overlap with chunk */
      if( heap_range_addr+HEAP_RANGE_SIZE >= chunk_start ) { /* heap ranges definitely overlaps with chunk */
        Chunk_requires_rescan(heap_chunk) = 1;
        Chunk_rescan_offset(heap_chunk) = 0;
        chunks_postponed++;
        
        /* check if we need to reset the current rescan_chunk */
        if( rescan_chunk == NULL || heap_chunk < rescan_chunk ) {
          rescan_chunk = heap_chunk;
        }

        if( heap_range_addr+HEAP_RANGE_SIZE <= chunk_end ) { /* heap ranges is fully contained in this chunk, no need */
          i++;                                  /* to check against the next chunk*/
          continue;
        }
      } else { /* heap ranges ends before the start of this chunk, move on to next heap ranges */
        i++;
        continue;
      }
    }

    heap_chunk = Chunk_next(heap_chunk);
  }
  while( i < count && heap_chunk != NULL );
  CAMLassert(i >= count-1); /* i could be count-1 in the case where the last heap ranges extends beyond
                               the end of the last chunk */ 

  for (entry = 0; entry < mark_stack_count; entry++) {
    mark_entry me = mark_stack[entry];
    value p = range_of_block(me.block);
    if (!caml_addrmap_contains(&t, p)) {
      mark_stack[out++] = me;
    }
  }
  stk->count = out;

  caml_stat_free(heap_ranges);

  caml_gc_message(0x08, "Mark stack overflow. Postponing %d chunks (%.1f%%, leaving %d).\n",
              chunks_postponed, 100. * (double)total / (double)mark_stack_count,
              (int)stk->count);
}

static void realloc_mark_stack (struct mark_stack* stk)
{
  mark_entry* new;
  uintnat mark_stack_bsize = stk->size * sizeof(mark_entry);

  if ( mark_stack_bsize < Caml_state->stat_heap_wsz / 32 ) {
    caml_gc_message (0x08, "Growing mark stack to %"
                           ARCH_INTNAT_PRINTF_FORMAT "uk bytes\n",
                     (intnat) mark_stack_bsize * 2 / 1024);

    new = (mark_entry*) caml_stat_resize_noexc ((char*) stk->stack,
                                                2 * mark_stack_bsize);
    if (new != NULL) {
      stk->stack = new;
      stk->size *= 2;
      return;
    }
  } 
  
  caml_gc_message (0x08, "No room for growing mark stack. Pruning..\n");
  mark_stack_prune(stk);
}

Caml_inline void mark_stack_push(struct mark_stack* stk, mark_entry me, intnat* work)
{
  value v;
  int i, block_end = Wosize_val(me.block), end;

  CAMLassert (Is_in_heap (me.block) || Is_black_hd (Hd_val(me.block)));

  CAMLassert(Is_black_val(me.block));
  CAMLassert(Is_block(me.block));
  CAMLassert(Tag_val(me.block) != Infix_tag);
  CAMLassert(Tag_val(me.block) < No_scan_tag);

#ifdef NO_NAKED_POINTERS
  if (Tag_val(me.block) == Closure_tag) {
    /* Skip the code pointers and integers at beginning of closure;
        start scanning at the first word of the environment part. */
    me.offset = Start_env_closinfo(Closinfo_val(me.block));
    CAMLassert(me.offset <= Wosize_val(me.block));
  }
#endif

  end = (block_end < 8 ? block_end : 8);

  /* Optimisation to avoid pushing small, unmarkable objects such as [Some 42]
   * into the mark stack. */
  for (i = me.offset; i < end; i++) {
    v = Field(me.block, i);

    if (Is_block(v) && !Is_black_val(v))
      /* found something to mark */
      break;
  }

  if (i == block_end) {
    /* nothing left to mark */
    if( work != NULL ) {
      /* we should take credit for it though */
      *work -= Whsize_wosize(block_end);
    }
    return;
  } 

  if( work != NULL ) {
    *work -= i;
  }

  me.offset = i;

  if (stk->count == stk->size)
    realloc_mark_stack(stk);

  stk->stack[stk->count++] = me;
}


void caml_darken (value v, value *p /* not used */)
{
#ifdef NATIVE_CODE_AND_NO_NAKED_POINTERS
  if (Is_block (v) && !Is_young (v)) {
#else
  if (Is_block (v) && Is_in_heap (v)) {
#endif
    header_t h = Hd_val (v);
    tag_t t = Tag_hd (h);
    if (t == Infix_tag){
      v -= Infix_offset_val(v);
      h = Hd_val (v);
      t = Tag_hd (h);
    }
#ifdef NATIVE_CODE_AND_NO_NAKED_POINTERS
    /* We insist that naked pointers to outside the heap point to things that
       look like values with headers coloured black.  This isn't always
       strictly necessary but is essential in certain cases---in particular
       when the value is allocated in a read-only section.  (For the values
       where it would be safe it is a performance improvement since we avoid
       putting them on the grey list.) */
    CAMLassert (Is_in_heap (v) || Is_black_hd (h));
#endif
    CAMLassert (!Is_blue_hd (h));
    if (Is_white_hd (h)){
      ephe_list_pure = 0;
      Hd_val (v) = Blackhd_hd (h);
      if (t < No_scan_tag){
        mark_entry me = {v, 0};
        mark_stack_push(Caml_state->mark_stack, me, NULL);
      }
    }
  }
}

/* This function adds blocks in the passed chunk to the mark stack. It may
   return 0 if doing so would cause the mark stack to grow more than half
   full. This is to lower the chance of triggering another overflow, which
   would be wasteful. Subsequent calls will continue progress from the last
   offset that was pushed on to the mark stack. */
static int redarken_chunk(char* heap_chunk, struct mark_stack* stk) {
  value* chunk_start = (value*)((char*)heap_chunk);
  value* p = chunk_start + Chunk_rescan_offset(heap_chunk);

  value* end = (value*)((char*)heap_chunk + Chunk_size(heap_chunk));

  while (p < end) {
    header_t hd = Hd_hp(p);

    if( Is_black_hd(hd) && Tag_hd(hd) < No_scan_tag ) {
      if( stk->count < stk->size/2 ) {
        mark_entry me = { Val_hp(p), 0 };
        mark_stack_push(stk, me, NULL);
      } else {
        /* Don't add to the mark stack as this would cause it to overflow again */
        Chunk_rescan_offset(heap_chunk) = p - chunk_start;
        return 0;
      }
    }

    p += Whsize_hp(p);
  }
  
  CAMLassert(p == end);

  Chunk_requires_rescan(heap_chunk) = 0;
  Chunk_rescan_offset(heap_chunk) = 0;
  return 1;
}

static void start_cycle (void)
{
  CAMLassert (caml_gc_phase == Phase_idle);
  CAMLassert (Caml_state->mark_stack->count == 0);
  CAMLassert (rescan_chunk == NULL);
  caml_gc_message (0x08, "starting new major GC cycle\n");
  caml_darken_all_roots_start ();
  caml_gc_phase = Phase_mark;
  caml_gc_subphase = Subphase_mark_roots;
  ephe_list_pure = 1;
  ephes_checked_if_pure = &caml_ephe_list_head;
  ephes_to_check = &caml_ephe_list_head;
#ifdef DEBUG
  ++ major_gc_counter;
  caml_heap_check ();
#endif
}

static void init_sweep_phase(void)
{
  /* Phase_clean is done. */
  /* Initialise the sweep phase. */
  caml_gc_sweep_hp = caml_heap_start;
  caml_fl_init_merge ();
  caml_gc_phase = Phase_sweep;
  sweep_chunk = caml_heap_start;
  caml_gc_sweep_hp = sweep_chunk;
  sweep_limit = sweep_chunk + Chunk_size (sweep_chunk);
  caml_fl_wsz_at_phase_change = caml_fl_cur_wsz;
  if (caml_major_gc_hook) (*caml_major_gc_hook)();
}

/* auxiliary function of mark_slice */
static inline void mark_slice_darken(struct mark_stack* stk, value v, mlsize_t i,
                                       int in_ephemeron, int *slice_pointers, intnat *work)
{
  value child;
  header_t chd;

  child = Field (v, i);

#ifdef NATIVE_CODE_AND_NO_NAKED_POINTERS
  if (Is_block (child) && ! Is_young (child) && Wosize_val (child) > 0) {
#else
  if (Is_block (child) && Is_in_heap (child)) {
#endif
    CAML_EVENTLOG_DO (++ *slice_pointers);
    chd = Hd_val (child);
    if (Tag_hd (chd) == Forward_tag){
      value f = Forward_val (child);
      if ((in_ephemeron && Is_long(f)) ||
          (Is_block (f)
           && (!Is_in_value_area(f) || Tag_val (f) == Forward_tag
               || Tag_val (f) == Lazy_tag
#ifdef FLAT_FLOAT_ARRAY
               || Tag_val (f) == Double_tag
#endif
               ))){
        /* Do not short-circuit the pointer. */
      }else{
        /* The variable child is not changed because it must be mark alive */
        Field (v, i) = f;
        if (Is_block (f) && Is_young (f) && !Is_young (child)){
          if(in_ephemeron) {
            add_to_ephe_ref_table (Caml_state->ephe_ref_table, v, i);
          } else {
            add_to_ref_table (Caml_state->ref_table, &Field (v, i));
          }
        }
      }
    }
    else if (Tag_hd(chd) == Infix_tag) {
      child -= Infix_offset_val(child);
      chd = Hd_val(child);
    }
#ifdef NATIVE_CODE_AND_NO_NAKED_POINTERS
    /* See [caml_darken] for a description of this assertion. */
    CAMLassert (Is_in_heap (child) || Is_black_hd (chd));
#endif
    if (Is_white_hd (chd)){
      ephe_list_pure = 0;
      Hd_val (child) = Blackhd_hd (chd);
      if( Tag_hd(chd) < No_scan_tag ) {
        mark_entry me = {child, 0};
        mark_stack_push(stk, me, work);
      } 
      else {
        *work -= 1; /* Account for header */
      }
    }
  }
}

static void mark_ephe_aux (struct mark_stack *stk, intnat *work,
                             int *slice_pointers)
{
  value v, data, key;
  header_t hd;
  mlsize_t size, i;

  v = *ephes_to_check;
  hd = Hd_val(v);
  CAMLassert(Tag_val (v) == Abstract_tag);
  data = Field(v,CAML_EPHE_DATA_OFFSET);
  if ( data != caml_ephe_none &&
       Is_block (data) && Is_in_heap (data) && Is_white_val (data)){

    int alive_data = 1;

    /* The liveness of the ephemeron is one of the condition */
    if (Is_white_hd (hd)) {
      alive_data = 0;
    }

    /* The liveness of the keys not caml_ephe_none is the other condition */
    size = Wosize_hd (hd);
    for (i = CAML_EPHE_FIRST_KEY; alive_data && i < size; i++){
      key = Field (v, i);
    ephemeron_again:
      if (key != caml_ephe_none &&
          Is_block (key) && Is_in_heap (key)){
        if (Tag_val (key) == Forward_tag){
          value f = Forward_val (key);
          if (Is_long (f) ||
              (Is_block (f) &&
               (!Is_in_value_area(f) || Tag_val (f) == Forward_tag
                || Tag_val (f) == Lazy_tag
#ifdef FLAT_FLOAT_ARRAY
                || Tag_val (f) == Double_tag
#endif
                ))){
            /* Do not short-circuit the pointer. */
          }else{
            Field (v, i) = key = f;
            goto ephemeron_again;
          }
        }
        if (Is_white_val (key)){
          alive_data = 0;
        }
      }
    }
    *work -= Whsize_wosize(i);

    if (alive_data){
      mark_slice_darken(stk, v,
                                        CAML_EPHE_DATA_OFFSET,
                                        /*in_ephemeron=*/1,
                                        slice_pointers, work);
    } else { /* not triggered move to the next one */
      ephes_to_check = &Field(v,CAML_EPHE_LINK_OFFSET);
      return;
    }
  } else {  /* a simily weak pointer or an already alive data */
    *work -= 1;
  }

  /* all keys black or data none or black
     move the ephemerons from (3) to the end of (1) */
  if ( ephes_checked_if_pure == ephes_to_check ) {
    /* corner case and optim */
    ephes_checked_if_pure = &Field(v,CAML_EPHE_LINK_OFFSET);
    ephes_to_check = ephes_checked_if_pure;
  } else {
    /*  - remove v from the list (3) */
    *ephes_to_check = Field(v,CAML_EPHE_LINK_OFFSET);
    /*  - insert it at the end of (1) */
    Field(v,CAML_EPHE_LINK_OFFSET) = *ephes_checked_if_pure;
    *ephes_checked_if_pure = v;
    ephes_checked_if_pure = &Field(v,CAML_EPHE_LINK_OFFSET);
  }
}



static void mark_slice (intnat work)
{
  mark_entry me = {0};
  mlsize_t me_end = 0;
#ifdef CAML_INSTR
  int slice_fields = 0; /** eventlog counters */
#endif /*CAML_INSTR*/
  int slice_pointers = 0;
  struct mark_stack* stk = Caml_state->mark_stack;
  
  caml_gc_message (0x40, "Marking %"ARCH_INTNAT_PRINTF_FORMAT"d words\n", work);
  caml_gc_message (0x40, "Subphase = %d\n", caml_gc_subphase);

  while (1){
    int can_mark = 0;

    if (me.offset == me_end) {
      if (stk->count > 0)
      {
        me = stk->stack[--stk->count];
        me_end = Wosize_val(me.block);
        can_mark = 1;
      }
    }
    else
    {
      can_mark = 1;
    }

    if (work <= 0) {
      if( can_mark ) {
        mark_stack_push(stk, me, NULL);
      }
      break;
    }

    if( can_mark ) {
      CAMLassert(Is_block(me.block) &&
                Is_black_val (me.block) &&
                Tag_val(me.block) < No_scan_tag);

      mark_slice_darken(stk, me.block, me.offset++, /*in_ephemeron=*/ 0,
                                              &slice_pointers, &work);

      work--;

      if( me.offset == me_end ) {
        work--; /* Include header word */
      }
    } else if( rescan_chunk != NULL ) {
      /* There are chunks that need to be rescanned because we overflowed our mark stack */
      if( redarken_chunk(rescan_chunk, stk) ) {
        do {
          rescan_chunk = Chunk_next(rescan_chunk);
        } while( rescan_chunk != NULL && !Chunk_requires_rescan(rescan_chunk) );
      }
    } else if (caml_gc_subphase == Subphase_mark_roots) {
      work = caml_darken_all_roots_slice (work);
      if (work > 0){
        caml_gc_subphase = Subphase_mark_main;
      }
    } else if (*ephes_to_check != (value) NULL) {
      /* Continue to scan the list of ephe */
      mark_ephe_aux(stk,&work,&slice_pointers);
    } else if (!ephe_list_pure){
      /* We must scan again the list because some value have been darken */
      ephe_list_pure = 1;
      ephes_to_check = ephes_checked_if_pure;
    }else{
      switch (caml_gc_subphase){
      case Subphase_mark_main: {
          /* Subphase_mark_main is done.
             Mark finalised values. */
          caml_final_update_mark_phase ();
          /* Complete the marking */
          ephes_to_check = ephes_checked_if_pure;
          CAML_EV_END(EV_MAJOR_MARK_MAIN);
          caml_gc_subphase = Subphase_mark_final;
      }
        break;
      case Subphase_mark_final: {
        /** The set of unreachable value will not change anymore for
            this cycle. Start clean phase. */
        CAML_EV_BEGIN(EV_MAJOR_MARK_FINAL);
        caml_gc_phase = Phase_clean;
        caml_final_update_clean_phase ();
        caml_memprof_update_clean_phase ();
        if (caml_ephe_list_head != (value) NULL){
          /* Initialise the clean phase. */
          ephes_to_check = &caml_ephe_list_head;
        } else {
          /* Initialise the sweep phase. */
          init_sweep_phase();
        }
        work = 0;
        CAML_EV_END(EV_MAJOR_MARK_FINAL);
      }
        break;
      default: CAMLassert (0);
      }
    }
  }
  CAML_EV_COUNTER(EV_C_MAJOR_MARK_SLICE_FIELDS, slice_fields);
  CAML_EV_COUNTER(EV_C_MAJOR_MARK_SLICE_POINTERS, slice_pointers);
}

/* Clean ephemerons */
static void clean_slice (intnat work)
{
  value v;

  caml_gc_message (0x40, "Cleaning %"
                   ARCH_INTNAT_PRINTF_FORMAT "d words\n", work);
  while (work > 0){
    v = *ephes_to_check;
    if (v != (value) NULL){
      if (Is_white_val (v)){
        /* The whole array is dead, remove it from the list. */
        *ephes_to_check = Field (v, CAML_EPHE_LINK_OFFSET);
        work -= 1;
      }else{
        caml_ephe_clean(v);
        ephes_to_check = &Field (v, CAML_EPHE_LINK_OFFSET);
        work -= Whsize_val (v);
      }
    }else{ /* End of list reached */
      /* Phase_clean is done. */
      /* Initialise the sweep phase. */
      init_sweep_phase();
      work = 0;
    }
  }
}

static void sweep_slice (intnat work)
{
  char *hp;
  header_t hd;

  caml_gc_message (0x40, "Sweeping %"
                   ARCH_INTNAT_PRINTF_FORMAT "d words\n", work);
  while (work > 0){
    if (caml_gc_sweep_hp < sweep_limit){
      hp = caml_gc_sweep_hp;
      hd = Hd_hp (hp);
      work -= Whsize_hd (hd);
      caml_gc_sweep_hp += Bhsize_hd (hd);
      switch (Color_hd (hd)){
      case Caml_white:
        caml_gc_sweep_hp = (char *) caml_fl_merge_block (Val_hp (hp), sweep_limit);
        break;
      case Caml_blue:
        /* Only the blocks of the free-list are blue.  See [freelist.c]. */
        caml_fl_merge = Bp_hp (hp);
        break;
      default:          /* gray or black */
        CAMLassert (Color_hd (hd) == Caml_black);
        Hd_hp (hp) = Whitehd_hd (hd);
        break;
      }
      CAMLassert (caml_gc_sweep_hp <= sweep_limit);
    }else{
      sweep_chunk = Chunk_next (sweep_chunk);
      if (sweep_chunk == NULL){
        /* Sweeping is done. */
        ++ Caml_state->stat_major_collections;
        work = 0;
        caml_gc_phase = Phase_idle;
        caml_request_minor_gc ();
      }else{
        caml_gc_sweep_hp = sweep_chunk;
        sweep_limit = sweep_chunk + Chunk_size (sweep_chunk);
      }
    }
  }
}

/* The main entry point for the major GC. Called about once for each
   minor GC. [howmuch] is the amount of work to do:
   -1 if the GC is triggered automatically
   0 to let the GC compute the amount of work
   [n] to make the GC do enough work to (on average) free [n] words
 */
void caml_major_collection_slice (intnat howmuch)
{
  double p, dp, filt_p, spend;
  intnat computed_work;
  int i;
  /*
     Free memory at the start of the GC cycle (garbage + free list) (assumed):
                 FM = Caml_state->stat_heap_wsz * caml_percent_free
                      / (100 + caml_percent_free)

     Assuming steady state and enforcing a constant allocation rate, then
     FM is divided in 2/3 for garbage and 1/3 for free list.
                 G = 2 * FM / 3
     G is also the amount of memory that will be used during this cycle
     (still assuming steady state).

     Proportion of G consumed since the previous slice:
                 PH = caml_allocated_words / G
                    = caml_allocated_words * 3 * (100 + caml_percent_free)
                      / (2 * Caml_state->stat_heap_wsz * caml_percent_free)
     Proportion of extra-heap resources consumed since the previous slice:
                 PE = caml_extra_heap_resources
     Proportion of total work to do in this slice:
                 P  = max (PH, PE)

     Here, we insert a time-based filter on the P variable to avoid large
     latency spikes in the GC, so the P below is a smoothed-out version of
     the P above.

     Amount of marking work for the GC cycle:
             MW = Caml_state->stat_heap_wsz * 100 / (100 + caml_percent_free)
                  + caml_incremental_roots_count
     Amount of sweeping work for the GC cycle:
             SW = Caml_state->stat_heap_wsz

     In order to finish marking with a non-empty free list, we will
     use 40% of the time for marking, and 60% for sweeping.

     Let MT be the time spent marking, ST the time spent sweeping, and TT
     the total time for this cycle. We have:
                 MT = 40/100 * TT
                 ST = 60/100 * TT

     Amount of time to spend on this slice:
                 T  = P * TT = P * MT / (40/100) = P * ST / (60/100)

     Since we must do MW work in MT time or SW work in ST time, the amount
     of work for this slice is:
                 MS = P * MW / (40/100)  if marking
                 SS = P * SW / (60/100)  if sweeping

     Amount of marking work for a marking slice:
                 MS = P * MW / (40/100)
                 MS = P * (Caml_state->stat_heap_wsz * 250
                           / (100 + caml_percent_free)
                           + 2.5 * caml_incremental_roots_count)
     Amount of sweeping work for a sweeping slice:
                 SS = P * SW / (60/100)
                 SS = P * Caml_state->stat_heap_wsz * 5 / 3

     This slice will either mark MS words or sweep SS words.
  */

  if (caml_major_slice_begin_hook != NULL) (*caml_major_slice_begin_hook) ();

  p = (double) caml_allocated_words * 3.0 * (100 + caml_percent_free)
      / Caml_state->stat_heap_wsz / caml_percent_free / 2.0;
  if (caml_dependent_size > 0){
    dp = (double) caml_dependent_allocated * (100 + caml_percent_free)
         / caml_dependent_size / caml_percent_free;
  }else{
    dp = 0.0;
  }
  if (p < dp) p = dp;
  if (p < caml_extra_heap_resources) p = caml_extra_heap_resources;
  p += p_backlog;
  p_backlog = 0.0;
  if (p > 0.3){
    p_backlog = p - 0.3;
    p = 0.3;
  }

  CAML_EV_COUNTER (EV_C_MAJOR_WORK_EXTRA,
                  (uintnat) (caml_extra_heap_resources * 1000000));

  caml_gc_message (0x40, "ordered work = %"
                   ARCH_INTNAT_PRINTF_FORMAT "d words\n", howmuch);
  caml_gc_message (0x40, "allocated_words = %"
                         ARCH_INTNAT_PRINTF_FORMAT "u\n",
                   caml_allocated_words);
  caml_gc_message (0x40, "extra_heap_resources = %"
                         ARCH_INTNAT_PRINTF_FORMAT "uu\n",
                   (uintnat) (caml_extra_heap_resources * 1000000));
  caml_gc_message (0x40, "raw work-to-do = %"
                         ARCH_INTNAT_PRINTF_FORMAT "du\n",
                   (intnat) (p * 1000000));
  caml_gc_message (0x40, "work backlog = %"
                         ARCH_INTNAT_PRINTF_FORMAT "du\n",
                   (intnat) (p_backlog * 1000000));

  for (i = 0; i < caml_major_window; i++){
    caml_major_ring[i] += p / caml_major_window;
  }

  if (caml_gc_clock >= 1.0){
    caml_gc_clock -= 1.0;
    ++caml_major_ring_index;
    if (caml_major_ring_index >= caml_major_window){
      caml_major_ring_index = 0;
    }
  }
  if (howmuch == -1){
    /* auto-triggered GC slice: spend work credit on the current bucket,
       then do the remaining work, if any */
    /* Note that the minor GC guarantees that the major slice is called in
       automatic mode (with [howmuch] = -1) at least once per clock tick.
       This means we never leave a non-empty bucket behind. */
    spend = fmin (caml_major_work_credit,
                  caml_major_ring[caml_major_ring_index]);
    caml_major_work_credit -= spend;
    filt_p = caml_major_ring[caml_major_ring_index] - spend;
    caml_major_ring[caml_major_ring_index] = 0.0;
  }else{
    /* forced GC slice: do work and add it to the credit */
    if (howmuch == 0){
      /* automatic setting: size of next bucket
         we do not use the current bucket, as it may be empty */
      int i = caml_major_ring_index + 1;
      if (i >= caml_major_window) i = 0;
      filt_p = caml_major_ring[i];
    }else{
      /* manual setting */
      filt_p = (double) howmuch * 3.0 * (100 + caml_percent_free)
               / Caml_state->stat_heap_wsz / caml_percent_free / 2.0;
    }
    caml_major_work_credit += filt_p;
    /* Limit work credit to 1.0 */
    caml_major_work_credit = fmin(caml_major_work_credit, 1.0);
  }

  p = filt_p;

  caml_gc_message (0x40, "filtered work-to-do = %"
                         ARCH_INTNAT_PRINTF_FORMAT "du\n",
                   (intnat) (p * 1000000));

  if (caml_gc_phase == Phase_idle){
    if (Caml_state->young_ptr == Caml_state->young_alloc_end){
      /* We can only start a major GC cycle if the minor allocation arena
         is empty, otherwise we'd have to treat it as a set of roots. */
      CAML_EV_BEGIN(EV_MAJOR_ROOTS);
      start_cycle ();
      CAML_EV_END(EV_MAJOR_ROOTS);
    }
    p = 0;
    goto finished;
  }

  if (p < 0){
    p = 0;
    goto finished;
  }

  if (caml_gc_phase == Phase_mark || caml_gc_phase == Phase_clean){
    computed_work = (intnat) (p * ((double) Caml_state->stat_heap_wsz * 250
                                   / (100 + caml_percent_free)
                                   + caml_incremental_roots_count));
  }else{
    computed_work = (intnat) (p * Caml_state->stat_heap_wsz * 5 / 3);
  }
  caml_gc_message (0x40, "computed work = %"
                   ARCH_INTNAT_PRINTF_FORMAT "d words\n", computed_work);
  if (caml_gc_phase == Phase_mark){
    CAML_EV_COUNTER (EV_C_MAJOR_WORK_MARK, computed_work);
    CAML_EV_BEGIN(EV_MAJOR_MARK);
    mark_slice (computed_work);
    CAML_EV_END(EV_MAJOR_MARK);
    caml_gc_message (0x02, "!");
  }else if (caml_gc_phase == Phase_clean){
    clean_slice (computed_work);
    caml_gc_message (0x02, "%%");
  }else{
    CAMLassert (caml_gc_phase == Phase_sweep);
    CAML_EV_COUNTER (EV_C_MAJOR_WORK_SWEEP, computed_work);
    CAML_EV_BEGIN(EV_MAJOR_SWEEP);
    sweep_slice (computed_work);
    CAML_EV_END(EV_MAJOR_SWEEP);
    caml_gc_message (0x02, "$");
  }

  if (caml_gc_phase == Phase_idle){
    CAML_EV_BEGIN(EV_MAJOR_CHECK_AND_COMPACT);
    caml_compact_heap_maybe ();
    CAML_EV_END(EV_MAJOR_CHECK_AND_COMPACT);
  }

 finished:
  caml_gc_message (0x40, "work-done = %"
                         ARCH_INTNAT_PRINTF_FORMAT "du\n",
                   (intnat) (p * 1000000));

  /* if some of the work was not done, take it back from the credit
     or spread it over the buckets. */
  p = filt_p - p;
  spend = fmin (p, caml_major_work_credit);
  caml_major_work_credit -= spend;
  if (p > spend){
    p -= spend;
    p /= caml_major_window;
    for (i = 0; i < caml_major_window; i++) caml_major_ring[i] += p;
  }

  Caml_state->stat_major_words += caml_allocated_words;
  caml_allocated_words = 0;
  caml_dependent_allocated = 0;
  caml_extra_heap_resources = 0.0;
  if (caml_major_slice_end_hook != NULL) (*caml_major_slice_end_hook) ();
}

/* This does not call [caml_compact_heap_maybe] because the estimates of
   free and live memory are only valid for a cycle done incrementally.
   Besides, this function itself is called by [caml_compact_heap_maybe].
*/
void caml_finish_major_cycle (void)
{
  if (caml_gc_phase == Phase_idle){
    p_backlog = 0.0; /* full major GC cycle, the backlog becomes irrelevant */
    start_cycle ();
  }
  while (caml_gc_phase == Phase_mark) mark_slice (LONG_MAX);
  while (caml_gc_phase == Phase_clean) clean_slice (LONG_MAX);
  CAMLassert (caml_gc_phase == Phase_sweep);
  CAMLassert (rescan_chunk == NULL);
  while (caml_gc_phase == Phase_sweep) sweep_slice (LONG_MAX);
  CAMLassert (caml_gc_phase == Phase_idle);
  Caml_state->stat_major_words += caml_allocated_words;
  caml_allocated_words = 0;
}

/* Call this function to make sure [bsz] is greater than or equal
   to both [Heap_chunk_min] and the current heap increment.
*/
asize_t caml_clip_heap_chunk_wsz (asize_t wsz)
{
  asize_t result = wsz;
  uintnat incr;

  /* Compute the heap increment as a word size. */
  if (caml_major_heap_increment > 1000){
    incr = caml_major_heap_increment;
  }else{
    incr = Caml_state->stat_heap_wsz / 100 * caml_major_heap_increment;
  }

  if (result < incr){
    result = incr;
  }
  if (result < Heap_chunk_min){
    result = Heap_chunk_min;
  }
  return result;
}

/* [heap_size] is a number of bytes */
void caml_init_major_heap (asize_t heap_size)
{
  int i;

  Caml_state->stat_heap_wsz =
    caml_clip_heap_chunk_wsz (Wsize_bsize (heap_size));
  Caml_state->stat_top_heap_wsz = Caml_state->stat_heap_wsz;
  CAMLassert (Bsize_wsize (Caml_state->stat_heap_wsz) % Page_size == 0);
  caml_heap_start =
    (char *) caml_alloc_for_heap (Bsize_wsize (Caml_state->stat_heap_wsz));
  if (caml_heap_start == NULL)
    caml_fatal_error ("cannot allocate initial major heap");
  Chunk_next (caml_heap_start) = NULL;
  Caml_state->stat_heap_wsz = Wsize_bsize (Chunk_size (caml_heap_start));
  Caml_state->stat_heap_chunks = 1;
  Caml_state->stat_top_heap_wsz = Caml_state->stat_heap_wsz;

  if (caml_page_table_add(In_heap, caml_heap_start,
        caml_heap_start + Bsize_wsize (Caml_state->stat_heap_wsz))
      != 0) {
    caml_fatal_error ("cannot allocate initial page table");
  }

  caml_fl_init_merge ();
  caml_make_free_blocks ((value *) caml_heap_start,
                         Caml_state->stat_heap_wsz, 1, Caml_white);
  caml_gc_phase = Phase_idle;

  Caml_state->mark_stack = caml_stat_alloc_noexc(sizeof(struct mark_stack));
  if (Caml_state->mark_stack == NULL)
    caml_fatal_error ("not enough memory for the mark stack");

  Caml_state->mark_stack->stack = caml_stat_alloc_noexc(MARK_STACK_INIT_SIZE * sizeof(mark_entry));
  if(Caml_state->mark_stack->stack == NULL) {
    caml_fatal_error("not enough memory for the mark stack");
  }

  Caml_state->mark_stack->count = 0;
  Caml_state->mark_stack->size = MARK_STACK_INIT_SIZE;

  caml_allocated_words = 0;
  caml_extra_heap_resources = 0.0;
  for (i = 0; i < Max_major_window; i++) caml_major_ring[i] = 0.0;
}

void caml_set_major_window (int w){
  uintnat total = 0;
  int i;
  if (w == caml_major_window) return;
  CAMLassert (w <= Max_major_window);
  /* Collect the current work-to-do from the buckets. */
  for (i = 0; i < caml_major_window; i++){
    total += caml_major_ring[i];
  }
  /* Redistribute to the new buckets. */
  for (i = 0; i < w; i++){
    caml_major_ring[i] = total / w;
  }
  caml_major_window = w;
}

void caml_finalise_heap (void)
{
  /* Finishing major cycle (all values become white) */
  caml_empty_minor_heap ();
  caml_finish_major_cycle ();
  CAMLassert (caml_gc_phase == Phase_idle);

  /* Finalising all values (by means of forced sweeping) */
  caml_fl_init_merge ();
  caml_gc_phase = Phase_sweep;
  sweep_chunk = caml_heap_start;
  caml_gc_sweep_hp = sweep_chunk;
  sweep_limit = sweep_chunk + Chunk_size (sweep_chunk);
  while (caml_gc_phase == Phase_sweep)
    sweep_slice (LONG_MAX);
}
