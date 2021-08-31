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

#ifndef CAML_EVENTRING_H
#define CAML_EVENTRING_H

#include "eventlog.h"
#include <stdint.h>

#define CAML_HAS_EVENTRING

#define CAML_EVENTRING_INIT() caml_eventring_init()
#define CAML_EV_BEGIN(p) caml_ev_begin(p)
#define CAML_EV_END(p) caml_ev_end(p)
#define CAML_EV_COUNTER(c, v) caml_ev_counter(c, v)
#define CAML_EV_ALLOC(s) caml_ev_alloc(s)
#define CAML_EV_ALLOC_FLUSH() caml_ev_alloc_flush()
#define CAML_EV_FLUSH() caml_ev_flush()

/* external C-API for reading from the eventring */
struct caml_eventring_cursor;

struct caml_eventring_callbacks {
    void (*ev_begin)(uint64_t timestamp, ev_gc_phase phase);
    void (*ev_end)(uint64_t timestamp, ev_gc_phase phase);
    void (*ev_counter)(uint64_t timestamp, ev_gc_counter counter, uint64_t val);
    void (*ev_alloc)(uint64_t timestamp, uint64_t* sz);
    void (*ev_lifecycle)(int64_t timestamp, ev_lifecycle lifecycle);
    void (*ev_lost_events)(int lost_events);
};

/* [eventring_path] is a path to a directory containing eventrings. [pid] is the
    process id (or equivalent) of the startup OCaml process. This function will
    return a cursor which can we be used with caml_eventring_read_poll to read
    events from the eventrings. */
CAMLextern struct caml_eventring_cursor* caml_eventring_create_cursor(
                                        char* eventring_path,
                                        int pid);

/* frees a cursor obtained from caml_eventring_creator_cursor */
CAMLextern void caml_eventring_free_cursor(struct caml_eventring_cursor* cursor);

/* polls the eventring pointed to by [cursor] and calls the appropriate callback
    provided in [callbacks] for each new event. Returns the number of events
    consumed. */
CAMLextern int caml_eventring_read_poll(struct caml_eventring_cursor* cursor,
                             struct caml_eventring_callbacks* callbacks);

/* TODO: OCaml API for reading from the eventring */

 /* Functions for putting runtime data on to the eventring */

void caml_eventring_init();
void caml_eventring_destroy();
void caml_eventring_start();
void caml_eventring_pause();
void caml_eventring_resume();
void caml_ev_begin(ev_gc_phase phase);
void caml_ev_end(ev_gc_phase phase);
void caml_ev_counter(ev_gc_counter counter, uint64_t val);
void caml_ev_alloc(uint64_t sz);
void caml_ev_alloc_flush();
void caml_ev_flush();

#endif /*CAML_EVENTRING_H*/

