#define CAML_NAME_SPACE

#include "caml/alloc.h"
#include "caml/eventring.h"
#include "caml/fail.h"
#include "caml/memory.h"
#include "caml/mlvalues.h"

#include <assert.h>

static int minors = 0;
static int majors = 0;
static int compacts = 0;

static int minor_started = 0;
static int major_started = 0;
static int compact_started = 0;

void ev_begin(uint64_t timestamp, ev_gc_phase phase) {
    switch( phase ) {
        case EV_MINOR:
            minor_started = 1;
            break;
        case EV_MAJOR:
            major_started = 1;
            break;
        case EV_COMPACT_MAIN:
            compact_started = 1;
            break;
    }
}

void ev_end(uint64_t timestamp, ev_gc_phase phase) {
    switch( phase ) {
        case EV_MINOR:
            assert(minor_started);
            minor_started = 0;
            minors++;
            break;
        case EV_MAJOR:
            assert(major_started);
            major_started = 0;
            majors++;
            break;
        case EV_COMPACT_MAIN:
            assert(compact_started);
            compact_started = 0;
            compacts++;
            break;
    }
}

value get_event_counts(void) {
    CAMLparam0();
    CAMLlocal1(counts_tuple);
    counts_tuple = caml_alloc_small(3, 0);

    struct caml_eventring_cursor* cursor = caml_eventring_create_cursor("/tmp/", Caml_state->eventlog_startup_pid);

    if( !cursor ) {
        caml_failwith("invalid or non-existent cursor");
    }

    struct caml_eventring_callbacks callbacks = { 0 };

    callbacks.ev_begin = ev_begin;
    callbacks.ev_end = ev_end;

    int read_events = caml_eventring_read_poll(cursor, &callbacks);

    Field(counts_tuple, 0) = Val_long(minors);
    Field(counts_tuple, 1) = Val_long(majors);
    Field(counts_tuple, 2) = Val_long(compacts);

    caml_eventring_free_cursor(cursor);

    CAMLreturn(counts_tuple);   
}