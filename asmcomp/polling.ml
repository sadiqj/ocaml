(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                Sadiq Jaffer, OCaml Labs Consultancy Ltd                *)
(*                                                                        *)
(*   Copyright 2020 OCaml Labs Consultancy Ltd                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This determines whether from a given instruction we unconditionally
   allocate and this is used to avoid adding polls unnecessarily *)
let polls_unconditionally ~future_funcnames:_ (_ : Mach.instruction) =
  false

let instrument_fundecl ~future_funcnames:_ (i : Mach.fundecl) : Mach.fundecl =
  i

let requires_prologue_poll ~future_funcnames:_ (_ : Mach.instruction) : bool =
  false
