open Symbolic_domain
open Syntax
open Counter

module type SYMBOLIC_ANALYSIS = sig
  module C : COUNTER
  module D : SYMBOLIC_DOMAIN
  type config = Lang.block_aux * D.state * Flag.t * Id.t * C.t
  val init: ?svm:D.svm option -> Prog.prog -> config
  val get_block: config -> Lang.block_aux
  val get_state: config -> D.state
  val get_flag: config -> Flag.t
  val get_id: config -> Id.t
  val get_counter: config -> C.t
  val set_flag: Flag.t -> config -> config
  val set_state: D.state -> config -> config
  val set_block: Lang.block_aux -> config -> config
  val set_id: Id.t -> config -> config
  val set_counter: C.t -> config -> config
  val lthr_ref: Threshold.t ref
  val set_thr: Threshold.t -> unit
  val stmt_assign: config -> config
  val stmt_input: config-> config
  val stmt_if: config -> config option * config option
  val stmt_while: config -> config
  val stmt_loop_norm: config -> config option * config option
  (* val stmt_loop_max_dirty: config -> config *)
  val stmt_loop_max: ?modset:(Var.VSet.t option) -> ?dirty:bool -> config -> config
  (* val stmt_loop: config -> config list *)
  val exec_stmt: config -> config list
  val exec_list: config list -> config list
  val exec_block: config -> config list
  val analyze_prog: Prog.prog -> Threshold.t -> config list
end