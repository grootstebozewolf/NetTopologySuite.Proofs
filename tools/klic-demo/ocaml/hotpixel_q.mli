
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val snd : ('a1, 'a2) prod -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val size_nat : positive -> nat

  val ggcdn :
    nat -> positive -> positive -> (positive, (positive, positive) prod) prod

  val ggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val of_nat : nat -> z

  val to_pos : z -> positive

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val div : z -> z -> z

  val modulo : z -> z -> z

  val even : z -> bool

  val sgn : z -> z

  val abs : z -> z

  val ggcd : z -> z -> (z, (z, z) prod) prod
 end

type q = { qnum : z; qden : positive }

val inject_Z : z -> q

val qeq_bool : q -> q -> bool

val qle_bool : q -> q -> bool

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

val qred : q -> q

val q_min : q -> q -> q

val q_max : q -> q -> q

val q_round_ne : q -> z

val q_snap_coord : q -> q -> q

type qPoint = { qx : q; qy : q }

val q_snap : qPoint -> q -> qPoint

val q_snap_disp : q -> q -> q

val q_axis : q -> q -> q -> q -> (q, q) prod option

val q_hot_pixel_radius : q -> q

val q_touches_closed : qPoint -> qPoint -> qPoint -> q -> bool

val q_passes_through_closed : qPoint -> qPoint -> qPoint -> q -> bool

val q_seg_intersection : qPoint -> qPoint -> qPoint -> qPoint -> qPoint option
