(* Standalone probe: is `geometric_interior_stdlib` satisfiable at all?
   Compiled against the real corpus definitions. *)
From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingCorrect PointInRingTangents.
Import ListNotations.
Local Open Scope R_scope.

(* ---- An x-coordinate bound for every point lying on a ring's skeleton ---- *)
(* fold of |px(fst e)| + |px(snd e)| over the edge list; clearly >= 0 and
   dominates the x-coordinate of any convex combination on any edge. *)
Fixpoint xbound (es : list Edge) : R :=
  match es with
  | [] => 0
  | e :: es' => Rabs (px (fst e)) + Rabs (px (snd e)) + xbound es'
  end.

Lemma xbound_nonneg : forall es, 0 <= xbound es.
Proof.
  induction es as [|e es IH]; simpl; [lra|].
  pose proof (Rabs_pos (px (fst e))); pose proof (Rabs_pos (px (snd e))); lra.
Qed.

(* Any point on the skeleton has px <= xbound (ring_edges). *)
Lemma ring_image_px_le : forall r q, ring_image r q -> px q <= xbound (ring_edges r).
Proof.
  intros r q [e [t [Hin [Ht [Hx _]]]]].
  revert Hin. generalize (ring_edges r) as es. clear r.
  induction es as [|e0 es IH]; simpl; [contradiction|].
  intros [He | He].
  - subst e0. rewrite Hx.
    pose proof (xbound_nonneg es).
    pose proof (Rabs_pos (px (fst e))) as Hfa.
    pose proof (Rabs_pos (px (snd e))) as Hsa.
    pose proof (Rle_abs (px (fst e))) as Hf.
    pose proof (Rle_abs (px (snd e))) as Hs.
    (* (1-t)*a + t*b <= |a| + |b| for 0<=t<=1 *)
    nra.
  - pose proof (IH He). pose proof (Rabs_pos (px (fst e0))).
    pose proof (Rabs_pos (px (snd e0))). lra.
Qed.

(* ====================================================================== *)
(* MAIN: geometric_interior_stdlib is FALSE for every point and ring.     *)
(* The defect: connected_in_complement does not require `path` to be      *)
(* continuous, so a step path links p to ANY off-ring point.  The ring    *)
(* skeleton is bounded, so off-ring points reach arbitrarily far out, and *)
(* no finite bound M can contain them -- in_bounded_component is empty.   *)
(* ====================================================================== *)
Theorem geometric_interior_stdlib_universally_false :
  forall (p : Point) (r : Ring), ~ geometric_interior_stdlib p r.
Proof.
  intros p r [Hpoff [M [HMpos Hbnd]]].
  set (B := Rmax (xbound (ring_edges r)) M + 1).
  set (q := mkPoint B 0).
  assert (HBxb : xbound (ring_edges r) < B).
  { unfold B. pose proof (Rmax_l (xbound (ring_edges r)) M). lra. }
  assert (HBM : M < B).
  { unfold B. pose proof (Rmax_r (xbound (ring_edges r)) M). lra. }
  (* q is off the ring: its x-coordinate exceeds the skeleton's x-bound. *)
  assert (Hqoff : ring_complement r q).
  { intro Himg. apply ring_image_px_le in Himg. unfold q in Himg; simpl in Himg. lra. }
  (* Discontinuous step path links p to the far point q within the complement. *)
  assert (Hcon : connected_in_complement r p q).
  { exists (fun t => if Req_EM_T t 1 then q else p).
    split; [|split].
    - destruct (Req_EM_T 0 1) as [E|_]; [lra|reflexivity].
    - destruct (Req_EM_T 1 1) as [_|N]; [reflexivity|lra].
    - intros t _. destruct (Req_EM_T t 1); assumption. }
  specialize (Hbnd q Hcon). unfold q in Hbnd; simpl in Hbnd.
  (* px q = B, py q = 0, so B*B <= M*M, contradicting 0 < M < B. *)
  nra.
Qed.

(* Corollary: under the corpus's concrete H1 instantiation, point_in_ring is
   forced false on EVERY closed/simple ring -- regardless of geometry. *)
Corollary H1_forces_not_point_in_ring :
  (forall q r, ring_closed r -> ring_simple r ->
     point_in_ring q r <-> geometric_interior_stdlib q r) ->
  forall q r, ring_closed r -> ring_simple r -> ~ point_in_ring q r.
Proof.
  intros H1 q r Hc Hs Hpir.
  apply (geometric_interior_stdlib_universally_false q r).
  apply (H1 q r Hc Hs). exact Hpir.
Qed.

Print Assumptions geometric_interior_stdlib_universally_false.
