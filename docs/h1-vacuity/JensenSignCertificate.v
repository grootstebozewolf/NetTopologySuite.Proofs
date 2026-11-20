(* JensenSignCertificate.v -- rational sign-alternation certificate for
   hyperbolicity of a real polynomial, with interval-enclosed coefficients.

   Probe for docs/attacks/2026-11-20-jensen-hyperbolicity-certificate.md
   ("Probe before xi"): mint the certificate bridge on an explicit rational
   polynomial before any xi / Jensen coefficient enters the trusted path.

   Certificate shape (the "orientation predicate" analogue):
     - a coefficient box  [lo_j, hi_j]  (rationals), j = 0..d,
       leading box excluding 0;
     - d+1 rational sample points  x_0 < x_1 < ... < x_d;
     - the exact rational enclosure of  P(x_i)  over the box has a strict
       sign s_i in {-1,+1}, and  s_i <> s_(i+1).
   The trusted check is `box_cert`, a boolean over Q (vm_compute).

   Theorem chain (all Qed, stdlib Reals only):
     box_cert box xs = true  /\  coefficients p : list R inside box
       -> p has exactly d real roots, pairwise distinct        (cert_sound)
       -> p = lead * prod (X - r_i)   i.e. hyperbolic           (hyperbolic)

   Multiplicity semantics (ticket Q4): `hyperbolic` is stated with a
   multiset of roots (repeated roots allowed).  The certificate proves the
   STRONGER `simple_real_rooted` and derives `hyperbolic` from it by a
   separate lemma.  Consequence: the certificate is sound but incomplete --
   a hyperbolic polynomial with a repeated root can never pass
   (`double_root_uncertifiable`), and a failed check is NOT a proof of
   non-hyperbolicity.  Nothing silently strengthens "hyperbolic" into
   "distinct real roots": the two predicates are separate definitions.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals QArith Qreals Lra Lia List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* 1. Polynomials as coefficient lists (low degree first), over R.     *)
(* ------------------------------------------------------------------ *)
Local Open Scope R_scope.

Fixpoint peval (p : list R) (x : R) : R :=
  match p with
  | [] => 0
  | a :: l => a + x * peval l x
  end.

Definition lead (p : list R) : R := last p 0.

Fixpoint prodlin (rs : list R) (x : R) : R :=
  match rs with
  | [] => 1
  | r :: t => (x - r) * prodlin t x
  end.

(* Degree convention: a coefficient list of length S d with nonzero last
   entry has degree d. *)

(* Hyperbolic = factors over R into linear factors (multiset of roots). *)
Definition hyperbolic (p : list R) : Prop :=
  exists rs, lead p <> 0 /\ S (length rs) = length p /\
             forall x, peval p x = lead p * prodlin rs x.

(* Simple real-rootedness: exactly deg p real roots, pairwise distinct,
   and they are all the real roots. *)
Definition simple_real_rooted (p : list R) : Prop :=
  exists rs, lead p <> 0 /\ S (length rs) = length p /\ NoDup rs /\
             (forall y, peval p y = 0 <-> In y rs) /\
             forall x, peval p x = lead p * prodlin rs x.

Lemma simple_real_rooted_hyperbolic p :
  simple_real_rooted p -> hyperbolic p.
Proof. intros (rs & H1 & H2 & _ & _ & H5). exists rs; auto. Qed.

Lemma peval_continuous p : continuity (peval p).
Proof.
  induction p as [|a l IH]; simpl.
  - apply continuity_const. intros ? ?; reflexivity.
  - apply (continuity_plus (fun _ => a) (fun x => x * peval l x)).
    + apply continuity_const. intros ? ?; reflexivity.
    + apply (continuity_mult (fun x => x) (peval l)); [|exact IH].
      apply derivable_continuous, derivable_id.
Qed.

(* Synthetic division by (X - r). *)
Fixpoint quot (r : R) (p : list R) : list R :=
  match p with
  | [] => []
  | a :: l => match l with [] => [] | _ :: _ => peval l r :: quot r l end
  end.

Lemma quot_spec r p x :
  peval p x = peval p r + (x - r) * peval (quot r p) x.
Proof.
  induction p as [|a l IH]; simpl; [ring|].
  destruct l as [|b l'].
  - simpl. ring.
  - simpl in *. rewrite IH. ring.
Qed.

Lemma quot_length r p : length (quot r p) = pred (length p).
Proof.
  induction p as [|a l IH]; simpl; [reflexivity|].
  destruct l as [|b l']; [reflexivity|]. simpl in *. now rewrite IH.
Qed.

Lemma quot_lead r p : (2 <= length p)%nat -> lead (quot r p) = lead p.
Proof.
  unfold lead. induction p as [|a l IH]; simpl; intros H; [lia|].
  destruct l as [|b l']; simpl in H; [lia|].
  destruct l' as [|c l''].
  - simpl. ring.
  - change (last (peval (b :: c :: l'') r :: quot r (b :: c :: l'')) 0
            = last (b :: c :: l'') 0).
    assert (Hq : quot r (b :: c :: l'') <> []).
    { simpl. discriminate. }
    destruct (quot r (b :: c :: l'')) as [|q qs] eqn:E; [contradiction|].
    rewrite <- E. rewrite <- IH by (simpl; lia).
    rewrite E. reflexivity.
Qed.

Lemma prodlin_zero rs y : prodlin rs y = 0 -> In y rs.
Proof.
  induction rs as [|r t IH]; simpl; intros H; [lra|].
  destruct (Rmult_integral _ _ H) as [H1|H1]; [left; lra|right; auto].
Qed.

Lemma prodlin_in rs y : In y rs -> prodlin rs y = 0.
Proof.
  induction rs as [|r t IH]; simpl; [tauto|].
  intros [<-|H]; [ring|rewrite IH by exact H; ring].
Qed.

(* d distinct roots of a length-(S d) list => full factorisation. *)
Lemma factor_from_roots rs : forall p,
  S (length rs) = length p -> NoDup rs ->
  (forall r, In r rs -> peval p r = 0) ->
  forall x, peval p x = lead p * prodlin rs x.
Proof.
  induction rs as [|r t IH]; intros p Hlen Hnd Hroot x.
  - destruct p as [|a [|b l]]; simpl in Hlen; try lia.
    unfold lead; simpl. ring.
  - simpl in Hlen. inversion Hnd as [|? ? Hnin Hnd']; subst.
    rewrite (quot_spec r p x), Hroot by (left; reflexivity).
    rewrite (IH (quot r p)).
    + rewrite quot_lead by lia. simpl. ring.
    + rewrite quot_length. lia.
    + exact Hnd'.
    + intros r' Hr'. pose proof (quot_spec r p r') as Hq.
      rewrite Hroot in Hq by (right; exact Hr').
      rewrite Hroot in Hq by (left; reflexivity).
      assert (r' - r <> 0) by (intro; apply Hnin; replace r with r' by lra; exact Hr').
      destruct (Rmult_integral (r' - r) (peval (quot r p) r')) as [E|E]; lra.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Real-side sign alternation  =>  simple real-rootedness.          *)
(* ------------------------------------------------------------------ *)

Fixpoint alternating (p : list R) (xs : list R) : Prop :=
  match xs with
  | [] => False
  | [_] => True
  | x0 :: ((x1 :: _) as rest) =>
      x0 < x1 /\ peval p x0 * peval p x1 < 0 /\ alternating p rest
  end.

Lemma alternating_roots p : forall xs x0,
  alternating p (x0 :: xs) ->
  exists rs, length rs = length xs /\ NoDup rs /\
             Forall (fun r => x0 < r) rs /\
             forall r, In r rs -> peval p r = 0.
Proof.
  induction xs as [|x1 xs IH]; intros x0 Halt.
  - exists []. repeat split; try constructor. simpl; tauto.
  - destruct Halt as (Hlt & Hsg & Hrest).
    destruct (IH x1 Hrest) as (rs & Hl & Hnd & Hgt & Hz).
    destruct (IVT_cor (peval p) x0 x1 (peval_continuous p) (Rlt_le _ _ Hlt)
                      (Rlt_le _ _ Hsg)) as (z & [Hz0 Hz1] & Hpz).
    assert (z <> x0) by (intro; subst; rewrite Hpz in Hsg; lra).
    assert (z <> x1) by (intro; subst; rewrite Hpz in Hsg; lra).
    exists (z :: rs). split; [simpl; lia|]. split; [|split].
    + constructor; [|exact Hnd].
      intro Hin. rewrite Forall_forall in Hgt. specialize (Hgt z Hin). lra.
    + constructor; [lra|].
      rewrite Forall_forall in *. intros r Hr. specialize (Hgt r Hr). lra.
    + intros r [<-|Hr]; auto.
Qed.

Theorem alternating_simple_real_rooted p xs :
  length xs = length p -> lead p <> 0 -> alternating p xs ->
  simple_real_rooted p.
Proof.
  intros Hlen Hlead Halt.
  destruct xs as [|x0 xs]; [contradiction|].
  destruct (alternating_roots p xs x0 Halt) as (rs & Hl & Hnd & _ & Hz).
  assert (Hlen' : S (length rs) = length p) by (simpl in Hlen; lia).
  pose proof (factor_from_roots rs p Hlen' Hnd Hz) as Hfac.
  exists rs. repeat split; auto.
  intros Hy. rewrite Hfac in Hy.
  apply Rmult_integral in Hy as [Hy|Hy]; [contradiction|].
  now apply prodlin_zero.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Rational interval certificate (the trusted, computed part).     *)
(* ------------------------------------------------------------------ *)
Local Open Scope Q_scope.

Definition box := list (Q * Q).   (* (lo, hi) per coefficient, low first *)

(* Exact range of c |-> sum c_j x^j over the box, for rational x
   (Horner with an exact scalar is exact: the map is linear in c). *)
Fixpoint ieval (b : box) (x : Q) : Q * Q :=
  match b with
  | [] => (0, 0)
  | (lo, hi) :: t =>
      let (l, h) := ieval t x in
      if Qle_bool 0 x then (lo + x * l, hi + x * h)
                      else (lo + x * h, hi + x * l)
  end.

Definition Qltb (a b : Q) : bool := negb (Qle_bool b a).

(* +1 / -1 for a strictly signed enclosure, 0 for "straddles zero". *)
Definition isign (lh : Q * Q) : Z :=
  let (l, h) := lh in
  if Qltb 0 l then 1%Z else if Qltb h 0 then (-1)%Z else 0%Z.

Fixpoint alt_check (b : box) (xs : list Q) : bool :=
  match xs with
  | [] => false
  | [x] => negb (Z.eqb (isign (ieval b x)) 0)
  | x0 :: ((x1 :: _) as rest) =>
      Qltb x0 x1 &&
      Z.eqb (isign (ieval b x0) * isign (ieval b x1)) (-1) &&
      alt_check b rest
  end.

Definition box_cert (b : box) (xs : list Q) : bool :=
  Nat.eqb (length xs) (length b) &&
  negb (Z.eqb (isign (last b (0, 0))) 0) &&
  alt_check b xs.

(* ------------------------------------------------------------------ *)
(* 4. Bridge: box_cert on Q  =>  alternating on R for every p in box. *)
(* ------------------------------------------------------------------ *)
Local Open Scope R_scope.

Definition in_box (p : list R) (b : box) : Prop :=
  Forall2 (fun c lh => Q2R (fst lh) <= c <= Q2R (snd lh)) p b.

Lemma Qltb_spec a b : Qltb a b = true -> Q2R a < Q2R b.
Proof.
  unfold Qltb. intros H. apply Qlt_Rlt.
  apply Qnot_le_lt. intros Hle. apply Qle_bool_iff in Hle.
  rewrite Hle in H. discriminate.
Qed.

Lemma Q2R_0 : Q2R 0 = 0.
Proof. unfold Q2R; simpl; field. Qed.

Lemma ieval_sound p b x :
  in_box p b ->
  Q2R (fst (ieval b x)) <= peval p (Q2R x) <= Q2R (snd (ieval b x)).
Proof.
  induction 1 as [|c [lo hi] p' b' Hc Hrest IH]; simpl.
  - rewrite Q2R_0. lra.
  - simpl in Hc. destruct (ieval b' x) as [l h]. simpl in IH.
    destruct (Qle_bool 0 x) eqn:Ex; simpl; rewrite !Q2R_plus, !Q2R_mult.
    + apply Qle_bool_iff, Qle_Rle in Ex. rewrite Q2R_0 in Ex.
      split; apply Rplus_le_compat; try lra;
        apply Rmult_le_compat_l; lra.
    + assert (Hx : Q2R x < 0).
      { rewrite <- Q2R_0. apply Qlt_Rlt, Qnot_le_lt.
        intros Hle; apply Qle_bool_iff in Hle; congruence. }
      split; apply Rplus_le_compat; try lra;
        apply Rmult_le_compat_neg_l; lra.
Qed.

Lemma isign_pos lh : isign lh = 1%Z -> 0 < Q2R (fst lh).
Proof.
  destruct lh as [l h]; unfold isign; simpl.
  destruct (Qltb 0 l) eqn:E1; [intros _; rewrite <- Q2R_0; now apply Qltb_spec|].
  destruct (Qltb h 0); discriminate.
Qed.

Lemma isign_neg lh : isign lh = (-1)%Z -> Q2R (snd lh) < 0.
Proof.
  destruct lh as [l h]; unfold isign; simpl.
  destruct (Qltb 0 l); [discriminate|].
  destruct (Qltb h 0) eqn:E2; [intros _; rewrite <- Q2R_0; now apply Qltb_spec|].
  discriminate.
Qed.

Lemma isign_cases lh : isign lh = 1%Z \/ isign lh = (-1)%Z \/ isign lh = 0%Z.
Proof.
  destruct lh as [l h]; unfold isign.
  destruct (Qltb 0 l); [auto|]. destruct (Qltb h 0); auto.
Qed.

Lemma sign_mul_neg p b x y :
  in_box p b ->
  (isign (ieval b x) * isign (ieval b y))%Z = (-1)%Z ->
  peval p (Q2R x) * peval p (Q2R y) < 0.
Proof.
  intros Hb Hs.
  pose proof (ieval_sound p b x Hb) as Bx.
  pose proof (ieval_sound p b y Hb) as By.
  destruct (isign_cases (ieval b x)) as [Ex|[Ex|Ex]];
  destruct (isign_cases (ieval b y)) as [Ey|[Ey|Ey]];
  rewrite Ex, Ey in Hs; try discriminate.
  - apply isign_pos in Ex. apply isign_neg in Ey.
    apply Rmult_pos_neg; lra.
  - apply isign_neg in Ex. apply isign_pos in Ey.
    rewrite Rmult_comm. apply Rmult_pos_neg; lra.
Qed.

Lemma alt_check_sound p b xs :
  in_box p b -> alt_check b xs = true -> alternating p (map Q2R xs).
Proof.
  intros Hb. induction xs as [|x0 rest IH]; simpl; [discriminate|].
  destruct rest as [|x1 rest']; [simpl; auto|].
  intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  simpl. split; [now apply Qltb_spec|]. split.
  - apply Z.eqb_eq in H2. now apply (sign_mul_neg p b).
  - apply IH. exact H3.
Qed.

Lemma in_box_length p b : in_box p b -> length p = length b.
Proof. induction 1; simpl; auto. Qed.

Lemma in_box_lead p b :
  in_box p b -> negb (Z.eqb (isign (last b (0%Q, 0%Q))) 0) = true -> lead p <> 0.
Proof.
  unfold lead. induction 1 as [|c lh p' b' Hc Hrest IH]; simpl.
  - unfold isign; simpl. unfold Qltb; simpl. discriminate.
  - destruct b' as [|lh' b''].
    + inversion Hrest; subst. simpl. intros Hs.
      destruct (isign_cases lh) as [E|[E|E]]; rewrite E in Hs; try discriminate.
      * apply isign_pos in E. lra.
      * apply isign_neg in E. lra.
    + inversion Hrest; subst. apply IH.
Qed.

(* MAIN BRIDGE THEOREM: a passed rational certificate makes EVERY real
   coefficient vector inside the box simple-real-rooted, hence hyperbolic. *)
Theorem cert_sound (p : list R) (b : box) (xs : list Q) :
  in_box p b -> box_cert b xs = true -> simple_real_rooted p.
Proof.
  intros Hb H. unfold box_cert in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1.
  apply (alternating_simple_real_rooted p (map Q2R xs)).
  - rewrite length_map, H1. symmetry. now apply in_box_length.
  - now apply (in_box_lead p b).
  - now apply (alt_check_sound p b).
Qed.

Corollary cert_hyperbolic p b xs :
  in_box p b -> box_cert b xs = true -> hyperbolic p.
Proof. intros; apply simple_real_rooted_hyperbolic; eapply cert_sound; eauto. Qed.

(* ------------------------------------------------------------------ *)
(* 5. Probe instance: a self-reciprocal rational quintic.               *)
(*    P = (X+1)(2X+1)(X+2)(3X+1)(X+3)                                   *)
(*      = 6 + 41X + 97X^2 + 97X^3 + 41X^4 + 6X^5                        *)
(*    Positive coefficients, negative roots -- the shape of a xi Jensen *)
(*    polynomial.  The proof never uses the factored form: only d+1    *)
(*    exact signs at rational points.                                   *)
(* ------------------------------------------------------------------ *)
Local Open Scope Q_scope.

Definition P5 : list Q := [6; 41; 97; 97; 41; 6].
Definition xs5 : list Q := [-4; -5#2; -3#2; -3#4; -2#5; -1#4].

Definition point_box (p : list Q) : box := map (fun q => (q, q)) p.
Definition width_box (d : Q) (p : list Q) : box :=
  map (fun q => (q - d, q + d)) p.

(* The certificate, decided by computation. *)
Lemma P5_cert : box_cert (point_box P5) xs5 = true.
Proof. vm_compute. reflexivity. Qed.

(* The exact sign list: the "orientation predicate" of this instance. *)
Lemma P5_signs :
  map (fun x => isign (ieval (point_box P5) x)) xs5 = [-1; 1; -1; 1; -1; 1]%Z.
Proof. vm_compute. reflexivity. Qed.

(* Robustness: absolute width 1/20 on every coefficient keeps the
   certificate (minimal normalised margin at these points is
   |P(x)| / sum |x|^j = 8/133 ~ 0.0602, attained at x = -5/2 and -2/5). *)
Lemma P5_cert_width : box_cert (width_box (1#20) P5) xs5 = true.
Proof. vm_compute. reflexivity. Qed.

(* ... and width 1/10 is rejected at THESE points (the checker straddles
   zero at x = -5/2).  This is a statement about the checker with fixed
   points, not a claim that the widened family contains a non-hyperbolic
   member. *)
Lemma P5_reject_width : box_cert (width_box (1#10) P5) xs5 = false.
Proof. vm_compute. reflexivity. Qed.

Local Open Scope R_scope.

Definition P5R : list R := map Q2R P5.

Lemma in_point_box p : in_box (map Q2R p) (point_box p).
Proof.
  induction p as [|q t IH]; simpl; constructor; [simpl; lra|exact IH].
Qed.

Theorem P5_simple_real_rooted : simple_real_rooted P5R.
Proof. exact (cert_sound _ _ _ (in_point_box P5) P5_cert). Qed.

Theorem P5_hyperbolic : hyperbolic P5R.
Proof. exact (cert_hyperbolic _ _ _ (in_point_box P5) P5_cert). Qed.

(* Every real quintic with coefficients within 1/20 of P5 is hyperbolic
   with 5 distinct real roots -- the interval-enclosure form that a xi
   Jensen instance will have to take. *)
Theorem P5_neighbourhood_hyperbolic (p : list R) :
  in_box p (width_box (1#20) P5) -> simple_real_rooted p.
Proof. intros H. exact (cert_sound _ _ _ H P5_cert_width). Qed.

(* ------------------------------------------------------------------ *)
(* 6. Multiplicity semantics (ticket Q4).                               *)
(* ------------------------------------------------------------------ *)

(* (X+1)^2 (X+2) = 2 + 5X + 4X^2 + X^3 is hyperbolic ... *)
Definition D3 : list Q := [2; 5; 4; 1]%Q.

Lemma D3_hyperbolic : hyperbolic (map Q2R D3).
Proof.
  exists [-1; -1; -2]. unfold lead; simpl.
  unfold Q2R; simpl. split; [lra|]. split; [reflexivity|].
  intros x. field.
Qed.

(* ... but no sign certificate (at any points, any box containing it)
   can ever pass: soundness would give 3 distinct roots, and the only
   real roots are -1 and -2.  The certificate is sound, not complete. *)
Theorem double_root_uncertifiable (b : box) (xs : list Q) :
  in_box (map Q2R D3) b -> box_cert b xs = false.
Proof.
  intros Hb. destruct (box_cert b xs) eqn:E; [|reflexivity]. exfalso.
  destruct (cert_sound _ _ _ Hb E) as (rs & _ & Hl & Hnd & Hiff & _).
  simpl in Hl. injection Hl as Hl.
  assert (Hr : forall y, In y rs -> y = -1 \/ y = -2).
  { intros y Hy. apply Hiff in Hy. unfold Q2R in Hy; simpl in Hy.
    assert (Hf : (y + 1) * (y + 1) * (y + 2) = 0) by lra.
    apply Rmult_integral in Hf as [Hf|Hf];
      [apply Rmult_integral in Hf as [Hf|Hf]|]; lra. }
  destruct rs as [|a [|b' [|c [|? ?]]]]; simpl in Hl; try discriminate.
  inversion Hnd as [|? ? Ha Hnd1]; subst. inversion Hnd1 as [|? ? Hb' _]; subst.
  assert (Ha' := Hr a (or_introl eq_refl)).
  assert (Hb2 := Hr b' (or_intror (or_introl eq_refl))).
  assert (Hc' := Hr c (or_intror (or_intror (or_introl eq_refl)))).
  inversion Hnd1 as [|? ? Hb3 Hnd2]; subst.
  simpl in Ha, Hb3.
  destruct Ha' as [-> | ->]; destruct Hb2 as [-> | ->];
    destruct Hc' as [-> | ->]; tauto.
Qed.

(* X^2 + 1 is not hyperbolic, and likewise never certifies. *)
Theorem no_real_roots_uncertifiable (b : box) (xs : list Q) :
  in_box (map Q2R [1; 0; 1]%Q) b -> box_cert b xs = false.
Proof.
  intros Hb. destruct (box_cert b xs) eqn:E; [|reflexivity]. exfalso.
  destruct (cert_sound _ _ _ Hb E) as (rs & _ & Hl & _ & Hiff & _).
  destruct rs as [|y l]; simpl in Hl; try discriminate.
  assert (Hy : In y (y :: l)) by (left; reflexivity).
  apply Hiff in Hy. unfold Q2R in Hy; simpl in Hy.
  pose proof (Rle_0_sqr y). unfold Rsqr in *. lra.
Qed.

Print Assumptions P5_neighbourhood_hyperbolic.
Print Assumptions double_root_uncertifiable.
