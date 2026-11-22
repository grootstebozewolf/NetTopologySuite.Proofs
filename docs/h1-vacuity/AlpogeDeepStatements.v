(* AlpogeDeepStatements.v -- STATEMENTS ONLY (no proofs) of four unrefined
   items of the claimed RH/GRH Lean development
   (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0):

     TopG              CharacterBoxes/ZeroFreeAllOfTopG.lean
     HostExW           GlobalTwisting/ThinScalesIffHostBound.lean (+ supplyChi)
     poleData          LandauTheorems/poleData.lean (+ PoleData, poleData_char)
     landau_pole_asym  LandauTheorems/LandauPoleAsym.lean (+ _deriv)

   Each item is a Rocq Definition of type Prop: its Lean statement, refined
   into named sub-statements.  Nothing here is asserted: there are no
   Theorems, Lemmas, Axioms, Parameters or Admitted.  Every definition lives
   over Stdlib's R and stays within the three-axiom allowlist
   (docs/axiom-allowlist.txt); x^a is AlpogeRealsQED2.v's allowlist-clean
   rpc, since Stdlib's Rpower carries Classical_Prop.classic.

   Representation (statement level):
   - C is R x R with the usual operations; |z| = sqrt(re^2 + im^2).
   - "eventually in a punctured neighbourhood", complex differentiability,
     AnalyticAt (a convergent power series on a disc) and iterated
     derivatives are defined from epsilon-delta limits and Stdlib's Un_cv.
   - The Laplace integral over (0, oo) is the limit T -> oo of Riemann
     integrals over [0, T] (real and imaginary parts); an integral's value
     is the limit of uniform Riemann sums of a Riemann-integrable function
     (Stdlib's RiemannInt value carries Classical_Prop.classic).  Lean uses
     the Bochner integral; Mathlib's "Measurable g" becomes local Riemann
     integrability.  Both substitutions are recorded in the finding.
   - The development's deep carriers (Ranks, Host, Frame data, FamP fields,
     ChainTied, VVle, EAtH, HostGood, RankVal, L-function zeros) are section
     variables, exactly as opaque as they are to the statements themselves.

   Evidence for docs/attacks/2026-11-21-alpoge-deep-statements.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra List Factorial.
From NTS.Proofs.Probes Require Import AlpogeRealsQED2.
Local Open Scope R_scope.

(* ===================================================================== *)
(* Complex numbers as R x R                                               *)
(* ===================================================================== *)
Record Cc : Type := mkC { cre : R; cim : R }.
Definition cadd (a b : Cc) : Cc := mkC (cre a + cre b) (cim a + cim b).
Definition csub (a b : Cc) : Cc := mkC (cre a - cre b) (cim a - cim b).
Definition cmul (a b : Cc) : Cc := mkC (cre a * cre b - cim a * cim b) (cre a * cim b + cim a * cre b).
Definition cnorm (a : Cc) : R := sqrt (cre a * cre a + cim a * cim a).
Definition cinv (a : Cc) : Cc :=
  mkC (cre a / (cre a * cre a + cim a * cim a)) (- cim a / (cre a * cre a + cim a * cim a)).
Definition cdiv (a b : Cc) : Cc := cmul a (cinv b).
Definition cofR (x : R) : Cc := mkC x 0.
Fixpoint cpow (a : Cc) (n : nat) : Cc := match n with O => cofR 1 | S m => cmul a (cpow a m) end.
Definition cexp (a : Cc) : Cc := mkC (exp (cre a) * cos (cim a)) (exp (cre a) * sin (cim a)).
Definition cconj (a : Cc) : Cc := mkC (cre a) (- cim a).

(* ===================================================================== *)
(* Analytic vocabulary                                                    *)
(* ===================================================================== *)
(* forall^f s in nhds[!=] rho, P s *)
Definition EvPunct (rho : Cc) (P : Cc -> Prop) : Prop :=
  exists d, 0 < d /\ forall s, 0 < cnorm (csub s rho) -> cnorm (csub s rho) < d -> P s.

(* HasDerivWithinAt f L S z (complex) *)
Definition CDerivWithin (f : Cc -> Cc) (L : Cc) (S : Cc -> Prop) (z : Cc) : Prop :=
  forall eps, 0 < eps -> exists d, 0 < d /\ forall w, S w -> 0 < cnorm (csub w z) -> cnorm (csub w z) < d ->
    cnorm (csub (cdiv (csub (f w) (f z)) (csub w z)) L) < eps.

Definition CDifferentiableOn (f : Cc -> Cc) (S : Cc -> Prop) : Prop :=
  forall z, S z -> exists L, CDerivWithin f L S z.

(* partial sums of a complex power series about rho, at w *)
Fixpoint psum (a : nat -> Cc) (rho w : Cc) (n : nat) : Cc :=
  match n with
  | O => cmul (a O) (cpow (csub w rho) O)
  | S m => cadd (psum a rho w m) (cmul (a (S m)) (cpow (csub w rho) (S m)))
  end.

(* AnalyticAt h rho: a power series converging to h on a disc about rho *)
Definition CAnalyticAt (h : Cc -> Cc) (rho : Cc) : Prop :=
  exists r (a : nat -> Cc), 0 < r /\ forall w, cnorm (csub w rho) < r ->
    Un_cv (fun n => cre (psum a rho w n)) (cre (h w)) /\ Un_cv (fun n => cim (psum a rho w n)) (cim (h w)).

Definition ball (z : Cc) (r : R) (w : Cc) : Prop := cnorm (csub w z) < r.

(* D is the family of iterated derivatives of Phi on the open set S:
   D 0 = Phi on S and D (k+1) is the derivative of D k on S.  (Stands for
   Mathlib's iteratedDeriv on an open set, where it is unique.) *)
Definition IterDerivs (Phi : Cc -> Cc) (U : Cc -> Prop) (D : nat -> Cc -> Cc) : Prop :=
  (forall z, U z -> D O z = Phi z) /\ (forall k z, U z -> CDerivWithin (D k) (D (S k) z) U z).

(* The value of a Riemann integral.  Stdlib's RiemannInt carries
   Classical_Prop.classic (Print Assumptions), Riemann_integrable does not;
   so the value is the limit of uniform left Riemann sums, which equals the
   integral for every Riemann-integrable function. *)
Definition RSum (f : R -> R) (a b : R) (n : nat) : R :=
  (b - a) / INR (S n) * sum_f_R0 (fun j => f (a + INR j * (b - a) / INR (S n))) n.
Definition IntVal (f : R -> R) (a b I : R) : Prop :=
  (exists _ : Riemann_integrable f a b, True) /\ Un_cv (RSum f a b) I.

(* the Laplace integral  int_(0,oo) g u e^(-s u) du = L, as the T -> oo limit
   of Riemann integrals over [0, T] of the real and imaginary parts *)
Definition LaplaceAt (g : R -> R) (s : Cc) (L : Cc) : Prop :=
  let fr := fun u => g u * exp (- cre s * u) * cos (cim s * u) in
  let fi := fun u => - g u * exp (- cre s * u) * sin (cim s * u) in
  forall eps, 0 < eps -> exists T0, 0 < T0 /\ forall T, T0 <= T ->
    exists Ir Ii, IntVal fr 0 T Ir /\ IntVal fi 0 T Ii /\
      Rabs (Ir - cre L) < eps /\ Rabs (Ii - cim L) < eps.

(* Mathlib "Measurable g", replaced at statement level by local Riemann
   integrability *)
Definition LocInt (g : R -> R) : Prop := forall a b, a <= b -> exists _ : Riemann_integrable g a b, True.

(* ===================================================================== *)
(* (P) poleData                                                           *)
(* ===================================================================== *)
(* structure PoleData (LandauZeroFreeCriterion.lean l.15) *)
Definition PoleData (g : R -> R) (Phi : Cc -> Cc) (Z : Cc -> Prop) : Prop :=
  (* meas *)    LocInt g /\
  (* growth *)  (exists C, forall u, 0 <= u -> Rabs (g u) <= C * exp (2 * u)) /\
  (* laplace *) (forall s, 2 < cre s -> LaplaceAt g s (Phi s)) /\
  (* pos *)     (forall rho, Z rho -> 0 < cre rho) /\
  (* diff *)    CDifferentiableOn Phi (fun s => 0 < cre s /\ ~ Z s) /\
  (* iso *)     (forall z, 0 < cre z -> EvPunct z (fun w => ~ Z w)) /\
  (* pole *)    (forall rho, Z rho -> exists c, c <> cofR 0 /\
                   (cim rho = 0 -> 0 < cre c /\ cim c = 0) /\
                   exists h, CAnalyticAt h rho /\
                     EvPunct rho (fun s => Phi s = cadd (cdiv c (csub s rho)) (h s))).

Section PoleDataStatements.
(* CharFamily: indices, characters' L-function zero predicates, weights > 0 *)
Variable Ix : Type.
Variable LZ : Ix -> Cc -> Prop.               (* DirichletCharacter.LFunction (F.chi i) s = 0 *)
Variable GmF : R -> R.                        (* Gm F *)

Definition gm (u : R) : R := GmF (exp u).     (* gm F u = Gm F (exp u) *)
Definition zeroSet (rho : Cc) : Prop :=        (* zeroSet F *)
  0 < cre rho /\ exists i, LZ i rho \/ LZ i (cconj rho).

(* poleData : forall F : CharFamily, exists Phi, PoleData (gm F) Phi (zeroSet F) *)
Definition poleData_statement : Prop := exists Phi : Cc -> Cc, PoleData gm Phi zeroSet.

(* refinement: the per-character statement poleData_char (l.137), from which
   poleData is assembled as Phi = sum_i (a_i/2)(Phi1(chi_i) + Phi2(chi_i^-1)) *)
Variable Gchi : R -> R.                       (* Re-part kernel Gchi chi (exp u), one character *)
Variable LZchi : Cc -> Prop.                  (* L(chi, s) = 0 *)
Definition poleData_char_statement : Prop :=
  exists Phi : Cc -> Cc,
    (forall s, 2 < cre s -> LaplaceAt (fun u => Gchi (exp u)) s (Phi s)) /\
    (forall rho, rho <> cofR 0 -> ~ LZchi rho -> CAnalyticAt Phi rho) /\
    (forall rho, rho <> cofR 0 -> exists m : nat, (m = 0%nat <-> ~ LZchi rho) /\
       exists h, CAnalyticAt h rho /\
         EvPunct rho (fun s => Phi s =
           cadd (cdiv (cmul (cofR (INR m)) (cdiv (cofR (-1)) (cmul rho (csub rho (cofR 1))))) (csub s rho)) (h s))) /\
    (forall z, EvPunct z (fun w => ~ LZchi w)).
End PoleDataStatements.

(* ===================================================================== *)
(* (A) landau_pole_asym                                                   *)
(* ===================================================================== *)
(* landau_pole_asym_deriv: the k-th derivative of c (s - rho)^-1 at z is
   c (-1)^k k! (z - rho)^-(k+1). *)
Definition landau_pole_asym_deriv_statement : Prop :=
  forall (c rho z : Cc) (k : nat) (D : nat -> Cc -> Cc),
    z <> rho ->
    IterDerivs (fun s => cmul c (cinv (csub s rho))) (fun s => s <> rho) D ->
    D k z = cmul c (cmul (cmul (cpow (cofR (-1)) k) (cofR (INR (fact k)))) (cinv (cpow (csub z rho) (S k)))).

(* landau_pole_asym:  rho in ball z r, rho <> z, Phi differentiable on the
   punctured ball, Phi = c/(s - rho) + h near rho with h analytic at rho,
   0 < r' < r  ==>  exists M, forall k,
   | (-1)^k Phi^(k)(z)/k! - c/(z - rho)^(k+1) | <= M / r'^k. *)
Definition landau_pole_asym_statement : Prop :=
  forall (Phi : Cc -> Cc) (z rho c : Cc) (r r' : R),
    ball z r rho -> rho <> z ->
    CDifferentiableOn Phi (fun w => ball z r w /\ w <> rho) ->
    (exists h, CAnalyticAt h rho /\ EvPunct rho (fun s => Phi s = cadd (cdiv c (csub s rho)) (h s))) ->
    0 < r' -> r' < r ->
    forall D, IterDerivs Phi (fun w => ball z r w /\ w <> rho) D ->
    exists M, forall k : nat,
      cnorm (csub (cdiv (cmul (cpow (cofR (-1)) k) (D k z)) (cofR (INR (fact k))))
                  (cdiv c (cpow (csub z rho) (S k))))
      <= M / pow r' k.

(* ===================================================================== *)
(* (H) HostExW   and   (T) TopG                                           *)
(* ===================================================================== *)
Section TopStatements.
(* Scale (DataParams2.lean l.9) *)
Record Scale : Type := mkScale {
  sx : R; seps : R; sJ : R; sb : R;
  s_one_lt : 1 < sx; s_eps_pos : 0 < seps; s_eps_lt : seps < 1 / 52; s_one_le_J : 1 <= sJ }.

(* Scales la (PrimeDiscriminants/Scales.lean l.9) *)
Record Scales (la : R) : Type := mkScales {
  SJ : R; S_one_le_J : 1 <= SJ; SWin : R -> Prop;
  S_windows : forall y, exists Y, y <= Y /\ forall x, Y <= x -> x <= rpc Y la -> SWin x }.
Definition ScalesMem {la} (S : Scales la) (s : Scale) : Prop := sJ s = SJ la S /\ SWin la S (sx s).

(* deep host carriers *)
Variable Ranks : Type.
Variable Host : Ranks -> Type.
Variable HostCT2 : forall Rk, Host Rk -> R.
Variable RankVal : Scale -> Ranks -> Prop.
Variable HostGood : Scale -> R -> R -> R -> R -> forall Rk, Host Rk -> nat -> Prop.

(* HostReq := R -> Scale -> forall R : Ranks, Host R -> nat -> Prop *)
Definition HostReq : Type := R -> Scale -> forall Rk : Ranks, Host Rk -> nat -> Prop.

(* HostExW la P (ThinScalesIffHostBound.lean l.120) *)
Definition HostExW (la : R) (P : HostReq) : Prop :=
  forall eps, 0 < eps -> eps < 1 / 52 ->
    exists CT2 C8 C5 c6 Cb x0, 1 <= C8 /\ 0 < C5 /\ 0 < c6 /\ 0 < Cb /\
      exists S : Scales la, forall s : Scale, seps s = eps -> x0 <= sx s -> ScalesMem S s ->
        exists (Rk : Ranks) (H : Host Rk) (q0 : nat),
          RankVal s Rk /\ HostCT2 Rk H = CT2 /\ HostGood s C8 C5 c6 Cb Rk H q0 /\ P C5 s Rk H q0.

(* families FamP eps (fields used by TopG's statement) *)
Variable FamP : R -> Type.
Variable fx1 : forall eps, FamP eps -> R.
Variable fIx : forall eps, FamP eps -> R -> Type.
Variable fWin : forall eps, FamP eps -> R -> Prop.
Variable ChainTied : forall eps, FamP eps -> R -> R -> R -> R -> R -> R -> R -> Prop.
Variable VV : forall eps (Fm : FamP eps) x, fIx eps Fm x -> Prop.   (* VVle (D x i).host.E (D x i).R.t (sqrt (L x i).sc.b) *)

(* FReq and its two projections (Supply.lean): req (to a HostReq) and the
   per-family-member predicate At used by cls *)
Variable FReq : Type.
Variable req : FReq -> HostReq.
Variable At : FReq -> forall eps (Fm : FamP eps) x, fIx eps Fm x -> Prop.   (* G.At (Fm.L x i) *)

Definition FamClass : Type := forall eps, FamP eps -> Prop.

(* FamCore.Windows (FamCore.lean l.155) *)
Definition FWindows {eps} (Fm : FamP eps) (la : R) : Prop :=
  forall y, exists Y, y <= Y /\ forall x, Y <= x -> x <= rpc Y la -> fWin eps Fm x.

(* FReq.cls la (Supply.lean) *)
Definition cls (G : FReq) (la : R) : FamClass := fun eps Fm =>
  FWindows Fm la /\ forall x, fx1 eps Fm < x -> forall i : fIx eps Fm x, At G eps Fm x i.

(* HypV (DivinNOfHypV.lean l.10) *)
Definition HypV {eps} (Fm : FamP eps) : Prop :=
  exists x0, forall x, x0 <= x -> forall i : fIx eps Fm x, VV eps Fm x i.

(* FamilyClassConnected (DivinNOfHypV.lean l.13) *)
Definition FamilyClassConnected (E : FamClass) : Prop :=
  exists eD eL e1, 0 < e1 /\ forall eps, 0 < eps -> eps < e1 ->
    exists Fm : FamP eps, E eps Fm /\ exists K cHH eK CL x0, forall x, x0 <= x -> fWin eps Fm x ->
      ChainTied eps Fm eD eL K cHH eK CL x.

(* TopG (ZeroFreeAllOfTopG.lean) *)
Definition TopG : Prop :=
  forall la (G : FReq), 1 < la -> HostExW la (req G) ->
    (forall eps (Fm : FamP eps), cls G la eps Fm -> HypV Fm) -> FamilyClassConnected (cls G la).

(* the two statements the main line actually consumes:
   hS : forall psi, HostExW la (GChi psi).req   (from supplyChi with VWin), and
   TopG at the character requirement GChi psi.  Their conjunction yields
   ChebyshevInequalityAtWindowScale via eFamC_of_cls / hypV_of_cls. *)
Variable PChar : Type.
Variable GChi : PChar -> FReq.
Definition HostExW_main_statement (la : R) : Prop := forall psi : PChar, HostExW la (req (GChi psi)).
Definition TopG_at_main_statement (la : R) : Prop :=
  forall psi : PChar, HostExW la (req (GChi psi)) ->
    (forall eps (Fm : FamP eps), cls (GChi psi) la eps Fm -> HypV Fm) -> FamilyClassConnected (cls (GChi psi) la).
End TopStatements.

(* the statements, with their (allowlist) assumptions *)
Print Assumptions PoleData.
Print Assumptions poleData_statement.
Print Assumptions poleData_char_statement.
Print Assumptions landau_pole_asym_deriv_statement.
Print Assumptions landau_pole_asym_statement.
Print Assumptions HostExW.
Print Assumptions TopG.
Print Assumptions HostExW_main_statement.
Print Assumptions TopG_at_main_statement.
