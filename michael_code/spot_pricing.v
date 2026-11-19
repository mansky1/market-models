From stdpp Require Import gmap.
From Stdlib Require Import QArith Qround.
From MarketModels.michael_code Require Import spot_market.
Local Open Scope nat_scope.

(* A pricing rule for the spot market.

  AR(1) spot pricing model from ben-yehuda et al. 2013

     P_0 = F,  Δ_0 = 0.1 (F - C)
     Δ_i = -a1 Δ_(i-1) + ε_i,    ε_i iid with mean 0 and sd σ = k (C - F)
     P_i = P_(i-1) + Δ_i,        ε_i redrawn until P_i ∈ [F, C] and P_i ≠ P_(i-1)

   It is an example of an opaque market component whose behaviour is fitted from
   data (a1 and k).

   There is also band_step, which says anything can happen between floor and ceiling.

   Modeling choices:
   - A price is a nat, as in spot_market.v. Here it counts ticks of 0.001 of the
     on-demand price, so prices are rounded to 0.001 by construction.
   - Increments and noise are rationals, in ticks.
   - There is no probability yet*)

Record params := {
  p_floor : nat;  (* F *)
  p_ceil : nat;   (* C *)
  p_a1 : Q;       (* AR(1) coefficient *)
  p_k : Q;        (* noise scale; not used until we have probability *)
}.

(* this doesn't really matter yet but these are the feasible values.
   conceivably, tightening bounds or fixing constants is a promising form of market repair *)
Definition params_wf (θ : params) : Prop :=
  0 < θ.(p_floor) < θ.(p_ceil) ∧
  (-1 < θ.(p_a1) < 1)%Q ∧
  (0 < θ.(p_k))%Q.

(* The rule's own state: the current price and the last increment. *)
Record pstate := { p_price : nat; p_delta : Q }.

Definition qn (n : nat) : Q := inject_Z (Z.of_nat n).

Section pricing.

Variable (θ : params).
Notation F := θ.(p_floor).
Notation C := θ.(p_ceil).
Notation a1 := θ.(p_a1).

Definition p_init : pstate :=
  {| p_price := F; p_delta := ((1 # 10) * (qn F - qn C))%Q |}.

(* round to the nearest tick *)
Definition round (q : Q) : Z := Qfloor (q + (1 # 2))%Q.

(* given the source of noise, sample the next price *)
Definition ar1_step (s : pstate) (ε : Q) : option pstate :=
  let Δ := (- a1 * s.(p_delta) + ε)%Q in
  let p := (Z.of_nat s.(p_price) + round Δ)%Z in
  if decide ((Z.of_nat F ≤ p ≤ Z.of_nat C)%Z ∧ p ≠ Z.of_nat s.(p_price))
  then Some {| p_price := Z.to_nat p; p_delta := Δ |}
  else None.

(* a coarse pricing model: anything can happen between floor and ceiling *)
Definition band_step (p p' : nat) : Prop := F ≤ p' ≤ C.

(* useless result that claude proved: without probability,
   our ar1 model is the same as the coarse model *)
Lemma ar1_step_band s ε s' :
  ar1_step s ε = Some s' → band_step s.(p_price) s'.(p_price).
Proof.
  unfold ar1_step; intros Hstep.
  case_decide; simplify_eq; simpl. unfold band_step. lia.
Qed.

(* And nearly the converse, although you need an extra assumption that the price changes *)
Lemma band_ar1_step s p' :
  band_step s.(p_price) p' → p' ≠ s.(p_price) →
  ∃ ε s', ar1_step s ε = Some s' ∧ s'.(p_price) = p'.
Proof.
Admitted.

End pricing.

(* Plugging the pricing rule into slightly modified local copy of spot market
   to make it all compile *)
Section market.

Context {participant resource : Type} `{Countable resource} `{Countable participant}.
Variables (θ : params) (bid_map : gmap participant nat).
Notation state := (state participant resource).
Notation price := (price participant resource).
Notation allocation := (allocation participant resource).
Notation market_step := (market_step participant resource bid_map).
Notation bid := (bid participant bid_map).

(* the market run by the ar1 rule, for a given noise value ε *)
Definition priced_step (ε : Q) (q q' : state * pstate) : Prop :=
  ar1_step θ q.2 ε = Some q'.2 ∧ price q'.1 = q'.2.(p_price) ∧ market_step q.1 q'.1.

(* the market run by the coarse rule *)
Definition banded_step (q q' : state) : Prop :=
  band_step θ (price q) (price q') ∧ market_step q q'.

(* Anything proved about the market under the coarse rule holds under the
   fitted one. *)
Lemma priced_banded ε q q' : priced_step ε q q' → banded_step q.1 q'.1.
Proof.
  intros (Hstep%ar1_step_band & Hq' & ?). split; last done.
  unfold band_step in *. by rewrite Hq'.
Qed.

(* A first conjecture, using only the coarse rule: a participant who bids at
   least the ceiling keeps their resource. *)
Lemma ceiling_bid_kept q q' r a :
  banded_step q q' → θ.(p_ceil) ≤ bid a →
  allocation q !! r = Some (Some a) → allocation q' !! r = Some (Some a).
Proof.
Admitted.
(* claude wrote this correct proof that i don't understand *)
  (*  intros [[_ Hceil] (alloc1 & Hq' & Hold & _)] Hbid Hr.
  assert (Hkept : drop_resources _ _ bid_map (price q') (allocation q) !! r = Some (Some a)).
  { unfold drop_resources. rewrite lookup_fmap, Hr; simpl.
    destruct (Nat.leb_spec0 (price q') (bid a)); [done | lia]. }
  rewrite Hq', map_lookup_imap, Hkept; simpl.
  by rewrite (Hold _ _ Hkept).
     Qed.*)

(* a participant who bids at least the ceiling has a resource after the step, unless the market has run out.*)
Lemma ceiling_bid_served q q' r a :
  banded_step q q' → θ.(p_ceil) ≤ bid a →
  allocation q' !! r = Some None → ∃ r', allocation q' !! r' = Some (Some a).
Proof.
Admitted.
(* a proof that Rocq accepts, kept out of the way as above *)
  (*  intros [[_ Hceil] Hstep] Hbid Hr.
  assert (∃ o, allocation q !! r = Some o) as (o & Ho).
  { apply elem_of_dom. rewrite <- (market_step_dom _ _ _ _ _ Hstep).
    by apply elem_of_dom. }
  destruct Hstep as (alloc1 & Hq' & _ & _ & _ & Hfree).
  rewrite Hq', map_lookup_imap in Hr.
  unfold drop_resources in Hr, Hfree.
  rewrite lookup_fmap, Ho in Hr; simpl in Hr.
  destruct (alloc1 !! r) eqn: Hr1; simplify_eq.
  eapply (Hfree r); [done | | lia].
  rewrite lookup_fmap, Ho; simpl. by rewrite Hr.
     Qed.*)

Definition reachable (q0 q : state) : Prop := rtc banded_step q0 q.

(* if any resource is free, everyone who bids at least the ceiling has one. *)
Definition ceiling_served (q : state) : Prop :=
  ∀ r a, θ.(p_ceil) ≤ bid a → allocation q !! r = Some None →
    ∃ r', allocation q !! r' = Some (Some a).

(* if the market starts in such a state, every state it can ever reach is one too. *)
Theorem always_ceiling_served q0 q :
  ceiling_served q0 → reachable q0 q → ceiling_served q.
Proof.
  (* a claude-generated proof that i do more or less understand*)
  unfold reachable. intros Hinit Hreach.
  induction Hreach as [q1 | q1 q2 q3 Hstep _ IH]; first done.
  apply IH. intros r a ??. by eapply ceiling_bid_served.
Qed.

End market.

(* Open questions.

  1. probability. how do we model it? right now there is none, essentially anything in the support
   of the distribution "can happen". 

   3. timing. do we have one clock where allocations change and the price also changes on the same tick? *)

