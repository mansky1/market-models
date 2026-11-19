From stdpp Require Import gmap.
From Stdlib Require Import QArith Qround.
From MarketModels.michael_code Require Import spot_market.
Local Open Scope nat_scope.


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

(* pricing rule state *)
Record pstate := { p_price : nat; p_delta : Q }.

Definition qn (n : nat) : Q := inject_Z (Z.of_nat n).

(* round to the nearest tick *)
Definition round (q : Q) : Z := Qfloor (q + (1 # 2))%Q.

Section pricing.

Context {participant resource : Type} `{Countable resource} `{Countable participant}.

(* do we want this "global"? is this good practice *)
Variables (θ : params) (bid_map : gmap participant nat).

Notation F := θ.(p_floor).
Notation C := θ.(p_ceil).
Notation a1 := θ.(p_a1).
Notation state := (state participant resource).
Notation price := (price participant resource).
Notation allocation := (allocation participant resource).
Notation market_step := (market_step participant resource bid_map).
Notation bid := (bid participant bid_map).
Notation valid_state := (valid_state participant resource bid_map).

(* is market congested? -> current pricing state -> next pricing state *)
Definition pricing_rule := bool → pstate → pstate → Prop.

(* 2. band: a coarse pricing model: anything can happen between floor and ceiling *)
Definition band_rule : pricing_rule := λ _ _ s', F ≤ s'.(p_price) ≤ C.


(* 1. ar1: given the source of noise, sample the next price *)

(* 

  AR(1) spot pricing model from ben-yehuda et al. 2013

     P_0 = F,  Δ_0 = 0.1 (F - C)
     Δ_i = -a1 Δ_(i-1) + ε_i,    ε_i iid with mean 0 and sd σ = k (C - F)
     P_i = P_(i-1) + Δ_i,        ε_i redrawn until P_i ∈ [F, C] and P_i ≠ P_(i-1)

   It is an example of an opaque market component whose behaviour is fitted from
   data (a1 and k). *)

Definition p_init : pstate :=
  {| p_price := F; p_delta := ((1 # 10) * (qn F - qn C))%Q |}.

Definition ar1_step (s : pstate) (ε : Q) : option pstate :=
  let Δ := (- a1 * s.(p_delta) + ε)%Q in
  let p := (Z.of_nat s.(p_price) + round Δ)%Z in
  if decide ((Z.of_nat F ≤ p ≤ Z.of_nat C)%Z ∧ p ≠ Z.of_nat s.(p_price))
  then Some {| p_price := Z.to_nat p; p_delta := Δ |}
  else None.

Definition ar1_rule (ε : Q) : pricing_rule := λ _ s s', ar1_step s ε = Some s'.


(* 3. thermostat: tick the price up when congested, down when not,
   clamped to [F, C]. *)
Definition thermostat (congested : bool) (p : nat) : nat :=
  if congested then min C (S p) else max F (p - 1).

Definition thermo_rule : pricing_rule := λ c s s', s'.(p_price) = thermostat c s.(p_price).

(* applying rules in markets *)

(* congested means no resource is free *)
Definition congested (q : state) : bool :=
  bool_decide (map_Forall (λ _ o, is_Some o) (allocation q)).

(* the market price and the rule's price agree *)
(* how important this this? good design choice? *)
Definition synced (q : state * pstate) : Prop := price q.1 = q.2.(p_price).


Definition priced_step (R : pricing_rule) (q q' : state * pstate) : Prop :=
  synced q ∧ R (congested q.1) q.2 q'.2 ∧ synced q' ∧ market_step q.1 q'.1.

(* conjectured properties *)

(* useless result that claude proved: without probability,
   our ar1 model is the same as the coarse model *)
Lemma ar1_band ε c s s' : ar1_rule ε c s s' → band_rule c s s'.
Proof.
  unfold ar1_rule, ar1_step; intros Hstep.
  case_decide; simplify_eq; simpl. unfold band_rule; simpl. lia.
Qed.

(* And nearly the converse, although you need an extra assumption that the price changes *)
Lemma band_ar1 c s s' :
  band_rule c s s' → s'.(p_price) ≠ s.(p_price) →
  ∃ ε s'', ar1_rule ε c s s'' ∧ s''.(p_price) = s'.(p_price).
Proof.
Admitted.

(* similar for thermostat and coarse band *)
Lemma thermo_band c s s' :
  F ≤ s.(p_price) ≤ C → thermo_rule c s s' → band_rule c s s'.
Proof. unfold band_rule, thermo_rule, thermostat. destruct c; lia. Qed.

(* if every move of R is a move of R', the market under R is a market under R' *)
Lemma priced_step_impl (R R' : pricing_rule) q q' :
  (∀ c s s', R c s s' → R' c s s') → priced_step R q q' → priced_step R' q q'.
Proof. intros HR (? & ? & ? & ?). split_and!; auto. Qed.

(* Anything proved about the market under the coarse rule holds under the
   ar1 rule. *)
Lemma ar1_market_band ε q q' :
  priced_step (ar1_rule ε) q q' → priced_step band_rule q q'.
Proof. apply priced_step_impl, ar1_band. Qed.

(* another slightly useless theorem *)
(* assuming thermostat respects the same floor and ceiling, every thermostat price adjustment could have been made by the coarse *)
Lemma thermo_market_band q q' :
  F ≤ price q.1 ≤ C → priced_step thermo_rule q q' → priced_step band_rule q q'.
Proof.
  intros ? (Hq & ? & ? & ?). split_and!; try done.
  eapply thermo_band; last done. by rewrite <- Hq.
Qed.

(** * Properties of the market under the coarse rule *)

(* a participant who bids higher than the ceiling will never lose resource *)
Lemma ceiling_bid_kept q q' r a :
  priced_step band_rule q q' → C ≤ bid a →
  allocation q.1 !! r = Some (Some a) → allocation q'.1 !! r = Some (Some a).
Proof.
Admitted.
(* claude wrote this correct proof that i don't understand *)
  (*  intros (_ & [_ Hceil] & Hsync & Hstep) Hbid Hr.
  rewrite <- Hsync in Hceil.
  (* buying never takes a resource from its holder, so it is enough that
     a survives the drop phase *)
  eapply buy_maintains; first done.
  unfold drop_resources. rewrite lookup_fmap, Hr; simpl.
  destruct (Nat.leb_spec0 (price q'.1) (bid a)); [done | lia].
     Qed.*)

(* a participant who bids at least the ceiling has a resource after the step, unless the market has run out.*)
Lemma ceiling_bid_served q q' r a :
  priced_step band_rule q q' → C ≤ bid a →
  allocation q'.1 !! r = Some None → ∃ r', allocation q'.1 !! r' = Some (Some a).
Proof.
Admitted.
(* a proof that Rocq accepts, kept out of the way as above --claude*)
  (*  intros (_ & [_ Hceil] & Hsync & Hstep) Hbid Hr.
  rewrite <- Hsync in Hceil.
  (* a resource free after buying was free before *)
  pose proof (buy_unused _ _ _ _ _ _ Hstep _ Hr) as Hr0.
  destruct Hstep as (alloc1 & Hq' & _ & _ & _ & Hfree).
  rewrite Hq', map_lookup_imap, Hr0 in Hr; simpl in Hr.
  destruct (alloc1 !! r) eqn: Hr1; simplify_eq.
  eapply (Hfree r); [done | done | lia].
     Qed.*)

Definition reachable (q0 q : state * pstate) : Prop := rtc (priced_step band_rule) q0 q.

(* if any resource is free, everyone with a bid at least the ceiling has one. *)
Definition ceiling_served (q : state) : Prop :=
  ∀ r a, C ≤ bid a → allocation q !! r = Some None →
    ∃ r', allocation q !! r' = Some (Some a).

(* if the market starts in a valid state with the price at most the ceiling,
   every state it can ever reach is ceiling_served.
   validity is the invariant (valid_inv, from spot_market.v) *)
Theorem always_ceiling_served q0 q :
  valid_state q0.1 → price q0.1 ≤ C → reachable q0 q → ceiling_served q.1.
Proof.
  unfold reachable. intros Hvalid Hle Hreach.
  assert (valid_state q.1 ∧ price q.1 ≤ C) as [[_ Hfree] ?].
  { induction Hreach as [q1 | q1 q2 q3 Hstep _ IH]; first done.
    destruct Hstep as (_ & [_ Hceil] & Hsync & Hstep).
    apply IH; [by eapply valid_inv | unfold synced in Hsync; lia]. }
  intros r a ? Hr. eapply Hfree; [done | lia].
Qed.


(* example: a conjecture that doesn't hold on the coarse rule (or ar1 until we define probability)
but does hold on the thermostat *)

(* first, a deliberately naive version of this conjecture,
where the market that has no resources is a trivial counterexample *)

Definition congested_no_fall_naive (R : pricing_rule) : Prop :=
  ∀ q q', price q.1 ≤ C → congested q.1 = true →
    priced_step R q q' → price q.1 ≤ price q'.1.

(* v0 holds for the thermostat *)
Theorem thermo_congested_no_fall_naive : congested_no_fall_naive thermo_rule.
Proof.
  intros q q' ? Hc (Hq & HR & Hq' & _).
  unfold synced, thermo_rule, thermostat in *. rewrite Hc in HR. lia.
Qed.

(* counterexample is the market with no resources, which is (vacuously) congested.
   ar1 and coarse rules may lower the price*)
Lemma congested_fall_refutes_naive (R : pricing_rule) s s' :
  s'.(p_price) < s.(p_price) ≤ C → R true s s' → ¬ congested_no_fall_naive R.
Admitted. (*another claude proof I won't pretend to understand *)
(*Proof.
  intros ? HR Hprop.
  specialize (Hprop (Build_state participant resource ∅ s.(p_price), s)
                    (Build_state participant resource ∅ s'.(p_price), s')).
  simpl in Hprop. enough (s.(p_price) ≤ s'.(p_price)) by lia.
  apply Hprop; [lia | by apply bool_decide_eq_true_2, map_Forall_empty |].
  split_and!; [done | done | done |].
  unfold spot_market.market_step, drop_resources; simpl. rewrite fmap_empty.
  exists ∅. split_and!; [by rewrite map_imap_empty | intros; simplify_map_eq..].
Qed.*)

(* v0 fails for the coarse rule: it may drop from the ceiling straight to the floor *)
Theorem band_not_congested_no_fall_naive : F < C → ¬ congested_no_fall_naive band_rule.
Proof.
  intros ?.
  apply (congested_fall_refutes_naive _ {| p_price := C; p_delta := 0 |}
                                        {| p_price := F; p_delta := 0 |}); simpl; first lia.
  unfold band_rule; simpl; lia.
Qed.

(* ar1 can tick down from the ceiling, whatever the congestion signal *)
Lemma ar1_tick_down c :
  F < C → ar1_rule (-1) c {| p_price := C; p_delta := 0 |}
                          {| p_price := C - 1; p_delta := (- a1 * 0 + -1)%Q |}.
Proof.
  intros ?. unfold ar1_rule, ar1_step; simpl.
  assert (round (- a1 * 0 + -1) = (-1)%Z) as ->.
  { unfold round. transitivity (Qfloor (-1 # 2)); last done.
    apply Qfloor_comp. ring. }
  case_decide; last lia. do 2 f_equal. lia.
Qed.

(* v0 fails for ar1 too: it ignores congestion, so negative noise lowers the price *)
Theorem ar1_not_congested_no_fall_naive : F < C → ¬ congested_no_fall_naive (ar1_rule (-1)).
Proof.
  intros ?. eapply congested_fall_refutes_naive; last by apply ar1_tick_down.
  simpl; lia.
Qed.

(** ** Conjecture v1: refined

   Adds the assumption that the market has at least one resource, so that
   congestion is no longer vacuous. *)
   
   
Definition congested_no_fall (R : pricing_rule) : Prop :=
  ∀ q q', price q.1 ≤ C → allocation q.1 ≠ ∅ → congested q.1 = true →
    priced_step R q q' → price q.1 ≤ price q'.1.

(* v1 only adds an assumption, so anything satisfying v0 satisfies v1 *)
Lemma congested_no_fall_naive_refined R :
  congested_no_fall_naive R → congested_no_fall R.
Proof. intros HR q q' ? _. by apply HR. Qed.

(* v1 holds for the thermostat *)
Theorem thermo_congested_no_fall : congested_no_fall thermo_rule.
Proof. apply congested_no_fall_naive_refined, thermo_congested_no_fall_naive. Qed.

(* v1: any rule that can lower the price on a congestion signal still fails,
   provided a participant and a resource exist. counterexample is now a market
   with one resource, held by someone *)
Lemma congested_fall_refutes (R : pricing_rule) (a : participant) (r : resource) s s' :
  0 < s'.(p_price) < s.(p_price) → s.(p_price) ≤ C → R true s s' →
  ¬ congested_no_fall R.
Admitted. (* i particularly don't understand this one lmao *)
(*Proof.
  intros [? ?] ? HR Hprop.
  (* one resource, held by a *)
  set (alloc := {[r := Some a]} : gmap resource (option participant)).
  (* buy_exists: at a non-zero price the market can always take a step *)
  destruct (buy_exists participant resource bid_map s'.(p_price)
              (drop_resources participant resource bid_map s'.(p_price) alloc))
    as [alloc' Hbuy]; first lia.
  assert (congested (Build_state participant resource alloc s.(p_price)) = true) as Hc.
  { apply bool_decide_eq_true_2, map_Forall_singleton. eauto. }
  specialize (Hprop (Build_state participant resource alloc s.(p_price), s)
                    (Build_state participant resource alloc' s'.(p_price), s')).
  simpl in Hprop. enough (s.(p_price) ≤ s'.(p_price)) by lia.
  apply Hprop; [lia | apply map_non_empty_singleton | done |].
  split_and!; [done | by simpl; rewrite Hc | done | done].
Qed.*)

(* v1 fails for the coarse rule *)
Theorem band_not_congested_no_fall (a : participant) (r : resource) :
  0 < F < C → ¬ congested_no_fall band_rule.
Proof.
  intros ?.
  apply (congested_fall_refutes _ a r {| p_price := C; p_delta := 0 |}
                                      {| p_price := F; p_delta := 0 |}); simpl; [lia..|].
  unfold band_rule; simpl; lia.
Qed.

(* v1 fails for ar1 *)
Theorem ar1_not_congested_no_fall (a : participant) (r : resource) :
  0 < F < C → ¬ congested_no_fall (ar1_rule (-1)).
Proof.
  intros ?. eapply (congested_fall_refutes _ a r); last (apply ar1_tick_down; lia).
  all: simpl; lia.
Qed.

End pricing.

(* Open questions.

  1. probability. how do we model it? right now there is none, essentially anything in the support
   of the distribution "can happen". 

   3. timing. do we have one clock where allocations change and the price also changes on the same tick? currently this is assumption.*)

