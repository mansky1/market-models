From stdpp Require Import gmap finite.

(* STUB (Michael): compatibility with stdpp 1.12. Upstream is written against a
   newer stdpp, where lookup_insert is the decide form and the old lemma is
   lookup_insert_eq. These shadow stdpp's names in this file only (Import, not
   Export), and are harmless on newer stdpp. Delete once stdpp is upgraded. *)
Module StdppCompat.
  Lemma lookup_insert_eq {K M} `{FinMap K M} {A} (m : M A) i x : <[i:=x]>m !! i = Some x.
  Proof. apply stdpp.fin_maps.lookup_insert. Qed.
  Lemma lookup_insert {K M} `{FinMap K M} {A} (m : M A) i j x :
    <[i:=x]>m !! j = if decide (i = j) then Some x else m !! j.
  Proof.
    destruct (decide (i = j)) as [->|];
      [apply stdpp.fin_maps.lookup_insert | by apply lookup_insert_ne].
  Qed.
End StdppCompat.
Import StdppCompat.

Section spot_market.

Variables (participant resource : Type).

Context `{Countable resource} `{Countable participant}.
Record state := { allocation : gmap resource (option participant); price : nat }.
(* A resource mapped to Some a belongs to participant a;
   a resource mapped to None exists but is unallocated;
   a resource that isn't in the domain of the map isn't available to be allocated (yet).
   *)
(* single uniform price for all resources *)

Section big_step.

(* Each participant has a price they're willing to pay. For now, we assume that
   this is constant. *)
Variable (bid_map : gmap participant nat).
Definition bid a := match bid_map !! a with Some n => n | _ => 0 end.

Definition drop_resources pr (alloc : gmap resource (option participant)) :=
  (λ o, match o with Some a => if pr <=? bid a then Some a else None
                   | None => None end) <$> alloc.

Definition buy_resources pr (alloc alloc' : gmap resource (option participant)) : Prop :=
  ∃ alloc1 : gmap resource participant,
    (* alloc' is obtained by adding new mappings alloc1 to alloc *)
    alloc' = map_imap (λ r o, match alloc1 !! r with Some a => Some (Some a) | _ => Some o end) alloc ∧
    (forall r a, alloc !! r = Some (Some a) → alloc1 !! r = None) ∧
    (* only assign resources to participants who don't already have one *)
    (∀ r a, alloc1 !! r = Some a → ∀ r', alloc !! r' ≠ Some (Some a)) ∧
    (* only assign resources to participants who want to pay for them *)
    (∀ r a, alloc1 !! r = Some a → pr ≤ bid a) ∧
    (* don't leave any resources unassigned if someone wants to buy them *)
    (∀ r, alloc1 !! r = None → alloc !! r = Some None →
          (∀ a, pr ≤ bid a → ∃ r', alloc' !! r' = Some (Some a))).

Definition market_step (q q' : state) : Prop :=
  buy_resources q'.(price) (drop_resources q'.(price) q.(allocation)) q'.(allocation).

Definition used_resources (a : gmap resource (option participant)) :=
  dom (filter (λ '(_, o), o ≠ None) a).

Lemma drop_decreases : ∀ pr a, used_resources (drop_resources pr a) ⊆ used_resources a.
Proof.
  intros; unfold used_resources, drop_resources.
  intros r (? & Hdrop)%elem_of_dom.
  apply map_lookup_filter_Some in Hdrop as (Hdrop & ?).
  apply lookup_fmap_Some in Hdrop as (o & <- & ?).
  destruct o; last done.
  rewrite elem_of_dom.
  exists (Some p).
  rewrite map_lookup_filter_Some; auto.
Qed.

Lemma drop_none : ∀ pr alloc (Hover : ∀ r a, alloc !! r = Some (Some a) → pr ≤ bid a),
  drop_resources pr alloc = alloc.
Proof.
  intros; apply map_eq; intros.
  unfold drop_resources; rewrite lookup_fmap.
  destruct (alloc !! i) eqn: Hi; last done; simpl.
  destruct o; last done.
  destruct (Nat.leb_spec0 pr (bid p)); first done.
  contradiction n; by eapply Hover.
Qed.

Lemma buy_unused : ∀ pr alloc alloc' (Hbuy : buy_resources pr alloc alloc'),
  ∀ r, alloc' !! r = Some None → alloc !! r = Some None.
Proof.
  intros ??? (? & -> & _) ?.
  rewrite map_lookup_imap.
  destruct (alloc !! r) eqn: Hr; try done; simpl.
  destruct (x !! r); by inversion 1.
Qed.

Lemma buy_maintains : ∀ pr alloc alloc' (Hbuy : buy_resources pr alloc alloc'),
  ∀ r a, alloc !! r = Some (Some a) → alloc' !! r = Some (Some a).
Proof.
  intros ??? (? & -> & Hconds) ?? Hr.
  rewrite map_lookup_imap, Hr; simpl.
  destruct Hconds as (Hcond & _); erewrite Hcond; eauto.
Qed.

Lemma imap_dom : ∀ (A : gmap resource (option participant)) (B : gmap resource participant),
  dom (map_imap (λ r o, match B !! r with Some a => Some (Some a) | _ => Some o end) A) = dom A.
Proof.
  intros.
  apply dom_imap_L.
  intros; rewrite elem_of_dom; split.
  - intros (? & ?); eexists; split; first done.
    by destruct (B !! i).
  - by intros (? & ? & ?).
Qed.

Lemma market_step_dom : ∀ q q' (Hstep : market_step q q'), dom q'.(allocation) = dom q.(allocation).
Proof.
  intros ?? (? & -> & Hunion & ?).
  rewrite imap_dom.
  unfold drop_resources.
  apply dom_fmap_L.
Qed.

Definition valid_state (q : state) :=
  (* allocated resources are allocated to buyers who want to pay for them *)
  (∀ r a, q.(allocation) !! r = Some (Some a) → q.(price) ≤ bid a) ∧
  (* if a resource is unallocated, no one wanted to buy it *)
  (∀ r, q.(allocation) !! r = Some None → ∀ a, q.(price) ≤ bid a →
    ∃ r', q.(allocation) !! r' = Some (Some a)).

Lemma valid_inv : ∀ q q' (Hvalid : valid_state q) (Hstep : market_step q q'), valid_state q'.
Proof.
  intros; split.
  - destruct Hstep as (alloc' & -> & Hconds).
    intros ??; rewrite map_lookup_imap.
    unfold drop_resources; rewrite lookup_fmap.
    destruct (q.(allocation) !! r) eqn: Hr; last done; simpl.
    destruct (alloc' !! r) eqn: Hr'.
    + inversion 1; subst.
      destruct Hconds as (_ & _ & Hprice & _); eauto.
    + destruct o; inversion 1.
      destruct (Nat.leb_spec0 q'.(price) (bid p)); by inv H3.
  - unfold valid_state; intros r Hr ? Hbid.
    assert (∃ o, q.(allocation) !! r = Some o) as (o & Ho).
    { apply elem_of_dom.
      rewrite <- (market_step_dom _ _ Hstep).
      by apply elem_of_dom. }
    destruct Hstep as (alloc' & Hq' & Hconds).
    rewrite Hq', map_lookup_imap in Hr.
    unfold drop_resources in *.
    rewrite lookup_fmap, Ho in Hr; simpl in Hr.
    destruct (alloc' !! r) eqn: Ho'; inv Hr.
    destruct Hconds as (? & ? & ? & HNone); eapply HNone in Ho'; eauto.
    rewrite lookup_fmap, Ho; simpl.
    destruct o; last done.
    by destruct (Nat.leb_spec0 q'.(price) (bid p)).
Qed.

Theorem monotonic_increasing : ∀ q q' (Hvalid : valid_state q) (Hstep : market_step q q')
    (Hincr : q.(price) ≤ q'.(price)), used_resources q'.(allocation) ⊆ used_resources q.(allocation).
Proof.
  intros; unfold used_resources.
  intros r (x & Hdrop)%elem_of_dom.
  apply map_lookup_filter_Some in Hdrop as (Hdrop & ?).
  destruct x as [a|]; last done.
  rewrite elem_of_dom.
  unfold is_Some.
  setoid_rewrite map_lookup_filter_Some.
  assert (∃ o, allocation q !! r = Some o) as (o & Ho).
  { apply elem_of_dom.
    rewrite <- (market_step_dom _ _ Hstep).
    by apply elem_of_dom. }
  exists o; split; first done.
  intros ->.
  pose proof ((proj2 Hvalid) _ Ho) as Hfull.
  destruct Hstep as (alloc' & Hq' & Hconds).
  rewrite Hq' in Hdrop.
  unfold drop_resources in *; rewrite map_lookup_imap, lookup_fmap, Ho in Hdrop; simpl in Hdrop.
  destruct (alloc' !! r) eqn: Ho'; inv Hdrop.
  destruct Hconds as (_ & Hunused & Hprice & _).
  specialize (Hprice _ _ Ho').
  destruct (Hfull a ltac:(lia)) as (r0 & Ha).
  eapply Hunused in Ho'.
  rewrite lookup_fmap, Ha in Ho'; simpl in Ho'.
  by destruct (Nat.leb_spec0 q'.(price) (bid a)).
Qed.

Definition alloc_incl : relation (gmap resource (option participant)) :=
  map_included (λ _ a b, match a with None => True | _ => a = b end).

Theorem monotonic_decreasing : ∀ q q' (Hvalid : valid_state q) (Hstep : market_step q q')
    (Hincr : q'.(price) ≤ q.(price)), alloc_incl q.(allocation) q'.(allocation).
Proof.
  intros ??????.
  pose proof (market_step_dom _ _ Hstep) as Hdom.
  unfold market_step in Hstep.
  rewrite drop_none in Hstep.
  2: { intros ???%Hvalid; lia. }
  destruct (q.(allocation) !! i) eqn: Hq, (q'.(allocation) !! i) eqn: Hq'; try done; simpl.
  2: { rewrite <- not_elem_of_dom, Hdom, not_elem_of_dom in Hq'; congruence. }
  destruct o; last done.
  eapply buy_maintains in Hstep; last done.
  congruence.
Qed.

End big_step.

(* buy is nondeterministic but always possible *)
Theorem buy_exists : ∀ bid_map pr alloc, pr ≠ 0 → ∃ alloc', buy_resources bid_map pr alloc alloc'.
Proof.
  intros.
  induction bid_map using map_ind.
  - exists alloc, ∅; repeat split; try done.
    + apply map_eq; intros; rewrite map_lookup_imap, lookup_empty.
      by destruct (alloc !! i).
    + intros ????.
      unfold bid; rewrite lookup_empty; lia.
  - destruct IHbid_map as (alloc' & Hbuy).
    destruct (decide (pr ≤ x)).    
    + (* if i needs a resource and r is still available, exists <[r := Some i]>alloc',
         else exists alloc' *)
      destruct (decide (map_Exists (λ _ s, s = Some i) alloc)) as [(r & ? & Hr & ->) | Hneed]; last
        destruct (decide (map_Exists (λ _ s, s = None) alloc')) as [(r & ? & Hr & ->) | Hfull].
      * exists alloc'.
        pose proof (buy_maintains _ _ _ _ Hbuy _ _ Hr) as Hr'.
        destruct Hbuy as (alloc1 & Hbuy); exists alloc1.
        destruct Hbuy as (? & ? & ? & Hprice & ?); repeat split; try done.
        -- intros ?? Hbid%Hprice.
           unfold bid in *.
           rewrite lookup_insert_ne; try done.
           intros <-; rewrite H2 in Hbid; lia.
        -- intros ????.
           unfold bid; rewrite lookup_insert.
           destruct (decide (i = a)); subst; eauto.
      * pose proof (buy_unused _ _ _ _ Hbuy) as Hunused.
        pose proof (Hunused _ Hr) as Hr_none.
        exists (<[r := Some i]>alloc').
        destruct Hbuy as (alloc1 & Hbuy); exists (<[r := i]>alloc1).
        destruct Hbuy as (Heq & ? & ? & Hprice & Hfull); repeat split; try done.
        -- apply map_eq; intros r0.
           rewrite map_lookup_imap.
           rewrite !lookup_insert; destruct (decide (r = r0)) as [<- |]; first by rewrite Hr_none.
           by rewrite Heq, map_lookup_imap.
        -- intros r0 ?; rewrite lookup_insert.
           destruct (decide (r = r0)) as [<- |]; first by rewrite Hr_none.
           eauto.
        -- intros r0 ?; rewrite lookup_insert.
           destruct (decide (r = r0)) as [<- |]; last eauto.
           inversion 1; subst.
           apply map_not_Exists in Hneed.
           by intros ? Ha; apply Hneed in Ha.
        -- unfold bid; intros ?? Halloc.
           rewrite lookup_insert; destruct (decide (i = a)); first done.
           rewrite lookup_insert in Halloc; destruct (decide (r = r0)); first by inv Halloc.
           eauto.
        -- unfold bid; intros ? Hr1 Hr0 ??.
           rewrite !lookup_insert in *.
           destruct (decide (i = a)) as [-> |].
           { eexists; apply lookup_insert_eq. }
           destruct (decide (r = r0)); first done.
           eapply Hfull in Hr0 as (? & ?); [|eauto..].
           eexists; rewrite lookup_insert_ne; eauto; congruence.
      * exists alloc'.
        destruct Hbuy as (alloc1 & Hbuy); exists alloc1.
        destruct Hbuy as (? & ? & ? & Hprice & ?); repeat split; try done.
        -- intros ?? Hbid%Hprice.
           unfold bid in *.
           rewrite lookup_insert_ne; try done.
           intros <-; rewrite H2 in Hbid; lia.
        -- apply map_not_Exists in Hfull.
           intros ? Hr1 Hr; specialize (Hfull r None); subst.
           rewrite map_lookup_imap, Hr, Hr1 in Hfull; simpl in Hfull.
           by specialize (Hfull eq_refl).
    + exists alloc'.
      (* participant i doesn't want to buy at this price, so is irrelevant to
         this step *)
      destruct Hbuy as (alloc1 & Hbuy); exists alloc1.
      destruct Hbuy as (? & ? & ? & Hprice & Hfull); repeat split; try done.
      * intros ?? Hbid%Hprice.
        unfold bid in *.
        rewrite lookup_insert_ne; try done.
        intros <-; rewrite H2 in Hbid; lia.
      * intros ???? Ha; eapply Hfull; eauto.
        unfold bid in *.
        rewrite lookup_insert in Ha; destruct (decide (i = a)); [lia | done].
Qed.

(* make up a bad pricing strategy, show how our system would catch and fix it *)
(* Interesting extensions/refinements:
    1. pricing strategies, possibly including NN-determined ones
    2. concurrency/distributed-systems conflicts in the market implementation
    3. lag between price change notification, user choices, and actual price change; shutdown and startup time
    4. concurrency issues at the market level
    5. downtime and minimum occupancy periods *)
(*  6. non-unit demand, resources need to be contiguous *)

Section event_lag.

Inductive resource_state := Unused | Starting (a : participant) | Used (a : participant).

Definition user_of rs := match rs with Unused => None | Starting a | Used a => Some a end.

Record l_state := { l_allocation : gmap resource resource_state; l_price : nat;
  l_incoming_price : option nat }.

Variable (bid_map : gmap participant nat).
Notation bid := (bid bid_map).

(* The price can only change to a previously announced incoming price. *)
Definition price_step (q q' : l_state) :=
  match q.(l_incoming_price) with
  | Some pr => q'.(l_incoming_price) = None ∧ q'.(l_price) = pr
  | None => q'.(l_price) = q.(l_price)
  end.

Definition l_drop_resources pr (alloc : gmap resource resource_state) :=
  match pr with None => alloc
  | Some pr =>
    (λ s, match user_of s with Some a => if pr <=? bid a then s else Unused
                             | None => Unused end) <$> alloc end.

Definition l_start_resources (alloc : gmap resource resource_state) :=
  (λ s, match s with Starting a => Used a | _ => s end) <$> alloc.

Definition l_buy_resources pr (alloc alloc' : gmap resource resource_state) : Prop :=
  ∃ alloc1 : gmap resource participant,
    (* alloc' is obtained by adding new mappings alloc1 to alloc *)
    alloc' = map_imap (λ r s, match alloc1 !! r with Some a => Some (Starting a) | _ => Some s end) alloc ∧
    (forall r, alloc !! r ≠ Some Unused → alloc1 !! r = None) ∧
    (* only assign resources to participants who don't already have one *)
    (∀ r a, alloc1 !! r = Some a → ∀ r' s', alloc !! r' = Some s' → user_of s' ≠ Some a) ∧
    (* only assign resources to participants who want to pay for them *)
    (∀ r a, alloc1 !! r = Some a → pr ≤ bid a) ∧
    (* don't leave any resources unassigned if someone wants to buy them *)
    (∀ r, alloc1 !! r = None → alloc !! r = Some Unused →
          (∀ a, pr ≤ bid a → ∃ r' s', alloc' !! r' = Some s' ∧ user_of s' = Some a)).

(* 1. Seller either announces a new price or implements the announced price.
   2. Participants drop based on the new announced price, if any.
   3. Resources in the Starting state move to the Used state.
   4. Participants without a resource buy the available resources at the current price. *)
Definition l_market_step (q q' : l_state) : Prop :=
  price_step q q' ∧
  l_buy_resources q'.(l_price) (l_start_resources
    (l_drop_resources q'.(l_incoming_price) q.(l_allocation))) q'.(l_allocation).

End event_lag.

(* same model except participants can enter, leave, and change their bids arbitrarily *)
Section event_lag2.

Record l2_state := { l2_allocation : gmap resource resource_state; l2_price : nat;
  l2_incoming_price : option nat; l2_bid_map : gmap participant nat }.

(* The price can only change to a previously announced incoming price. *)
Definition l2_price_step (q q' : l2_state) :=
  match q.(l2_incoming_price) with
  | Some pr => q'.(l2_incoming_price) = None ∧ q'.(l2_price) = pr
  | None => q'.(l2_price) = q.(l2_price)
  end.

Definition l2_drop_resources bid_map pr (alloc : gmap resource resource_state) :=
  match pr with None => alloc
  | Some pr =>
    (λ s, match user_of s with Some a => if pr <=? bid bid_map a then s else Unused
                             | None => Unused end) <$> alloc end.

Definition l2_buy_resources bid_map pr (alloc alloc' : gmap resource resource_state) : Prop :=
  ∃ alloc1 : gmap resource participant,
    (* alloc' is obtained by adding new mappings alloc1 to alloc *)
    alloc' = map_imap (λ r s, match alloc1 !! r with Some a => Some (Starting a) | _ => Some s end) alloc ∧
    (forall r, alloc !! r ≠ Some Unused → alloc1 !! r = None) ∧
    (* only assign resources to participants who don't already have one *)
    (∀ r a, alloc1 !! r = Some a → ∀ r' s', alloc !! r' = Some s' → user_of s' ≠ Some a) ∧
    (* only assign resources to participants who want to pay for them *)
    (∀ r a, alloc1 !! r = Some a → pr ≤ bid bid_map a) ∧
    (* don't leave any resources unassigned if someone wants to buy them *)
    (∀ r, alloc1 !! r = None → alloc !! r = Some Unused →
          (∀ a, pr ≤ bid bid_map a → ∃ r' s', alloc' !! r' = Some s' ∧ user_of s' = Some a)).

(* 1. Seller either announces a new price or implements the announced price.
   2. Participants drop based on the new announced price, if any.
   3. Resources in the Starting state move to the Used state.
   4. Participants without a resource buy the available resources at the current price. *)
Definition l2_market_step (q q' : l2_state) : Prop :=
  l2_price_step q q' ∧
  l2_buy_resources q'.(l2_bid_map) q'.(l2_price) (l_start_resources
    (l2_drop_resources q'.(l2_bid_map) q'.(l2_incoming_price) q.(l2_allocation))) q'.(l2_allocation).

End event_lag2.

Section small_step.

(* Does it make sense to model this happening step by step, or is it that
   the seller changes the price and then everyone reacts at once? *)
(* STUB (Michael): renamed from market_step, which clashes with big_step's;
   allocation values wrapped in Some to match the option participant map. *)
Inductive small_market_step (q q' : state) : Prop :=
| change_price (same_alloc : q'.(allocation) = q.(allocation)):
    small_market_step q q'
    (* Do priced-out participants drop right away, or does it take a step? *)
| subscribe (a : participant) (r : resource)
    (r_unused : q.(allocation) !! r = None)
    (use_r : q'.(allocation) = <[r := Some a]>(q.(allocation)))
    (same_price : q'.(price) = q.(price)) :
    small_market_step q q'
    (* Is it important that multiple participants be able to act simultaneously? *)
| unsubscribe (a : participant) (a : participant) (r : resource)
    (r_used_by_a : q.(allocation) !! r = Some (Some a))
    (drop_r : q'.(allocation) = delete r q.(allocation))
    (same_price : q'.(price) = q.(price)) :
    small_market_step q q'.

End small_step.

End spot_market.