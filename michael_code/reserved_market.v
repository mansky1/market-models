From stdpp Require Import gmap finite.

(* A spot market with an added market for reserved blocks of capacity.

   This file is self-contained, but is shaped to match spot_market.v: the
   [allocation] and [price] fields, [bid], [buy_resources] and [used_resources]
   are the same as there, and [drop_resources] differs only in skipping reserved
   resources. *)

Section reserved_market.

Variables (participant resource : Type).

Context `{Countable resource} `{Countable participant}.

(* A block of reserved capacity. A block bought at time t for K steps has
   b_end = t + K: it is in force in the states at times t, ..., t + K - 1.
   b_rate is the per-step reservation price at the time of purchase, which the
   holder pays for the whole block regardless of later price changes. *)
Record block := { b_end : nat; b_rate : nat }.

Record state := {
  allocation : gmap resource (option participant);
  price : nat;
  reserved : gmap resource block;
  r_price : nat;
  time : nat }.
(* allocation and price are as in the spot market:
   a resource mapped to Some a belongs to participant a;
   a resource mapped to None exists but is unallocated;
   a resource that isn't in the domain of the map isn't available to be allocated (yet).

   A resource in the domain of reserved is held under a block; any other
   allocated resource is held on the spot market.
   r_price is the per-step price of a block bought now. *)
(* single uniform spot price and single uniform reservation price for all resources *)

Section big_step.

(* Each participant has a price they're willing to pay on the spot market. For
   now, we assume that this is constant. *)
Variable (bid_map : gmap participant nat).
Definition bid a := match bid_map !! a with Some n => n | _ => 0 end.

(* Each participant may also have a per-step price they're willing to pay for
   reserved capacity, and a fixed length of block that they want. A participant
   who isn't in the map never reserves. *)
Variable (r_bid_map : gmap participant (nat * nat)).
Definition r_len a := match r_bid_map !! a with Some (_, K) => K | _ => 0 end.

Definition wants_block pr a : Prop :=
  ∃ b K, r_bid_map !! a = Some (b, K) ∧ pr ≤ b ∧ 0 < K.

(* participant a holds some resource under a block *)
Definition holds_block (alloc : gmap resource (option participant))
    (res : gmap resource block) a : Prop :=
  ∃ r, is_Some (res !! r) ∧ alloc !! r = Some (Some a).

(* Blocks that have reached their end time lapse. The holder keeps the resource,
   but now holds it on the spot market. *)
Definition expire_blocks t (res : gmap resource block) :=
  filter (λ '(_, b), t < b.(b_end)) res.

(* As in the spot market, except that holders of reserved resources are not
   affected by the spot price. *)
Definition drop_resources pr (res : gmap resource block)
    (alloc : gmap resource (option participant)) :=
  map_imap (λ r o, Some (
    match res !! r with
    | Some _ => o
    | None => match o with Some a => if pr <=? bid a then Some a else None
                         | None => None end
    end)) alloc.

(* Participants buy blocks starting at the current time t, at per-step price pr.
   A block can be bought on any resource that isn't already reserved, including
   one that someone holds on the spot market, who then loses it. *)
Definition reserve_blocks pr t (alloc : gmap resource (option participant))
    (res : gmap resource block) (alloc' : gmap resource (option participant))
    (res' : gmap resource block) : Prop :=
  ∃ res1 : gmap resource participant,
    let buyers : gset participant := map_img res1 in
    (* res' is obtained by adding blocks for the new mappings res1 to res *)
    res' = ((λ a, {| b_end := t + r_len a; b_rate := pr |}) <$> res1) ∪ res ∧
    (* alloc' gives each newly reserved resource to its buyer, and releases any
       resource that a buyer held on the spot market *)
    alloc' = map_imap (λ r o,
      match res1 !! r with
      | Some a => Some (Some a)
      | None => match o with
                | Some a => if decide (a ∈ buyers) then Some None else Some o
                | None => Some o
                end
      end) alloc ∧
    (* only reserve resources that exist and aren't already reserved *)
    (∀ r a, res1 !! r = Some a → is_Some (alloc !! r) ∧ res !! r = None) ∧
    (* each participant buys at most one block *)
    (∀ r r' a, res1 !! r = Some a → res1 !! r' = Some a → r = r') ∧
    (* only sell blocks to participants who don't already have one *)
    (∀ r a, res1 !! r = Some a → ¬ holds_block alloc res a) ∧
    (* only sell blocks to participants who want to pay for them *)
    (∀ r a, res1 !! r = Some a → wants_block pr a) ∧
    (* don't leave any resources unreserved if someone wants to reserve them *)
    (∀ r, is_Some (alloc !! r) → res' !! r = None →
          (∀ a, wants_block pr a → holds_block alloc' res' a)) ∧
    (* only take a resource from a spot holder if there are no unallocated
       resources left *)
    (∀ r a a', res1 !! r = Some a → alloc !! r = Some (Some a') → a' ≠ a →
          ∀ r', alloc !! r' = Some None → is_Some (res1 !! r')).

(* Exactly as in the spot market. Reserved resources are already allocated, so
   they aren't sold, and their holders already have a resource, so they don't buy. *)
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

(* 1. Time advances, and the seller sets the new spot and reservation prices.
   2. Blocks that have reached their end time lapse into spot holdings.
   3. Spot holders drop based on the new spot price.
   4. Participants who want a block at the new reservation price buy one,
      starting now.
   5. Participants without a resource buy the remaining resources at the spot price. *)
Definition market_step (q q' : state) : Prop :=
  q'.(time) = S q.(time) ∧
  let res := expire_blocks q'.(time) q.(reserved) in
  ∃ alloc,
    reserve_blocks q'.(r_price) q'.(time)
      (drop_resources q'.(price) res q.(allocation)) res alloc q'.(reserved) ∧
    buy_resources q'.(price) alloc q'.(allocation).

Definition used_resources (a : gmap resource (option participant)) :=
  dom (filter (λ '(_, o), o ≠ None) a).

(* every reserved resource is allocated to someone *)
Definition wf_state (q : state) :=
  ∀ r, is_Some (q.(reserved) !! r) → ∃ a, q.(allocation) !! r = Some (Some a).

End big_step.

End reserved_market.
