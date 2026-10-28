(** * A per-level view of the dead set

  This is PLAN.md's item 2, step 3.  The port's world satisfaction is
  levelled ([nola/verus_halt/typing/level_ctx.v] builds the family and
  [∗_{k<j} Winv_k]), and a borrow whose content is interpreted at level
  [k] has to live in a borrow bookkeeping of its own, at its own ghost
  names.  What stands in the way is that [inv.inner_inv] is *indexed by
  the dead set*: if there is one per level, a lifetime's death has to
  advance every level at once, and a body running at level [j] never
  holds the levels at or above [j].

  The way out is for each level to keep its own view of the dead set and
  to catch up lazily.  Two things make that possible, and both are
  checked here rather than assumed.

  - **[alive] is redundant.**  [inv.subseteq_alive_iff] and the three
    [_alive_free] lemmas beside it say the bookkeeping consults [alive]
    only as [al ⊆ alive], and [map_wf] turns that into [al ## dead].  So
    a level can be indexed by *created and dead*, and "κ is alive"
    transfers into a lagging level for free - death is persistent,
    aliveness is not.

  - **Death leaves [created] alone.**  In the [(alive, dead)]
    coordinates a kill moves both indices; in [(created, dead)] it moves
    only the second ([inner_kill_lt_c] below).  Both indices are then
    monotone, which is what lets a level lag behind.

  The change of variable is [created := alive ∪ dead], i.e.

  >  [inner_inv_c created dead blocked := inner_inv (created ∖ dead) dead blocked]

  and it is faithful exactly when [dead ⊆ created], which every
  operation preserves.

  A level's invariant must be a *closed* proposition - it may not
  mention the shared [(sa, sd)] - because [∗_{k<j} Wbor_k] is held on
  its own by a body that was passed nothing else.  That is not free.
  "[dead_k] is behind the real dead set" has a persistent witness, which
  [inner_inv] already carries, so it need not be stated; but "[created_k]
  is behind everything created" has none, aliveness being the
  non-persistent side, and it is what freshness would want when a new
  lifetime reaches a level.  The way out is to make creation need no
  freshness at a level at all: [lv_know] is unconditional, because an
  atom the level already believes dead is absorbed for nothing - adding
  it to [created] does not move [created ∖ dead].  What is left of the
  level's well-formedness ([lv_wf]) is local to the level.

  Two things fall out, and the first corrects PLAN.md.

  **Lifetime creation does not have to reach down the levels.**  A
  borrow of [κ] can be made at a level that has never heard of [κ]: the
  level creates [κ]'s atoms on the spot ([lv_borrow_ready]), needing
  only that it does not believe them dead, which the lender's own token
  supplies.  So a lifetime reaches a level lazily too, when it is first
  borrowed there.  That is the right design and not merely a cheaper
  one: lifetimes are not levelled, borrows are - because a borrow's
  content is interpreted at its level - and the argument that the knot
  cannot close never asked anything of lifetime creation.

  **A level's dead set is the shared kill order's prefix.**  It cannot
  be a free parameter.  Killing [k] is allowed only when everything that
  must outlive [k] is already dead, and the shared logic checks that
  against the shared dead set; a level with some other dead set has no
  way to re-derive it, and [no_greedy_kill_order] shows the condition
  does not follow from consistency alone.  So a level replays the shared
  order, and its state carries the prefix it has reached ([lv_log]) with
  a persistent [mono_list_lb_own] witness - which keeps the invariant
  closed while the order it replays is shared.  [kill_run] is phrased in
  terms of the accumulated dead set, so the condition the shared logic
  checked when an atom died is *literally* the one a level at that
  prefix needs, and [lv_catch_up_to_log] brings any level level with the
  log using nothing else.

  **The levelled invariant has no use for [Delayed].**
  [outer_inv]'s two phases exist because killing a lifetime has to close
  the [NllftG] mask between taking the [Dead] token and updating the
  borrows (see the comment above [inv.outer_inv]).  Here those two steps
  are decoupled *by construction* - the kill is at the shared lifetime
  tokens and the borrow update happens later, at whichever level the
  lender happens to hold - so the level invariant is built from
  [inner_inv] directly. *)

From nola.verus_halt Require Import boxes.
From nola.verus_halt.lifetime Require Import ra.
From nola.verus_halt.lifetime Require Import inv.
From nola.verus_halt.lifetime Require Import new_lt.
From nola.verus_halt.lifetime Require Import expire_lt.
From nola.verus_halt.lifetime Require Import augment_outlives.
From nola.verus_halt.lifetime Require Import iff join split reborrow unborrow unnest.

Require Import stdpp.base.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import auth gset.
From iris.prelude Require Import options.

From nola.iris Require Export iprop sinv.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
Import GuardNotation ModwNotation iPropAppNotation.

(** The borrow side's ghost names, which vary with the level.  The
  lifetime tokens' name does not: it is shared, and that separation is
  what the [LtRa] split bought. *)
Record borNames : Type := BorNames { bn_bor : gname; bn_o : gname; }.

(** A level's own view of the world.  Its dead set is not a free
  parameter: it is the prefix of the shared kill order the level has
  replayed.  That is what makes the outlives condition transfer -
  [kill_run] is phrased in terms of the *accumulated* dead set, so the
  condition the shared logic checked when an atom died is literally the
  one a level sitting at that prefix needs, and the prefix has a
  persistent witness ([mono_list_lb_own]) so the level's invariant stays
  closed. *)
Record lvState : Type := LvState {
  lv_created : gset lt_atom;
  lv_log : list lt_atom;
  lv_blocked : gset lt_atom;
}.

Definition lv_dead (s : lvState) : gset lt_atom :=
  {[default_dead]} ∪ list_to_set (lv_log s).
Definition lv_alive (s : lvState) : gset lt_atom := lv_created s ∖ lv_dead s.

(** Killing an atom at a level, and telling a level about a lifetime.
  The second is unconditional; see [lv_know_one]. *)
Definition lv_kill (k : lt_atom) (s : lvState) : lvState :=
  LvState (lv_created s ∪ {[k]}) (lv_log s ++ [k]) (lv_blocked s).
Definition lv_know (κ : gset lt_atom) (s : lvState) : lvState :=
  LvState (lv_created s ∪ κ) (lv_log s) (lv_blocked s).
Definition lv_block (bl : gset lt_atom) (s : lvState) : lvState :=
  LvState (lv_created s) (lv_log s) (lv_blocked s ∪ bl).
Definition lv_unblock (bl : gset lt_atom) (s : lvState) : lvState :=
  LvState (lv_created s) (lv_log s) (lv_blocked s ∖ bl).

Lemma lv_dead_kill k s : lv_dead (lv_kill k s) = lv_dead s ∪ {[k]}.
Proof. rewrite /lv_dead /lv_kill /= list_to_set_app_L. set_solver. Qed.
Lemma lv_dead_know κ s : lv_dead (lv_know κ s) = lv_dead s.
Proof. done. Qed.

(** The only condition a level's view has to satisfy, and it is entirely
  local: an atom it believes dead is one it has heard of. *)
Definition lv_wf (s : lvState) : Prop := lv_dead s ⊆ lv_created s.

(** [set_solver] is not worth running where the context is large, so the
  two set facts the level bookkeeping needs are proved here. *)
Lemma elem_of_diff_union (X D : gset lt_atom) x :
  x ∈ X → x ∈ (X ∖ D) ∪ D.
Proof.
  move=> Hx. apply elem_of_union.
  destruct (decide (x ∈ D)) as [?|?]; [by right|].
  left. by apply elem_of_difference.
Qed.

Lemma sub_diff_union (X D Z : gset lt_atom) : Z ⊆ X → Z ⊆ (X ∖ D) ∪ D.
Proof. move=> H x /H. apply elem_of_diff_union. Qed.

Section Levelled.
  Context {Σ: gFunctors} {FML : oFunctor}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS_gen hlc Σ}.
  Context `{!boxG Σ, !sinvGS FML Σ, !BorSem FML Σ}.

  (** Shared by every level: the lifetime tokens' ghost name, and the
    kill order's. *)
  Context (γlt: gname).
  Context `{!mono_listG lt_atom Σ}.
  Context (γlog: gname).
  Context `{!inG Σ (authUR (gsetUR lt_atom))}.
  Context (γmint: gname).

  (** ** Which atoms have ever been minted

    A level's created set has to stay inside the atoms the shared
    lifetime logic has minted, and that fact cannot live in the shared
    invariant: with one bookkeeping per level the shared part cannot see
    the levels' states.  It is carried here instead, as a persistent
    witness - which works because [sa ∪ sd] only ever grows. *)
  Definition Minted (X : gset lt_atom) : iProp Σ :=
    own γmint (◯ (X : gsetUR lt_atom)).
  Definition MintAuth (X : gset lt_atom) : iProp Σ :=
    own γmint (● (X : gsetUR lt_atom)).

  #[export] Instance minted_persistent {X} : Persistent (Minted X).
  Proof. exact _. Qed.

  Lemma minted_union X Y : Minted X -∗ Minted Y -∗ Minted (X ∪ Y).
  Proof.
    rewrite /Minted. iIntros "A B". iCombine "A B" as "C".
    iApply (own_mono with "C"). apply auth_frag_mono, gset_included.
    set_solver.
  Qed.
  Lemma minted_mono X Y : X ⊆ Y → Minted Y -∗ Minted X.
  Proof.
    move=> Hsub. rewrite /Minted. iIntros "A". iApply (own_mono with "A").
    by apply auth_frag_mono, gset_included.
  Qed.
  Lemma minted_agree X Y : MintAuth Y -∗ Minted X -∗ ⌜X ⊆ Y⌝.
  Proof.
    rewrite /MintAuth /Minted. iIntros "A B".
    iDestruct (own_valid_2 with "A B") as %[inc ?]%auth_both_valid_discrete.
    iPureIntro. by apply gset_included.
  Qed.
  Lemma minted_alloc_set X Y :
    MintAuth X ==∗ MintAuth (X ∪ Y) ∗ Minted (X ∪ Y).
  Proof.
    rewrite /MintAuth /Minted. iIntros "A".
    iMod (own_update _ _ (● ((X ∪ Y) : gsetUR lt_atom)
      ⋅ ◯ ((X ∪ Y) : gsetUR lt_atom)) with "A") as "[$ $]";
      [|done].
    apply auth_update_alloc, gset_local_update. set_solver.
  Qed.
  Lemma minted_get X : MintAuth X ==∗ MintAuth X ∗ Minted X.
  Proof.
    iIntros "A". iMod (minted_alloc_set X X with "A") as "[A B]".
    rewrite union_idemp_L. by iFrame.
  Qed.

  (** ** How far a level's outlives relation has caught up

    The outlives relation grows, and the shared logic may grow it while
    a level is not held - a body at execution level [j] never holds the
    levels at or above [j].  So a level's relation lags, exactly as its
    dead set does, and what it needs of the shared one is a *bound*:
    [kill_run] is antitone in the relation ([kill_run_anti] below), so a
    level with fewer pairs may replay a run the shared logic checked
    with more, and [outlives_consistent] goes the same way.

    As with [Minted], the bound cannot be stated in the shared
    invariant - that part cannot see the levels - so it is a persistent
    witness against an authority that only grows. *)
  Context `{!inG Σ (authUR (gsetUR (gset lt_atom * lt_atom)))}.
  Context (γoset: gname).

  Definition Osub (X : outlives_set) : iProp Σ :=
    own γoset (◯ (X : gsetUR (gset lt_atom * lt_atom))).
  Definition OsetAuth (X : outlives_set) : iProp Σ :=
    own γoset (● (X : gsetUR (gset lt_atom * lt_atom))).

  #[export] Instance osub_persistent {X} : Persistent (Osub X).
  Proof. exact _. Qed.

  Lemma osub_mono X Y : X ⊆ Y → Osub Y -∗ Osub X.
  Proof.
    move=> Hsub. rewrite /Osub. iIntros "A". iApply (own_mono with "A").
    by apply auth_frag_mono, gset_included.
  Qed.
  Lemma osub_agree X Y : OsetAuth Y -∗ Osub X -∗ ⌜X ⊆ Y⌝.
  Proof.
    rewrite /OsetAuth /Osub. iIntros "A B".
    iDestruct (own_valid_2 with "A B") as %[inc ?]%auth_both_valid_discrete.
    iPureIntro. by apply gset_included.
  Qed.
  Lemma osub_alloc_set X Y :
    OsetAuth X ==∗ OsetAuth (X ∪ Y) ∗ Osub (X ∪ Y).
  Proof.
    rewrite /OsetAuth /Osub. iIntros "A".
    iMod (own_update _ _ (● ((X ∪ Y) : gsetUR (gset lt_atom * lt_atom))
      ⋅ ◯ ((X ∪ Y) : gsetUR (gset lt_atom * lt_atom))) with "A") as "[$ $]";
      [|done].
    apply auth_update_alloc, gset_local_update. set_solver.
  Qed.
  Lemma osub_get X : OsetAuth X ==∗ OsetAuth X ∗ Osub X.
  Proof.
    iIntros "A". iMod (osub_alloc_set X X with "A") as "[A B]".
    rewrite union_idemp_L. by iFrame.
  Qed.

  (** ** The change of variable *)

  Definition inner_inv_c (n : borNames) (created dead blocked : gset lt_atom)
      : iProp Σ :=
    inner_inv (FML:=FML) γlt n.(bn_bor) n.(bn_o) (created ∖ dead) dead blocked.

  (** Going the other way needs [alive ## dead], which [inner_inv] itself
    supplies. *)
  Lemma inner_inv_to_c n alive dead blocked :
    inner_inv (FML:=FML) γlt n.(bn_bor) n.(bn_o) alive dead blocked ⊢
    inner_inv_c n (alive ∪ dead) dead blocked.
  Proof.
    iIntros "Inv".
    iDestruct (inv_get_alive_dead_disj with "Inv") as "%Hdisj".
    rewrite /inner_inv_c.
    by replace ((alive ∪ dead) ∖ dead) with alive by set_solver.
  Qed.

  (** ** The three operations, in created coordinates *)

  (** Creation moves [created] and leaves [dead] alone. *)
  Lemma inner_new_lt_c n created dead blocked k :
    k ∉ created ∪ dead →
    inner_inv_c n created dead blocked -∗ |=[box_wsat bor_sem]=>
    inner_inv_c n (created ∪ {[k]}) dead blocked.
  Proof.
    move=> Hk. rewrite /inner_inv_c.
    replace ((created ∪ {[k]}) ∖ dead) with ((created ∖ dead) ∪ {[k]})
      by set_solver.
    iApply inner_new_lt. set_solver.
  Qed.

  (** An atom the level has already heard of costs nothing to create
    again, so creation needs only that the level does not believe it
    dead. *)
  Lemma inner_new_lt_c' n created dead blocked k :
    k ∉ dead →
    inner_inv_c n created dead blocked -∗ |=[box_wsat bor_sem]=>
    inner_inv_c n (created ∪ {[k]}) dead blocked.
  Proof.
    move=> Hk. destruct (decide (k ∈ created)) as [Hin|Hout].
    - replace (created ∪ {[k]}) with created by set_solver.
      iIntros "Inv". by iModIntro.
    - iApply inner_new_lt_c. set_solver.
  Qed.

  Lemma inner_new_lts_c n dead blocked (κ : gset lt_atom) :
    κ ## dead → ∀ created,
    inner_inv_c n created dead blocked -∗ |=[box_wsat bor_sem]=>
    inner_inv_c n (created ∪ κ) dead blocked.
  Proof.
    induction κ as [|k κ Hk IH] using set_ind_L=> Hdisj created.
    { replace (created ∪ ∅) with created by set_solver.
      iIntros "Inv". by iModIntro. }
    iIntros "Inv".
    iMod (inner_new_lt_c' n created dead blocked k with "Inv") as "Inv";
      [set_solver|].
    iMod (IH ltac:(set_solver) (created ∪ {[k]}) with "Inv") as "Inv".
    iModIntro.
    by replace (created ∪ ({[k]} ∪ κ)) with ((created ∪ {[k]}) ∪ κ)
      by set_solver.
  Qed.

  (** Death moves [dead] and leaves [created] alone.  This is the whole
    point of the change of variable: in [(alive, dead)] coordinates both
    indices move, and a level that lagged in one would have to lag in the
    other too. *)
  Lemma inner_kill_lt_c n created dead blocked outlives k :
    k ∈ created → k ∉ dead → k ∉ blocked →
    (∀ other , (other, k) ∈ outlives → ¬(other ## (dead ∪ {[k]}))) →
    inner_inv_c n created dead blocked ∗ Outlives n.(bn_o) outlives ∗ Dead γlt k
      -∗ |=[box_wsat bor_sem]{↑NllftUsr ∪ ↑NllftUsr2}=>
    inner_inv_c n created (dead ∪ {[k]}) blocked ∗ Outlives n.(bn_o) outlives.
  Proof.
    move=> Hcr Hd Hbl Ho. rewrite /inner_inv_c.
    replace (created ∖ (dead ∪ {[k]})) with ((created ∖ dead) ∖ {[k]})
      by set_solver.
    iApply inner_kill_lt; [set_solver|done|done].
  Qed.

  (** An atom this level never created dies here too, and then both
    indices grow by it.  This is the case that lets a level skip a
    lifetime entirely: levels at or above the one a lifetime was created
    for never learn of it until it dies. *)
  Lemma inner_instant_kill_c n created dead blocked k :
    k ∉ created ∪ dead →
    Dead γlt k ∗ inner_inv_c n created dead blocked ={∅}=∗
    inner_inv_c n (created ∪ {[k]}) (dead ∪ {[k]}) blocked.
  Proof.
    move=> Hk. rewrite /inner_inv_c.
    replace ((created ∪ {[k]}) ∖ (dead ∪ {[k]})) with (created ∖ dead)
      by set_solver.
    iApply inner_instant_kill_lt. set_solver.
  Qed.

  (** ** Catching up, one atom at a time

    A level that has lagged behind learns of a death by one of the two
    kills above, according to whether it had heard of the lifetime at
    all.  Both leave it at [lv_kill k s]. *)
  Lemma inner_catch_up_one n created dead blocked outlives k :
    k ∉ dead → k ∉ blocked →
    (∀ other , (other, k) ∈ outlives → ¬(other ## (dead ∪ {[k]}))) →
    inner_inv_c n created dead blocked ∗ Outlives n.(bn_o) outlives ∗ Dead γlt k
      -∗ |=[box_wsat bor_sem]{↑NllftUsr ∪ ↑NllftUsr2}=>
    inner_inv_c n (created ∪ {[k]}) (dead ∪ {[k]}) blocked ∗
      Outlives n.(bn_o) outlives.
  Proof.
    move=> Hd Hbl Ho. destruct (decide (k ∈ created)) as [Hin|Hout].
    - replace (created ∪ {[k]}) with created by set_solver.
      by iApply inner_kill_lt_c.
    - rewrite -modw_fold. iIntros "(Inv & Ou & #D) W".
      iApply (fupd_mask_mono ∅); [set_solver|].
      iMod (inner_instant_kill_c with "[$D $Inv]") as "Inv"; [set_solver|].
      iModIntro. iFrame.
  Qed.

  (** Catching up over a run of deaths.  The run is a *list*, not a
    set, and the next lemma says why it has to be.

    What it carries is what the shared logic checks at each kill: that
    the atom was not already dead, and the outlives condition.  It does
    *not* carry [k ∉ blocked], which follows from the [Alive] token the
    level parked ([blocked_dead]) and is discharged in
    [lv_catch_up_one]. *)
  Fixpoint kill_run (dead : gset lt_atom) (outlives : outlives_set)
      (ks : list lt_atom) : Prop :=
    match ks with
    | [] => True
    | k :: ks' => k ∉ dead
        ∧ (∀ other , (other, k) ∈ outlives → ¬(other ## (dead ∪ {[k]})))
        ∧ kill_run (dead ∪ {[k]}) outlives ks'
    end.

  (** Replaying a run in two stages, which is what a level catching up
    to a prefix of the shared kill order does. *)
  Lemma kill_run_app dead outlives ks1 ks2 :
    kill_run dead outlives (ks1 ++ ks2) ↔
    kill_run dead outlives ks1
      ∧ kill_run (dead ∪ list_to_set ks1) outlives ks2.
  Proof.
    move: dead. induction ks1 as [|k ks1 IH]=> dead.
    - cbn [app kill_run].
      replace (dead ∪ list_to_set (@nil lt_atom)) with dead by set_solver.
      tauto.
    - cbn [app kill_run]. rewrite IH.
      replace (dead ∪ list_to_set (k :: ks1))
        with ((dead ∪ {[k]}) ∪ list_to_set ks1) by set_solver.
      tauto.
  Qed.

  (** *** A past run survives the outlives relation growing

    This is what makes a lagging level safe.  A level replays the shared
    kill order, and [kill_run] quantifies over the outlives relation as
    it stands *now*, not as it stood when each atom died - so a pair
    added later could in principle invalidate a step the shared logic
    had already checked.  It cannot: [lifetime_full.llft_augment_outlives]
    adds [(κ, k)] only for [k ∈ κ' ⊆ sa], so a new pair's second
    component is alive, hence not in the shared dead set and not in the
    run at all.

    Without this the level would have to be caught up before every
    [llft_augment_outlives], and a body at level [j] cannot catch up the
    levels at or above [j]. *)
  Lemma kill_run_mono dead outlives outlives' ks :
    (∀ o , o ∈ outlives' → o ∉ outlives →
       o.2 ∉ (list_to_set ks : gset lt_atom)) →
    kill_run dead outlives ks → kill_run dead outlives' ks.
  Proof.
    move: dead. induction ks as [|k ks IH]=> dead Hnew Hrun; [done|].
    destruct Hrun as [Hnd [Ho Hrun]]. split; [done|]. split.
    - move=> other Hin. destruct (decide ((other, k) ∈ outlives)) as [?|Hnot].
      + by apply Ho.
      + exfalso. have := Hnew _ Hin Hnot=> /=. set_solver.
    - apply IH; [|done]. move=> o Hin Hnot. have := Hnew o Hin Hnot.
      set_solver.
  Qed.

  (** A level replaying the shared order with *fewer* pairs than the
    shared logic checked it with is safe, and that is this file's half
    of the lazy outlives catch-up: [kill_run] is antitone, so the bound
    [Osub] carries is all a level needs. *)
  Lemma kill_run_anti dead outlives outlives' ks :
    outlives' ⊆ outlives →
    kill_run dead outlives ks → kill_run dead outlives' ks.
  Proof.
    move=> Hsub. apply kill_run_mono=> o Hin Hnot. by have := Hsub _ Hin.
  Qed.

  (** ** Why the run is a list

    [outlives_consistent] alone does not order a catch-up: a level can
    be consistent with the real dead set and yet have no atom it is
    allowed to kill first.  The witness is a two-cycle - [a] must end
    before [b] and [b] before [a] - which is consistent once both are
    dead and is simply unreachable, but unreachability is a fact about
    the real kill order, not about [outlives_consistent].  So a level
    catches up by replaying that order, as [kill_run] says. *)
  Lemma no_greedy_kill_order :
    ∃ (outlives : outlives_set) (sd : gset lt_atom),
      outlives_consistent sd outlives ∧
      (∀ k, k ∈ sd →
        ¬ (∀ other , (other, k) ∈ outlives → ¬(other ## (∅ ∪ {[k]})))).
  Proof.
    set a := LtAtomSwell 0. set b := LtAtomSwell 1.
    exists ({[ ({[a]}, b) ; ({[b]}, a) ]} : outlives_set), ({[a; b]} : gset lt_atom).
    split.
    - move=> o /elem_of_union [/elem_of_singleton ->|/elem_of_singleton ->] /=;
        set_solver.
    - move=> k /elem_of_union
        [/elem_of_singleton ->|/elem_of_singleton ->] Hall.
      + apply (Hall {[b]}); set_solver.
      + apply (Hall {[a]}); set_solver.
  Qed.

  (** ** What a lagging level gets for free

    Opening a borrow of [κ] at a level that has fallen behind needs
    [κ ## dead_k] and [κ ⊆ created_k].  Both are free, and the first is
    free *logically* rather than arithmetically: the level's own
    [inner_inv] carries [□ ∀ d ∈ dead, Dead γlt d], so an atom the user
    holds a token for cannot be believed dead there.

    That matters more than it looks.  Nothing below relates a level's
    view to the shared [(sa, sd)] - and nothing may, because a level's
    world satisfaction has to be a closed proposition: [∗_{k<j} Wbor_k]
    is held on its own, by a body that holds no shared lifetime state
    beyond what it was passed. *)
  Lemma inner_inv_deads n created dead blocked :
    inner_inv_c n created dead blocked ⊢ □ (∀ d , ⌜d ∈ dead⌝ -∗ Dead γlt d).
  Proof.
    iIntros "Inv".
    by iDestruct "Inv" as (mbs mprops Ptotal outlives) "(_ & _ & #Ds & _)".
  Qed.

  Lemma map_wf_created {created dead blocked outlives mbs sn al de} :
    dead ⊆ created →
    inv.map_wf (created ∖ dead) dead blocked outlives mbs →
    mbs !! sn = Some (Borrow al de) → al ∪ de ⊆ created.
  Proof.
    move=> Hdc [_ [_ [_ [Hall _]]]] Hsn.
    have H := Hall sn _ Hsn. set_solver.
  Qed.

  (** ** The lifetime-level invariant

    One borrow bookkeeping per level, each at its own names and with its
    own view of the world.  The lifetime tokens are shared, so the
    blocked atoms' tokens are parked here, level by level.

    Note what is *not* here: no [sa], no [sd], no relation to them.  The
    level's place in the shared kill order is carried by a *persistent*
    prefix witness, so the invariant is a closed proposition even though
    the order it replays is shared.  A death in the shared logic
    therefore leaves [llft_lv_inv] syntactically unchanged - there is no
    lemma to state, which is lazy catch-up in its sharpest form.  A
    level moves only when a lender comes to collect, by
    [lv_catch_up_one]. *)
  Definition lv_inv (n : borNames) (s : lvState) : iProp Σ :=
    ⌜lv_wf s⌝ ∗ mono_list_lb_own γlog (lv_log s) ∗ Minted (lv_created s)
      ∗ inner_inv_c n (lv_created s) (lv_dead s) (lv_blocked s)
      ∗ [∗ set] b ∈ lv_blocked s, Alive γlt b.

  (** Opening a level's invariant down to the borrow bookkeeping the
    existing [inner_*] rules speak about.  Definitional: the level's
    [(created, dead)] is the old [(alive, dead)] under the change of
    variable. *)
  Lemma lv_inv_unfold n s :
    lv_inv n s ⊣⊢ ⌜lv_wf s⌝ ∗ mono_list_lb_own γlog (lv_log s)
      ∗ Minted (lv_created s)
      ∗ inner_inv (FML:=FML) γlt n.(bn_bor) n.(bn_o)
          (lv_alive s) (lv_dead s) (lv_blocked s)
      ∗ [∗ set] b ∈ lv_blocked s, Alive γlt b.
  Proof. done. Qed.

  (** A level's prefix is a prefix of the shared kill order. *)
  Lemma lv_log_prefix n s log dq :
    mono_list_auth_own γlog dq log -∗ lv_inv n s -∗
    ⌜lv_log s `prefix_of` log⌝.
  Proof.
    iIntros "Auth (_ & #Lb & _ & _ & _)".
    iDestruct (mono_list_auth_lb_own_valid with "Auth Lb") as "%Hv".
    iPureIntro. by destruct Hv.
  Qed.

  (** The witness is persistent, so it can be read off without spending
    the invariant. *)
  Lemma lv_inv_split n s :
    lv_inv n s ⊣⊢ mono_list_lb_own γlog (lv_log s) ∗ lv_inv n s.
  Proof.
    rewrite /lv_inv. iSplit.
    - iIntros "(%Hwf & #Lb & #Mint & Inv & Bl)". iSplitR; [iExact "Lb"|].
      iSplitR; [by iPureIntro|]. iSplitR; [iExact "Lb"|].
      iSplitR; [iExact "Mint"|].
      iSplitL "Inv"; [iExact "Inv"|iExact "Bl"].
    - by iIntros "[_ $]".
  Qed.

  Definition llft_lv_inv (ls : list (borNames * lvState)) : iProp Σ :=
    [∗ list] p ∈ ls, lv_inv p.1 p.2.

  (** A lifetime the user holds a token for is not dead at any level. *)
  Lemma lv_alive_disj_dead n s (κ : gset lt_atom) :
    ([∗ set] x ∈ κ, Alive γlt x) -∗ lv_inv n s -∗
    ⌜κ ## lv_dead s⌝ ∗ ([∗ set] x ∈ κ, Alive γlt x) ∗ lv_inv n s.
  Proof.
    iIntros "Al L". destruct (decide (κ ## lv_dead s)) as [?|Hnd].
    { iSplitR; [by iPureIntro|]. iSplitL "Al"; [iExact "Al"|iExact "L"]. }
    iExFalso.
    have Hne : κ ∩ lv_dead s ≠ ∅.
    { move=> He. apply Hnd. by apply disjoint_intersection_L. }
    have [x Hx] := set_choose_L _ Hne.
    apply elem_of_intersection in Hx as [Hx1 Hx2].
    iDestruct "L" as "(_ & _ & _ & Inv & _)".
    iDestruct (inner_inv_deads with "Inv") as "#Ds".
    rewrite (big_sepS_delete _ _ _ Hx1). iDestruct "Al" as "[A _]".
    iApply (lt_alive_dead_false γlt x). iSplit; [iExact "A"|].
    by iApply "Ds".
  Qed.

  (** A lifetime the lender holds a token for is not blocked at this
    level either: the level parks the *other* [Alive] token, and there
    are only two. *)
  Lemma lv_blocked_disj n s (κ sa : gset lt_atom) :
    κ ⊆ sa →
    ([∗ set] x ∈ sa, Alive γlt x) -∗ ([∗ set] x ∈ κ, Alive γlt x) -∗
    lv_inv n s -∗ ⌜κ ## lv_blocked s⌝.
  Proof.
    move=> Hsub. iIntros "Sa Sk L".
    destruct (decide (κ ## lv_blocked s)) as [?|Hnd]; [done|]. iExFalso.
    have Hne : κ ∩ lv_blocked s ≠ ∅.
    { move=> He. apply Hnd. by apply disjoint_intersection_L. }
    have [x Hx] := set_choose_L _ Hne.
    apply elem_of_intersection in Hx as [Hx1 Hx2].
    iDestruct "L" as "(_ & _ & _ & _ & Bl)".
    rewrite (big_sepS_delete _ sa x); last by set_solver.
    rewrite (big_sepS_delete _ κ x); last done.
    rewrite (big_sepS_delete _ (lv_blocked s) x); last done.
    iDestruct "Sa" as "[A1 _]". iDestruct "Sk" as "[A2 _]".
    iDestruct "Bl" as "[A3 _]".
    iApply alive_alive_alive_false. iFrame "A1 A2 A3".
  Qed.

  (** No level can be blocking on an atom that is dead: the level parks
    the lender's own [Alive] token while a borrow is unborrowed.  This
    discharges [inner_catch_up_one]'s [k ∉ blocked] rather than assuming
    it. *)
  Lemma blocked_dead (bl : gset lt_atom) k :
    Dead γlt k -∗ ([∗ set] b ∈ bl, Alive γlt b) -∗
    ⌜k ∉ bl⌝ ∗ [∗ set] b ∈ bl, Alive γlt b.
  Proof.
    iIntros "#D Bl". destruct (decide (k ∈ bl)) as [Hin|].
    2: { iSplitR; [by iPureIntro|]. iExact "Bl". }
    iExFalso. rewrite (big_sepS_delete _ _ _ Hin). iDestruct "Bl" as "[A _]".
    iApply (lt_alive_dead_false γlt k). iSplit; [iExact "A"|iExact "D"].
  Qed.

  (** *** Catching up at a level

    The level advances one step along the shared kill order, so it is
    handed the witness for the longer prefix.  What it needs beyond that
    is exactly what [kill_run] carries. *)
  Lemma lv_catch_up_one n s outlives k :
    k ∉ lv_dead s →
    (∀ other , (other, k) ∈ outlives → ¬(other ## (lv_dead s ∪ {[k]}))) →
    mono_list_lb_own γlog (lv_log s ++ [k]) -∗ Minted {[k]} -∗
    lv_inv n s ∗ Outlives n.(bn_o) outlives ∗ Dead γlt k
      -∗ |=[box_wsat bor_sem]{↑NllftUsr ∪ ↑NllftUsr2}=>
    lv_inv n (lv_kill k s) ∗ Outlives n.(bn_o) outlives.
  Proof.
    move=> Hnd Ho.
    iIntros "#Lb' #Mk ((%Hwf & #Lb & #Mint & Inv & Bl) & Ou & #D)".
    iDestruct (blocked_dead with "D Bl") as "[%Hbl Bl]".
    iMod (inner_catch_up_one n (lv_created s) (lv_dead s) (lv_blocked s)
      outlives k with "[$Inv $Ou $D]") as "[Inv Ou]"; [done|done|done|].
    iModIntro. iSplitR "Ou"; [|iExact "Ou"].
    rewrite /lv_inv /lv_wf lv_dead_kill. iSplitR.
    { iPureIntro. rewrite /lv_kill /=. set_solver. }
    iFrame "Lb'". iSplitR; [iApply (minted_union with "Mint Mk")|].
    iSplitL "Inv"; [iExact "Inv"|iExact "Bl"].
  Qed.

  (** An atom this level has never heard of needs no outlives condition
    at all: nothing in the level's map or its outlives relation mentions
    it, so the step is [inner_instant_kill_c]. *)
  Lemma lv_instant_kill n s k :
    k ∉ lv_created s →
    mono_list_lb_own γlog (lv_log s ++ [k]) -∗ Minted {[k]} -∗
    Dead γlt k -∗ lv_inv n s ={∅}=∗ lv_inv n (lv_kill k s).
  Proof.
    move=> Hk. iIntros "#Lb' #Mk #D (%Hwf & #Lb & #Mint & Inv & Bl)".
    iMod (inner_instant_kill_c n (lv_created s) (lv_dead s) (lv_blocked s) k
      with "[$D $Inv]") as "Inv"; [set_solver|].
    iModIntro. rewrite /lv_inv /lv_wf lv_dead_kill. iSplitR.
    { iPureIntro. rewrite /lv_kill /=. set_solver. }
    iFrame "Lb'". iSplitR; [iApply (minted_union with "Mint Mk")|].
    iSplitL "Inv"; [iExact "Inv"|iExact "Bl"].
  Qed.

  (** Replaying a whole run at a level. *)
  Fixpoint lv_kills (ks : list lt_atom) (s : lvState) : lvState :=
    match ks with [] => s | k :: ks' => lv_kills ks' (lv_kill k s) end.

  Lemma lv_log_kills ks s : lv_log (lv_kills ks s) = lv_log s ++ ks.
  Proof.
    move: s. induction ks as [|k ks IH]=> s /=; [by rewrite app_nil_r|].
    by rewrite IH /lv_kill /= -app_assoc.
  Qed.

  Lemma lv_catch_up n outlives ks : ∀ s,
    kill_run (lv_dead s) outlives ks →
    mono_list_lb_own γlog (lv_log s ++ ks) -∗ Minted (list_to_set ks) -∗
    lv_inv n s ∗ Outlives n.(bn_o) outlives ∗ ([∗ list] k ∈ ks, Dead γlt k)
      -∗ |=[box_wsat bor_sem]{↑NllftUsr ∪ ↑NllftUsr2}=>
    lv_inv n (lv_kills ks s) ∗ Outlives n.(bn_o) outlives.
  Proof.
    induction ks as [|k ks IH]=> s Hrun.
    { iIntros "_ _ (L & Ou & _)". iModIntro.
      iSplitL "L"; [iExact "L"|iExact "Ou"]. }
    destruct Hrun as [Hnd [Ho Hrun]].
    iIntros "#Lb #Mks (L & Ou & [#D Ds])".
    iMod (lv_catch_up_one n s outlives k Hnd Ho with "[] [] [$L $Ou $D]")
      as "[L Ou]".
    { iApply (mono_list_lb_own_le with "Lb"). exists ks.
      by rewrite -app_assoc. }
    { iApply (minted_mono with "Mks"). rewrite list_to_set_cons. set_solver. }
    iApply (IH (lv_kill k s) ltac:(by rewrite lv_dead_kill) with "[] []").
    { rewrite /lv_kill /= -app_assoc. iExact "Lb". }
    { iApply (minted_mono with "Mks"). rewrite list_to_set_cons. set_solver. }
    iSplitL "L"; [iExact "L"|]. iSplitL "Ou"; [iExact "Ou"|iExact "Ds"].
  Qed.

  (** *** A level can always be brought level with the shared log

    This is what the prefix witness buys.  The level's own dead set is
    the log's prefix it has replayed, so the suffix is determined, and
    [kill_run_app] hands over exactly the conditions the shared logic
    checked when those atoms died.  Nothing is needed about the level's
    created set, and nothing relates it to the shared `(sa, sd)`. *)
  Lemma lv_catch_up_to_log n s outlives log dq :
    kill_run {[default_dead]} outlives log →
    mono_list_auth_own γlog dq log -∗ Minted (list_to_set log) -∗
    ([∗ list] k ∈ log, Dead γlt k) -∗
    lv_inv n s ∗ Outlives n.(bn_o) outlives
      -∗ |=[box_wsat bor_sem]{↑NllftUsr ∪ ↑NllftUsr2}=>
    mono_list_auth_own γlog dq log ∗
      ∃ s', ⌜lv_log s' = log⌝ ∗ lv_inv n s' ∗ Outlives n.(bn_o) outlives.
  Proof.
    move=> Hrun. iIntros "Auth #Mlog #Ds [L Ou]".
    iAssert (□ [∗ list] k ∈ log, Dead γlt k)%I as "#Ds'"; [by iModIntro|].
    rewrite lv_inv_split. iDestruct "L" as "[#Lb L]".
    iDestruct (mono_list_auth_lb_own_valid with "Auth Lb") as "%Hv".
    destruct Hv as [_ [ks Hks]].
    iDestruct (mono_list_lb_own_get with "Auth") as "#LbA".
    rewrite {1}Hks in Hrun. apply kill_run_app in Hrun as [_ Hrun].
    iMod (lv_catch_up n outlives ks s with "[] [] [$L $Ou]") as "[L Ou]".
    { by rewrite /lv_dead. }
    { rewrite -Hks. iExact "LbA". }
    { iApply (minted_mono with "Mlog"). rewrite Hks list_to_set_app_L.
      set_solver. }
    { rewrite Hks big_sepL_app. by iDestruct "Ds'" as "[_ $]". }
    iModIntro. iFrame "Auth". iExists (lv_kills ks s).
    iSplitR; [by rewrite lv_log_kills -Hks|].
    iSplitL "L"; [iExact "L"|iExact "Ou"].
  Qed.

  (** *** A lifetime reaches a level when it is first borrowed there

    PLAN.md expected lifetime creation to have to reach down the levels
    below the one a lifetime was made for.  It does not have to reach
    them at all.  A borrow of [κ] can be made at a level that has never
    heard of [κ]: the level takes [κ]'s atoms on the spot ([lv_know],
    which asks nothing), and the lender's own token then says they are
    alive there ([lv_alive_disj_dead]).

    That is the right design and not merely a cheaper one.  Lifetimes
    are not levelled - borrows are, because a borrow's content is
    interpreted at its level - and the argument that the knot cannot
    close (a body at level [j] holds only [Wbor_h] for [h < j], so it
    cannot open the level-[k] borrow holding its own closure) never
    asked anything of lifetime creation. *)
  (** Telling a level about a lifetime is unconditional.  An atom it
    already believes dead is absorbed for nothing, because adding it to
    [created] does not move [created ∖ dead]. *)
  Lemma inner_know_c n created dead blocked (κ : gset lt_atom) :
    inner_inv_c n created dead blocked -∗ |=[box_wsat bor_sem]=>
    inner_inv_c n (created ∪ κ) dead blocked.
  Proof.
    iIntros "Inv".
    iMod (inner_new_lts_c n dead blocked (κ ∖ dead) ltac:(set_solver) created
      with "Inv") as "Inv".
    iModIntro. rewrite /inner_inv_c.
    by replace ((created ∪ (κ ∖ dead)) ∖ dead) with ((created ∪ κ) ∖ dead)
      by set_solver.
  Qed.

  Lemma lv_know_one n s κ :
    Minted κ -∗ lv_inv n s -∗ |=[box_wsat bor_sem]=> lv_inv n (lv_know κ s).
  Proof.
    iIntros "#Mk (%Hwf & #Lb & #Mint & Inv & Bl)".
    iMod (inner_know_c n (lv_created s) (lv_dead s) (lv_blocked s) κ with "Inv")
      as "Inv".
    iModIntro. rewrite /lv_inv /lv_wf lv_dead_know.
    iSplitR; [iPureIntro; rewrite /lv_know /=; set_solver|].
    iFrame "Lb". iSplitR; [iApply (minted_union with "Mint Mk")|].
    iSplitL "Inv"; [iExact "Inv"|iExact "Bl"].
  Qed.

  (** And once the level knows about [κ], a lender's own token says [κ]
    is alive there. *)
  Lemma lv_borrow_ready n s (κ : gset lt_atom) :
    Minted κ -∗ ([∗ set] x ∈ κ, Alive γlt x) -∗ lv_inv n s -∗
    |=[box_wsat bor_sem]=> ⌜κ ⊆ lv_alive (lv_know κ s)⌝ ∗
      ([∗ set] x ∈ κ, Alive γlt x) ∗ lv_inv n (lv_know κ s).
  Proof.
    iIntros "#Mk Al L".
    iDestruct (lv_alive_disj_dead with "Al L") as "(%Hdisj & Al & L)".
    iMod (lv_know_one n s κ with "Mk L") as "L". iModIntro.
    iSplitR; [iPureIntro; rewrite /lv_alive /lv_know /=; set_solver|].
    iSplitL "Al"; [iExact "Al"|iExact "L"].
  Qed.

  (** *** Reading the level's outlives bookkeeping, and extending it *)
  Lemma lv_dead_dd s : default_dead ∈ lv_dead s.
  Proof. rewrite /lv_dead. set_solver. Qed.

  Lemma lv_outlives_cond n s ol :
    lv_inv n s -∗ Outlives n.(bn_o) ol -∗
    ⌜(∀ o , o ∈ ol → o.1 ⊆ lv_created s ∧ o.2 ∈ lv_created s)
      ∧ outlives_consistent (lv_dead s) ol⌝
      ∗ lv_inv n s ∗ Outlives n.(bn_o) ol.
  Proof.
    iIntros "(%Hwf & #Lb & #Mint & Inv & Bl) Ou".
    iDestruct (inv_get_outlives_condition γlt n.(bn_bor) n.(bn_o)
      (lv_alive s) (lv_dead s) (lv_blocked s) ol with "[$Inv $Ou]")
      as "#%Hoc".
    iDestruct (inv_get_outlives_consistent γlt n.(bn_bor) n.(bn_o)
      (lv_alive s) (lv_dead s) (lv_blocked s) ol with "[$Inv $Ou]")
      as "#%Hcons".
    iSplitR.
    { iPureIntro. split; [|done]=> o Ho. have [H1 H2] := Hoc o Ho.
      rewrite /lv_alive in H1 H2. rewrite /lv_wf in Hwf. split.
      - etrans; [exact H1|]. set_solver.
      - revert H2. set_solver. }
    iSplitR "Ou"; [|iExact "Ou"].
    rewrite /lv_inv. iSplitR; [by iPureIntro|]. iFrame "Lb Mint".
    iSplitL "Inv"; [iExact "Inv"|iExact "Bl"].
  Qed.

  (** Extending the level's outlives relation.  The atoms the new pairs
    mention may be ones this level has never heard of, so it is told
    about them first - which asks nothing. *)
  Lemma lv_augment_outlives n s (κs : gset lt_atom) ol ol' :
    ol ⊆ ol' →
    (∀ o , o ∈ ol' → o.1 ⊆ lv_created s ∪ κs ∧ o.2 ∈ lv_created s ∪ κs) →
    outlives_consistent (lv_dead s) ol' →
    Minted κs -∗ lv_inv n s ∗ Outlives n.(bn_o) ol -∗
    |=[box_wsat bor_sem]=>
    lv_inv n (lv_know κs s) ∗ Outlives n.(bn_o) ol'.
  Proof.
    move=> Hsub Hwf Hoc. iIntros "#Mk [L Ou]".
    iMod (lv_know_one n s κs with "Mk L")
      as "(%Hwf' & #Lb & #Mint & Inv & Bl)".
    iMod (inner_augment_outlives γlt n.(bn_bor) n.(bn_o) n.(bn_o)
      (lv_alive (lv_know κs s)) (lv_dead (lv_know κs s))
      (lv_blocked (lv_know κs s)) ol ol' with "[$Inv $Ou]")
      as "[Inv Ou]".
    { move=> o Ho. have [H1 H2] := Hwf o Ho.
      rewrite /lv_alive /lv_know /=. split.
      - by apply sub_diff_union.
      - by apply elem_of_diff_union. }
    { done. }
    { by rewrite lv_dead_know. }
    iModIntro. iSplitR "Ou"; [|iExact "Ou"].
    rewrite /lv_inv. iSplitR; [by iPureIntro|]. iFrame "Lb Mint".
    iSplitL "Inv"; [iExact "Inv"|iExact "Bl"].
  Qed.

  (** The level's created set stays inside the minted atoms. *)
  Lemma lv_created_minted n s X :
    MintAuth X -∗ lv_inv n s -∗ ⌜lv_created s ⊆ X⌝.
  Proof.
    iIntros "A (_ & _ & #M & _)". by iApply (minted_agree with "A M").
  Qed.

  Lemma lv_inv_wf n s : lv_inv n s -∗ ⌜lv_wf s⌝.
  Proof. by iIntros "(% & _)". Qed.

  Lemma lv_know_alive κs s (X : gset lt_atom) :
    X ⊆ lv_created s ∪ κs → X ## lv_dead s → X ⊆ lv_alive (lv_know κs s).
  Proof.
    move=> Hsub Hdisj x Hx. rewrite /lv_alive /lv_know /=.
    apply elem_of_difference. split; [by apply Hsub|]. set_solver.
  Qed.

  (** *** The borrow rules at a level

    Each is the corresponding [inner_*] rule read in the level's own
    coordinates, with the blocked atoms' tokens moved in and out as the
    rule blocks and unblocks.  [de ⊆ lv_created s] is what
    [de ⊆ alive ∪ dead] becomes under the change of variable. *)
  Lemma lv_unborrow_start n s outlives sn bl al de Px :
    (al ⊆ lv_alive s) → (de ⊆ lv_created s) → ¬(de ## lv_dead s) →
    (bl ## lv_blocked s) → (bl ⊆ lv_alive s) →
    (∀ k , k ∈ al → (bl, k) ∈ outlives) →
    lv_inv n s ∗ Outlives n.(bn_o) outlives
      ∗ OwnBorState n.(bn_bor) sn (Borrow al de) ∗ sinv_tok sn Px
      ∗ ([∗ set] x ∈ bl, Alive γlt x)
    ⊢ |=[box_wsat bor_sem]=>
    lv_inv n (lv_block bl s) ∗ Outlives n.(bn_o) outlives
      ∗ OwnBorState n.(bn_bor) sn (Unborrow bl al de) ∗ bor_sem Px.
  Proof.
    move=> Hal Hde Hded Hbl Hbla Ho.
    iIntros "((%Hwf & #Lb & #Mint & Inv & Blk) & Ou & Ob & #Sl & Bl)".
    iMod (inner_unborrow_start γlt n.(bn_bor) n.(bn_o) n.(bn_o)
      (lv_alive s) (lv_dead s) (lv_blocked s) outlives sn bl al de Px
      with "[$Inv $Ou $Ob $Sl]") as "(Inv & Ou & Ob & P)";
      [done|by apply sub_diff_union|done|done|done|done|].
    iModIntro. iSplitR "Ou Ob P"; last first.
    { iSplitL "Ou"; [iExact "Ou"|]. iSplitL "Ob"; [iExact "Ob"|iExact "P"]. }
    rewrite /lv_inv /lv_wf /lv_block /=. iSplitR; [by iPureIntro|].
    iFrame "Lb Mint". iSplitL "Inv"; [iExact "Inv"|].
    rewrite big_sepS_union; [|set_solver].
    iSplitL "Blk"; [iExact "Blk"|iExact "Bl"].
  Qed.

  Lemma lv_unborrow_end n s sn bl al de Px Qx :
    swell_set al → swell_set de →
    lv_inv n s ∗ OwnBorState n.(bn_bor) sn (Unborrow bl al de)
      ∗ sinv_tok sn Px
      ∗ (bor_sem Qx ∗ (∃ k , ⌜ k ∈ bl ⌝ ∗ Dead γlt k)
          ={↑NllftUsr ∪ ↑NllftUsr2}=∗ bor_sem Px)
      ∗ bor_sem Qx
    -∗ |=[box_wsat bor_sem]=> ∃ sn2,
      lv_inv n (lv_unblock bl s) ∗ OwnBorState n.(bn_bor) sn2 (Borrow al de)
      ∗ sinv_tok sn2 Qx ∗ ⌜bl ⊆ lv_blocked s⌝
      ∗ ([∗ set] x ∈ bl, Alive γlt x).
  Proof.
    move=> Hal Hde.
    iIntros "((%Hwf & #Lb & #Mint & Inv & Blk) & Ob & #Sl & Vs & Q)".
    iMod (inner_unborrow_end γlt n.(bn_bor) n.(bn_o) n.(bn_o)
      (lv_alive s) (lv_dead s) (lv_blocked s) sn bl al de Px Qx
      with "[$Inv $Ob $Sl $Vs $Q]") as (sn2) "(Inv & Ob & #Sl2 & %Hsub)";
      [done|done|].
    iModIntro. iExists sn2.
    rewrite {1}(union_difference_L bl (lv_blocked s)); [|done].
    rewrite big_sepS_union; [|set_solver]. iDestruct "Blk" as "[Bl Blk]".
    iSplitR "Ob Bl"; last first.
    { iSplitL "Ob"; [iExact "Ob"|]. iSplitR; [iExact "Sl2"|].
      iSplitR; [by iPureIntro|iExact "Bl"]. }
    rewrite /lv_inv /lv_wf /lv_unblock /=. iSplitR; [by iPureIntro|].
    iFrame "Lb Mint". iSplitL "Inv"; [iExact "Inv"|iExact "Blk"].
  Qed.

  Lemma lv_unborrow_end_at_same_idx n s sn bl al de Px :
    swell_set al → swell_set de →
    lv_inv n s ∗ OwnBorState n.(bn_bor) sn (Unborrow bl al de)
      ∗ sinv_tok sn Px ∗ bor_sem Px
    -∗ |=[box_wsat bor_sem]=>
      lv_inv n (lv_unblock bl s) ∗ OwnBorState n.(bn_bor) sn (Borrow al de)
      ∗ ⌜bl ⊆ lv_blocked s⌝ ∗ ([∗ set] x ∈ bl, Alive γlt x).
  Proof.
    move=> Hal Hde.
    iIntros "((%Hwf & #Lb & #Mint & Inv & Blk) & Ob & #Sl & P)".
    iMod (inner_unborrow_end_at_same_idx γlt n.(bn_bor) n.(bn_o) n.(bn_o)
      (lv_alive s) (lv_dead s) (lv_blocked s) sn bl al de Px
      with "[$Inv $Ob $Sl $P]") as "(Inv & Ob & %Hsub)"; [done|done|].
    iModIntro.
    rewrite {1}(union_difference_L bl (lv_blocked s)); [|done].
    rewrite big_sepS_union; [|set_solver]. iDestruct "Blk" as "[Bl Blk]".
    iSplitR "Ob Bl"; last first.
    { iSplitL "Ob"; [iExact "Ob"|]. iSplitR; [by iPureIntro|iExact "Bl"]. }
    rewrite /lv_inv /lv_wf /lv_unblock /=. iSplitR; [by iPureIntro|].
    iFrame "Lb Mint". iSplitL "Inv"; [iExact "Inv"|iExact "Blk"].
  Qed.

  Lemma lv_unborrow_atomic n s outlives sn bl al de Px :
    (al ⊆ lv_alive s) → ¬(de ## lv_dead s) →
    (∀ k , k ∈ al → (bl, k) ∈ outlives) →
    lv_inv n s ∗ Outlives n.(bn_o) outlives
      ∗ OwnBorState n.(bn_bor) sn (Borrow al de) ∗ sinv_tok sn Px
    -∗ |=[box_wsat bor_sem]=> bor_sem Px ∗ ∀ Qx,
      ((bor_sem Qx ∗ (∃ k , ⌜ k ∈ bl ⌝ ∗ Dead γlt k)
          ={↑NllftUsr ∪ ↑NllftUsr2}=∗ bor_sem Px) ∗ bor_sem Qx)
      -∗ |=[box_wsat bor_sem]=> ∃ sn2, lv_inv n s
        ∗ Outlives n.(bn_o) outlives
        ∗ OwnBorState n.(bn_bor) sn2 (Borrow al de) ∗ sinv_tok sn2 Qx.
  Proof.
    move=> Hal Hde Ho.
    iIntros "((%Hwf & #Lb & #Mint & Inv & Blk) & Ou & Ob & #Sl)".
    iMod (inner_unborrow_atomic γlt n.(bn_bor) n.(bn_o) n.(bn_o)
      (lv_alive s) (lv_dead s) (lv_blocked s) outlives sn bl al de Px
      with "[$Inv $Ou $Ob $Sl]") as "[P X]"; [done|done|done|].
    iModIntro. iFrame "P". iIntros (Qx) "H".
    iMod ("X" $! Qx with "H") as (sn2) "(Inv & Ou & Ob & #Sl2)".
    iModIntro. iExists sn2. iSplitR "Ou Ob"; last first.
    { iSplitL "Ou"; [iExact "Ou"|]. iSplitL "Ob"; [iExact "Ob"|iExact "Sl2"]. }
    rewrite /lv_inv. iSplitR; [by iPureIntro|]. iFrame "Lb Mint".
    iSplitL "Inv"; [iExact "Inv"|iExact "Blk"].
  Qed.

  Lemma lv_split n s sn al de Px Qx :
    lv_inv n s ∗ OwnBorState n.(bn_bor) sn (Borrow al de)
      ∗ sinv_tok sn (bor_sep Px Qx)
    ⊢ |=[box_wsat bor_sem]=> ∃ sn1 sn2, lv_inv n s
      ∗ OwnBorState n.(bn_bor) sn1 (Borrow al de)
      ∗ OwnBorState n.(bn_bor) sn2 (Borrow al de)
      ∗ sinv_tok sn1 Px ∗ sinv_tok sn2 Qx.
  Proof.
    iIntros "((%Hwf & #Lb & #Mint & Inv & Blk) & Ob & #Sl)".
    iMod (inner_split γlt n.(bn_bor) n.(bn_o) n.(bn_o)
      (lv_alive s) (lv_dead s) (lv_blocked s) sn al de Px Qx
      with "[$Inv $Ob $Sl]") as (sn1 sn2) "(Inv & Ob1 & Ob2 & #Sl1 & #Sl2)".
    iModIntro. iExists sn1, sn2. iSplitR "Ob1 Ob2"; last first.
    { iSplitL "Ob1"; [iExact "Ob1"|]. iSplitL "Ob2"; [iExact "Ob2"|].
      iSplitR; [iExact "Sl1"|iExact "Sl2"]. }
    rewrite /lv_inv. iSplitR; [by iPureIntro|]. iFrame "Lb Mint".
    iSplitL "Inv"; [iExact "Inv"|iExact "Blk"].
  Qed.

  Lemma lv_join n s sn1 sn2 al de Px Qx :
    swell_set de → (de ⊆ lv_created s) →
    lv_inv n s ∗ OwnBorState n.(bn_bor) sn1 (Borrow al de)
      ∗ OwnBorState n.(bn_bor) sn2 (Borrow al de)
      ∗ sinv_tok sn1 Px ∗ sinv_tok sn2 Qx
    ⊢ |=[box_wsat bor_sem]=> ∃ sn, lv_inv n s
      ∗ OwnBorState n.(bn_bor) sn (Borrow al de)
      ∗ sinv_tok sn (bor_sep Px Qx).
  Proof.
    move=> Hsw Hde.
    iIntros "((%Hwf & #Lb & #Mint & Inv & Blk) & Ob1 & Ob2 & #Sl1 & #Sl2)".
    iMod (inner_join γlt n.(bn_bor) n.(bn_o) n.(bn_o)
      (lv_alive s) (lv_dead s) (lv_blocked s) sn1 sn2 al de Px Qx
      with "[$Inv $Ob1 $Ob2 $Sl1 $Sl2]") as (sn) "(Inv & Ob & #Sl)";
      [done|by apply sub_diff_union|].
    iModIntro. iExists sn. iSplitR "Ob"; last first.
    { iSplitL "Ob"; [iExact "Ob"|iExact "Sl"]. }
    rewrite /lv_inv. iSplitR; [by iPureIntro|]. iFrame "Lb Mint".
    iSplitL "Inv"; [iExact "Inv"|iExact "Blk"].
  Qed.

  Lemma lv_iff n s sn al de Px Px' :
    lv_inv n s ∗ OwnBorState n.(bn_bor) sn (Borrow al de) ∗ sinv_tok sn Px
      ∗ □ (bor_sem Px ↔ bor_sem Px')
    ⊢ |=[box_wsat bor_sem]=> ∃ sn1, lv_inv n s
      ∗ OwnBorState n.(bn_bor) sn1 (Borrow al de) ∗ sinv_tok sn1 Px'.
  Proof.
    iIntros "((%Hwf & #Lb & #Mint & Inv & Blk) & Ob & #Sl & #Iff)".
    iMod (inner_iff γlt n.(bn_bor) n.(bn_o) n.(bn_o)
      (lv_alive s) (lv_dead s) (lv_blocked s) sn al de Px Px'
      with "[$Inv $Ob $Sl $Iff]") as (sn1) "(Inv & Ob & #Sl1)".
    iModIntro. iExists sn1. iSplitR "Ob"; last first.
    { iSplitL "Ob"; [iExact "Ob"|iExact "Sl1"]. }
    rewrite /lv_inv. iSplitR; [by iPureIntro|]. iFrame "Lb Mint".
    iSplitL "Inv"; [iExact "Inv"|iExact "Blk"].
  Qed.

  Lemma lv_reborrow n s Px sn al al' :
    swell_set al' → (al' ⊆ lv_created s) →
    lv_inv n s ∗ OwnBorState n.(bn_bor) sn (Borrow al {[default_dead]})
      ∗ sinv_tok sn Px
    -∗ |=[box_wsat bor_sem]=> ∃ sn1 sn2, lv_inv n s
      ∗ OwnBorState n.(bn_bor) sn1 (Borrow (al ∪ al') {[default_dead]})
      ∗ OwnBorState n.(bn_bor) sn2 (Borrow al al')
      ∗ sinv_tok sn1 Px ∗ sinv_tok sn2 Px.
  Proof.
    move=> Hsw Hal'.
    iIntros "((%Hwf & #Lb & #Mint & Inv & Blk) & Ob & #Sl)".
    iMod (inner_reborrow γlt n.(bn_bor) n.(bn_o) n.(bn_o)
      (lv_alive s) (lv_dead s) (lv_blocked s) Px sn al al'
      with "[$Inv $Ob $Sl]") as (sn1 sn2) "(Inv & Ob1 & Ob2 & #Sl1 & #Sl2)";
      [done|by apply sub_diff_union|].
    iModIntro. iExists sn1, sn2. iSplitR "Ob1 Ob2"; last first.
    { iSplitL "Ob1"; [iExact "Ob1"|]. iSplitL "Ob2"; [iExact "Ob2"|].
      iSplitR; [iExact "Sl1"|iExact "Sl2"]. }
    rewrite /lv_inv. iSplitR; [by iPureIntro|]. iFrame "Lb Mint".
    iSplitL "Inv"; [iExact "Inv"|iExact "Blk"].
  Qed.

  Lemma lv_borrow_create_empty n s Px :
    lv_inv n s ∗ bor_sem Px
    -∗ |=[box_wsat bor_sem]=> ∃ sn, lv_inv n s
      ∗ OwnBorState n.(bn_bor) sn (Borrow ∅ {[default_dead]})
      ∗ sinv_tok sn Px.
  Proof.
    iIntros "((%Hwf & #Lb & #Mint & Inv & Blk) & P)".
    iMod (inner_borrow_create_empty γlt n.(bn_bor) n.(bn_o) n.(bn_o)
      (lv_alive s) (lv_dead s) (lv_blocked s) Px
      with "[$Inv $P]") as (sn) "(Inv & Ob & #Sl)".
    iModIntro. iExists sn. iSplitR "Ob"; last first.
    { iSplitL "Ob"; [iExact "Ob"|iExact "Sl"]. }
    rewrite /lv_inv. iSplitR; [by iPureIntro|]. iFrame "Lb Mint".
    iSplitL "Inv"; [iExact "Inv"|iExact "Blk"].
  Qed.

  (** [inner_borrow_create] threads an [LtState] it never uses, so the
    level does not need the shared one to agree with it. *)
  Lemma lv_borrow_create n s lt Px :
    swell_set lt → (lt ⊆ lv_created s) →
    lv_inv n s ∗ bor_sem Px -∗ |=[box_wsat bor_sem]=> ∃ sn sn2, lv_inv n s
      ∗ OwnBorState n.(bn_bor) sn (Borrow lt {[default_dead]})
      ∗ OwnBorState n.(bn_bor) sn2 (Borrow ∅ lt)
      ∗ sinv_tok sn Px ∗ sinv_tok sn2 Px.
  Proof.
    move=> Hsw Hlt. iIntros "[Lv P]".
    iMod (lv_borrow_create_empty with "[$Lv $P]") as (sn) "(Lv & Ob & #Sl)".
    iMod (lv_reborrow n s Px sn ∅ lt with "[$Lv $Ob $Sl]")
      as (sn1 sn2) "(Lv & Ob1 & Ob2 & #Sl1 & #Sl2)"; [done|done|].
    iModIntro. iExists sn1, sn2.
    replace (∅ ∪ lt) with lt by set_solver.
    iSplitL "Lv"; [iExact "Lv"|]. iSplitL "Ob1"; [iExact "Ob1"|].
    iSplitL "Ob2"; [iExact "Ob2"|]. iSplitR; [iExact "Sl1"|iExact "Sl2"].
  Qed.

  Lemma lv_fake n s al de Qx :
    ¬(al ## lv_dead s) →
    lv_inv n s -∗ |=[box_wsat bor_sem]=> ∃ sn, lv_inv n s
      ∗ OwnBorState n.(bn_bor) sn (Borrow al de) ∗ sinv_tok sn Qx.
  Proof.
    move=> Hal. iIntros "(%Hwf & #Lb & #Mint & Inv & Blk)".
    iDestruct "Inv" as (mbs mprops Ptotal outlives)
      "[auth [Modulo [#DeadsLt [box [vs [#pures [#slices outlives]]]]]]]".
    iMod (inner_fake n.(bn_bor) (lv_alive s) (lv_dead s) (lv_blocked s)
      al de Qx with "Modulo") as (sn) "(Modulo & Ob & #Sl)"; [done|].
    iModIntro. iExists sn. iSplitR "Ob"; last first.
    { iSplitL "Ob"; [iExact "Ob"|iExact "Sl"]. }
    rewrite /lv_inv. iSplitR; [by iPureIntro|]. iFrame "Lb Mint".
    iSplitR "Blk"; [|iExact "Blk"].
    iExists mbs, mprops, Ptotal, outlives. iFrame. iFrame "#".
  Qed.

  (** ** The two phases, and why a level does not need them

    [outer_inv] exists because killing a lifetime in the shared logic
    has to close the [NllftG] mask between taking the [Dead] token and
    updating the borrows, so there is a moment when the two disagree and
    [Delayed] records it.  Nothing like that happens at a level: the
    kill is at the shared lifetime tokens, and the level's own update
    comes later, by [inner_catch_up_one], at whichever level the lender
    happens to hold.  So [lv_inv] is built from [inner_inv] directly,
    and these two lemmas say that costs nothing - while no kill is in
    flight the two invariants are the same thing. *)
  Lemma outer_inv_open γd n alive dead blocked :
    Delayed γd None -∗
    outer_inv (FML:=FML) γlt n.(bn_bor) n.(bn_o) γd alive dead blocked -∗
    Delayed γd None ∗ Delayed γd None ∗
      inner_inv (FML:=FML) γlt n.(bn_bor) n.(bn_o) alive dead blocked.
  Proof.
    iIntros "Del Inv". iDestruct "Inv" as (opt_k) "[D Inv]".
    iDestruct (delayed_agree with "[$D $Del]") as "%Heq". subst opt_k.
    iFrame.
  Qed.

  Lemma outer_inv_close γd n alive dead blocked :
    Delayed γd None -∗
    inner_inv (FML:=FML) γlt n.(bn_bor) n.(bn_o) alive dead blocked -∗
    outer_inv (FML:=FML) γlt n.(bn_bor) n.(bn_o) γd alive dead blocked.
  Proof. iIntros "Del Inv". iExists None. iFrame. Qed.

  (** A single level is the invariant the port has today, which is what
    makes step 4 of PLAN.md's order a substitution rather than a
    redesign. *)
  Lemma llft_lv_inv_single n s : lv_inv n s ⊢ llft_lv_inv [(n, s)].
  Proof. by rewrite /llft_lv_inv big_sepL_singleton. Qed.
End Levelled.

(** The whole file is closed under the global context - not even
  [Eq_rect_eq], which most of the development does use. *)
Print Assumptions inner_kill_lt_c.
Print Assumptions lv_catch_up_to_log.
Print Assumptions lv_catch_up_one.
Print Assumptions lv_borrow_ready.
Print Assumptions no_greedy_kill_order.
