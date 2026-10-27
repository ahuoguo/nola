(** * Ported from VerusBelt ([lifetime/lifetime_full.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), with the laters removed.

  The Leaf Lifetime Logic (LeLiLo), later-free.

  The one structural change relative to the original is how the ambient
  invariants are modelled.  Leaf puts the lifetime invariant into an Iris
  invariant at [↑Nmain] and the box into one at [↑Nbox], both inside [↑NllftG],
  and lifetime inclusion is a guard at [↑NllftG].  Here, following nola, the
  invariants become *world satisfactions* that are threaded explicitly:

    [llft_wsat = (WG ∗ box_wsat bor_sem ∗ llft_inv_main) ∗ llft_inv_other]

  where [WG] is the user's guarding world satisfaction (Leaf's [↑NllftG] minus
  the lifetime logic itself).  Lifetime inclusion is a guard at
  [llft_wsatG = WG ∗ box_wsat bor_sem ∗ llft_inv_main], which deliberately
  excludes [llft_inv_other] - that is where the inclusion guards themselves are
  stored, so excluding it is what breaks the definitional cycle that a
  later-free impredicative invariant would otherwise create. *)

From nola.verus_halt Require Import boxes own_and.
From nola.verus_halt.lifetime Require Import ra inv augment_outlives new_lt expire_lt
  iff join split reborrow unborrow unnest level.
From iris.base_logic.lib Require Import mono_list.
From nola.bi Require Import guard modw.
From nola.iris Require Export iprop sinv.
From nola.iris Require Import point guard.
Require Import stdpp.base.
Require Import stdpp.namespaces.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import excl_auth.
From iris.algebra Require Import auth gset.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import proofmode.
From iris.proofmode Require Import coq_tactics.
From iris.base_logic.lib Require Export invariants.
Import GuardNotation ModwNotation iPropAppNotation.

Class llft_logicGpreS Σ := {
  llft_logic_inG : ra.llft_logicGS Σ ;
  llft_boxG : boxG Σ ;
  (** The kill order.  A level's view of the dead set is a prefix of it;
    see [nola/verus_halt/lifetime/level.v]. *)
  llft_logG : mono_listG lt_atom Σ ;
  (** Which atoms have ever been minted.  A level's created set stays
    inside them, and that is a fact the shared invariant cannot state
    once there is one bookkeeping per level, so it is carried by a
    persistent witness instead. *)
  llft_mintG : inG Σ (authUR (gsetUR lt_atom)) ;
  (** How far a level's *outlives* relation has caught up.  The relation
    grows, and [llft_augment_outlives] may grow it while a level is not
    held, so a level's copy lags - and what it needs of the shared one is
    a bound, since [kill_run] and [outlives_consistent] are both antitone
    in the relation ([level.kill_run_anti]). *)
  llft_osubG : inG Σ (authUR (gsetUR (gset lt_atom * lt_atom)))
}.

Class llft_logicGS Σ := LlftLogicG {
  llft_in_preG : llft_logicGpreS Σ;

  (** The lifetime tokens' name.  [LtState], [Alive] and [Dead] live here,
    and it is the same for a whole run. *)
  llft_name : gname;
  d_name : gname;
  (** The kill order's name.  It is shared, like [llft_name]: a level
    replays this order, and carries a persistent witness of the prefix it
    has reached. *)
  log_name : gname;
  (** The minted atoms' name, shared for the same reason. *)
  mint_name : gname;
  (** A second half of the outlives relation, so that the main invariant
    can state the kill order's well-formedness - which mentions it - in
    one place.  [LlftBorNames]'s [o_name] has both its halves spoken
    for already, one by [inner_inv] and one by the client. *)
  oset_name : gname;
  (** The outlives relation's monotone authority: a level holds an
    [Osub] fragment of its own copy and the shared half holds the
    authority, which is what bounds a lagging level's relation. *)
  osub_name : gname;
}.
Global Existing Instance llft_in_preG.

(** ** The borrow bookkeeping's names, apart from the rest

  [AuthBorState], [OwnBorState] and [ModuloDead] live at [bor_name], and
  the outlives relation's client half at [o_name].  These used to be
  fields of [llft_logicGS], and [bor_name] used to be [llft_name] itself,
  because [LtRa]'s validity tied the two halves together ([w ⊆ d] in
  [lt_inv]).  That tie is gone ([lifetime/ra.v]'s split), and these two
  are *exactly* what varies with the execution level: one lifetime
  algebra, one kill order, one minted set - and one borrowing machinery
  per level.  So they are a class of their own, which a level
  instantiates ([typing/level_ctx.v]) while [llft_logicGS] stays shared
  for the whole run.

  It is a class rather than a section variable for the reason the rest of
  this file records about [LlftWG]: as a variable every lemma below would
  take it explicitly once the section closed, and a client could not even
  write [&{κ} Px]. *)
Class LlftBorNames (Σ : gFunctors) : Type := LlftBorNamesS {
  bor_name : gname;
  o_name : gname;
}.

Local Existing Instance llft_boxG.
Local Existing Instance llft_logic_inG.
Global Existing Instance llft_logG.
Global Existing Instance llft_mintG.
Global Existing Instance llft_osubG.

Definition llft_logicΣ : gFunctors := #[
  ra.llft_logicΣ ;
  boxΣ ;
  mono_listΣ lt_atom ;
  GFunctor (authUR (gsetUR lt_atom)) ;
  GFunctor (authUR (gsetUR (gset lt_atom * lt_atom)))
].

Global Instance subG_lt_logicΣ Σ : subG llft_logicΣ Σ → llft_logicGpreS Σ.
Proof. solve_inG. Qed.

(** The formula language must be able to express the content of a shared
  borrow: the borrowed formula, or the lifetime's death together with the
  cancellation token that reclaims it.  This is Leaf's
  [P ∨ (llft_dead_def' κ ∗ CCancel γc)]; it mentions no guard, so making it a
  formula creates no cycle. *)
Class ShrBorSem (FML : oFunctor) Σ `{!llft_logicGS Σ, !BorSem FML Σ} := {
  shr_fml : gset lt_atom → gname → FML $oi Σ → FML $oi Σ;
  shr_fml_sem κ γc Px :
    bor_sem (shr_fml κ γc Px) ⊣⊢
      bor_sem Px ∨ ((∃ k, ⌜k ∈ κ⌝ ∗ Dead llft_name k) ∗ CCancel γc);
}.

(** The shared-borrow ghost name and the user's guarding world satisfaction.

  These used to be section variables, which made *every* lemma below take them
  as two explicit arguments once the section closed - so a client could not
  even write [κ ⊑ κ'] without threading them.  As a class they are inferred
  instead. *)
Class LlftWG (Σ : gFunctors) : Type := LlftWGS {
  llft_shr_name : gname;
  llft_WG : iProp Σ;
  (** *** The worlds a *stored* guard has to work at

    A guard the lifetime logic keeps - a lifetime inclusion, an indexed
    borrow's, an outlives guard - is taken out again by whoever holds the
    world satisfaction at the time, and that need not be the world it was
    made at.  Two dimensions vary.  The *interpretation* does, which is
    why [st_incl] is already a family ([typing/ctx.v]); and the
    *execution level* does, which is what PLAN.md item 2 step 4 needs,
    since each level has its own borrows, box and shared-borrow family.

    So the logic does not fix the world its stored guards live at.  It
    takes an index type and the world at each index, and stores
    [∀ i, P &&{llft_Wat i}&&> Q].  Which indices exist is the client's
    business: [llft_Wix := unit] recovers the unlevelled, single
    interpretation logic, and the port instantiates it with the
    interpretations it already quantifies over.

    [llft_WG] stays, because the *ambient* world is still needed - a rule
    that opens a stored guard opens it at [llft_wsatG], and
    [LlftWHere] below is what says that world is among the family. *)
  llft_Wix : Type;
  (** What world [i] has *beyond* the ambient one.  A world of the
    family is the ambient [llft_wsatG] together with this; see
    [llft_Wat_ext].  Making the family upward closed this way is what
    the levels need and is not a convenience: a lifetime inclusion can
    be backed by a *shared borrow*, which lives in the ambient level's
    [shr_wsat], so a guard stored at one level is usable exactly at the
    worlds that still contain that level's machinery - the thesis's
    [∗_{k<j} Winv_k] for [j] above it.  It also makes every guard this
    file already proves at [llft_wsatG] a member of the family for
    free ([fguard_of_here]). *)
  llft_Wmore : llft_Wix → iProp Σ;
}.

Local Instance pers_dead2 `{!ra.llft_logicGS Σ} γlt k : Persistent (Dead γlt k).
Proof. apply own_core_persistent. unfold CoreId. trivial. Qed.

Definition log_sd (log : list lt_atom) : gset lt_atom :=
  {[default_dead]} ∪ list_to_set log.

(** The shared dead set is the kill order's, except for the atom
  currently being killed.  That one gap is what [Delayed] has always
  recorded: killing has to close the [NllftG] mask between taking
  [†κ] and settling the borrows, and in between the two disagree.
  Here the disagreement is between [sd] and the order, rather than
  between [sd] and a borrow invariant. *)
Definition pend_sd (pend : option (lt_atom * gset lt_atom)) : gset lt_atom :=
  from_option (λ p, {[p.1]}) ∅ pend.

Lemma log_sd_none log : log_sd log ∪ pend_sd None = log_sd log.
Proof. rewrite /pend_sd /=. set_solver. Qed.

Lemma not_disj_of (X D : gset lt_atom) x : x ∈ X → x ∈ D → ¬(X ## D).
Proof. set_solver. Qed.

Lemma sub_grow (sa sa' sd X : gset lt_atom) :
  sa ⊆ sa' → X ⊆ sa ∪ sd → X ⊆ sa' ∪ sd.
Proof. set_solver. Qed.
Lemma in_grow (sa sa' sd : gset lt_atom) x :
  sa ⊆ sa' → x ∈ sa ∪ sd → x ∈ sa' ∪ sd.
Proof. set_solver. Qed.
Lemma sub_l (sa sd X : gset lt_atom) : X ⊆ sa → X ⊆ sa ∪ sd.
Proof. set_solver. Qed.
Lemma in_l (sa sd : gset lt_atom) x : x ∈ sa → x ∈ sa ∪ sd.
Proof. set_solver. Qed.
Lemma notin_log (sa sd : gset lt_atom) log x :
  sa ∩ sd = ∅ → sd = log_sd log → x ∈ sa →
  x ∉ (list_to_set log : gset lt_atom).
Proof. rewrite /log_sd. set_solver. Qed.
Lemma sub_union3 (A B C D : gset lt_atom) :
  A ⊆ D → B ⊆ D → C ⊆ D → A ∪ (B ∪ C) ⊆ D.
Proof. set_solver. Qed.
Lemma sub_mid (A B C : gset lt_atom) : A ⊆ C ∪ (A ∪ B).
Proof. set_solver. Qed.
Lemma sub_mid2 (A B C : gset lt_atom) : B ⊆ C ∪ (A ∪ B).
Proof. set_solver. Qed.
Lemma inter_disj (X Y : gset lt_atom) : X ∩ Y = ∅ → X ## Y.
Proof. set_solver. Qed.
Lemma dd_not_disj (D : gset lt_atom) :
  default_dead ∈ D → ¬({[default_dead]} ## D).
Proof. set_solver. Qed.
Lemma dd_sub (D X : gset lt_atom) :
  default_dead ∈ D → D ⊆ X → {[default_dead]} ⊆ X.
Proof. set_solver. Qed.
Lemma log_sd_dd log : default_dead ∈ log_sd log.
Proof. rewrite /log_sd. set_solver. Qed.

Lemma disj_of_alive (X sa sd D : gset lt_atom) :
  X ⊆ sa → sa ∩ sd = ∅ → D ⊆ sd → X ## D.
Proof. set_solver. Qed.


Section LlftWsat.
  #[local] Set Default Proof Using "All".
  Context {Σ: gFunctors} {FML : oFunctor}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS_gen hlc Σ}.
  Context `{!sinvGS FML Σ, !BorSem FML Σ}.
  (** A second simple-invariant instance, holding the contents of shared
    borrows.  The box uses the ambient [sinvGS]; this one is separate.  It is
    introduced as a plain ghost name rather than a [Context] of class type, so
    that it does not become a typeclass instance and get picked up by the box. *)
  Context `{!LlftWG Σ}.
  Local Notation shr_name := llft_shr_name.
  Definition shrGS : sinvGS FML Σ := SinvGS FML Σ sinvGS_pre shr_name.
  Context `{!ShrBorSem FML Σ}.
  (** [unnest] needs the formula language to express borrow-state ownership. *)
  Context `{!LlftBorNames Σ, !BorStateFml bor_name}.
  (** The user's guarding world satisfaction, Leaf's [↑NllftG] minus the
    lifetime logic's own invariants. *)
  Local Notation WG := llft_WG.

  (*** Lifetime logic ***)

  (** A Lifetime κ is defined as a [gset nat]. *)

  Definition lft := gset nat.

  Global Instance llft_intersect : Meet lft := λ κ1 κ2, κ1 ∪ κ2.
  Definition llft_empty : lft := ∅.
  (* begin hide *)

  Local Definition llft_alive_def' (lt : gset lt_atom) : iProp Σ :=
    [∗ set] k ∈ lt , Alive llft_name k.
  Local Definition llft_dead_def' (lt : gset lt_atom) : iProp Σ :=
    ∃ k , ⌜ k ∈ lt ⌝ ∗ Dead llft_name k.

  Local Definition llft_alive_def (κ : lft) : iProp Σ :=
    [∗ set] k ∈ κ , Alive llft_name (LtAtomSwell k).
  Local Definition llft_dead_def (κ : lft) : iProp Σ :=
    ∃ k , ⌜ k ∈ κ ⌝ ∗ Dead llft_name (LtAtomSwell k).

  (** The borrow side's ghost names, collected because they are what
    varies with the execution level; the lifetime tokens' does not.  See
    [nola/verus_halt/lifetime/level.v]. *)
  Local Notation bn := (BorNames bor_name o_name).

  (** The main part of the lifetime invariant: Leaf's [↑Nmain].

    The borrow bookkeeping keeps its *own* view of the world - which
    atoms it has heard of, which it believes dead, which it is blocking
    on - and the two pure conjuncts here are the only thing relating that
    view to the shared [(sa, sd)].  With one bookkeeping per execution
    level the first of them weakens to "a prefix of the kill order" and
    the second to a fact about the outlives relation; everything else is
    already written in the level's own coordinates.

    [outer_inv]'s two phases are gone with it.  They existed because the
    shared kill had to close the [NllftG] mask between taking [†κ] and
    updating the borrows; the level's update is now a separate step
    ([level.lv_catch_up_one]), so [d_name] is vestigial. *)
  (** The shared half: everything that is not a level's.  Note the
    level's own conjunct is gone - the bookkeeping is allowed to lag
    behind the kill order, and [lv_inv] says only that its dead set is
    *some* prefix of that order.  That is what makes a level's piece a
    closed proposition, and hence what lets several of them be held
    separately as [∗_{k<j} Wbor_k].  A rule that needs a lifetime to be
    dead at the level catches it up first
    ([level.lv_catch_up_to_log]). *)
  (** The shared half: the lifetime tokens, the kill order, the minted
    atoms and the outlives relation's second copy.  Nothing here is a
    function of the execution level, and nothing here mentions a
    level's state - which is the point: with one bookkeeping per level
    this is the conjunct held *once*, beside the family. *)
  Definition llft_inv_shared_at (sa sd : gset lt_atom) (log : list lt_atom)
      (ol : outlives_set) (pend : option (lt_atom * gset lt_atom))
    : iProp Σ :=
      LtState llft_name sa sd
        ∗ llft_alive_def' sa
        ∗ mono_list_auth_own log_name (DfracOwn 1) log
        ∗ Outlives oset_name ol
        ∗ Delayed d_name pend
        ∗ ⌜sd = log_sd log ∪ pend_sd pend
            ∧ (∀ p , pend = Some p → p.2 = sa)
            ∧ kill_run {[default_dead]} ol log
            ∧ (∀ o , o ∈ ol → o.1 ⊆ sa ∪ sd ∧ o.2 ∈ sa ∪ sd)⌝
        ∗ MintAuth mint_name (sa ∪ sd).

  (** One level's half of the main invariant.  [lv_inv] is a closed
    proposition - see [level.v] - so this is the conjunct that becomes a
    list. *)
  Definition llft_bor_inv : iProp Σ :=
    ∃ s : lvState, lv_inv (FML:=FML) llft_name log_name mint_name bn s.

  (** The main invariant keeps its flat shape - every rule below
    destructures it - and the split is a lemma rather than the
    definition. *)
  Definition llft_inv_main_at (sa sd : gset lt_atom) (log : list lt_atom)
      (ol : outlives_set) (pend : option (lt_atom * gset lt_atom))
      (s : lvState) : iProp Σ :=
      LtState llft_name sa sd
        ∗ llft_alive_def' sa
        ∗ mono_list_auth_own log_name (DfracOwn 1) log
        ∗ Outlives oset_name ol
        ∗ Delayed d_name pend
        ∗ ⌜sd = log_sd log ∪ pend_sd pend
            ∧ (∀ p , pend = Some p → p.2 = sa)
            ∧ kill_run {[default_dead]} ol log
            ∧ (∀ o , o ∈ ol → o.1 ⊆ sa ∪ sd ∧ o.2 ∈ sa ∪ sd)⌝
        ∗ MintAuth mint_name (sa ∪ sd)
        ∗ lv_inv (FML:=FML) llft_name log_name mint_name bn s.

  Lemma llft_inv_main_at_split sa sd log ol pend s :
    llft_inv_main_at sa sd log ol pend s ⊣⊢
      llft_inv_shared_at sa sd log ol pend
        ∗ lv_inv (FML:=FML) llft_name log_name mint_name bn s.
  Proof.
    rewrite /llft_inv_main_at /llft_inv_shared_at. iSplit.
    - iIntros "(St & Al & Au & Ol & De & % & MA & Lv)".
      iFrame "St Al Au Ol De MA Lv". by iPureIntro.
    - iIntros "((St & Al & Au & Ol & De & % & MA) & Lv)".
      iFrame "St Al Au Ol De MA Lv". by iPureIntro.
  Qed.

  Definition llft_inv_main : iProp Σ :=
    ∃ (sa sd : gset lt_atom) (log : list lt_atom) (ol : outlives_set)
      (pend : option (lt_atom * gset lt_atom)) (s : lvState),
      llft_inv_main_at sa sd log ol pend s.

  Definition llft_inv_shared : iProp Σ :=
    ∃ (sa sd : gset lt_atom) (log : list lt_atom) (ol : outlives_set)
      (pend : option (lt_atom * gset lt_atom)),
      llft_inv_shared_at sa sd log ol pend.

  (** The split the family needs: the shared conjunct and the level's
    are independent existentials, so the main invariant is their
    separating conjunction and nothing has to be re-proved to see it. *)
  Lemma llft_inv_main_split : llft_inv_main ⊣⊢ llft_inv_shared ∗ llft_bor_inv.
  Proof.
    rewrite /llft_inv_main /llft_inv_shared /llft_bor_inv. iSplit.
    - iIntros "(%sa & %sd & %log & %ol & %pend & %s & M)".
      rewrite llft_inv_main_at_split. iDestruct "M" as "[Sh Lv]".
      iSplitL "Sh".
      { iExists sa, sd, log, ol, pend. iExact "Sh". }
      iExists s. iExact "Lv".
    - iIntros "[(%sa & %sd & %log & %ol & %pend & Sh) (%s & Lv)]".
      iExists sa, sd, log, ol, pend, s. rewrite llft_inv_main_at_split.
      iFrame "Sh Lv".
  Qed.

  (** Small set facts used where the context is large enough that
    [set_solver] is not worth running. *)
  Local Lemma log_sd_app log k : log_sd (log ++ [k]) = log_sd log ∪ {[k]}.
  Proof. rewrite /log_sd list_to_set_app_L /=. set_solver. Qed.

  Local Lemma in_shrunk (X Y : gset lt_atom) k x :
    x ∈ X ∪ Y → x ∈ (X ∖ {[k]}) ∪ (Y ∪ {[k]}).
  Proof.
    move=> Hx. destruct (decide (x = k)) as [->|Hne].
    { apply elem_of_union. right. apply elem_of_union. right.
      by apply elem_of_singleton. }
    apply elem_of_union in Hx as [Hx|Hx].
    - apply elem_of_union. left. apply elem_of_difference.
      split; [done|]. by rewrite elem_of_singleton.
    - apply elem_of_union. right. apply elem_of_union. by left.
  Qed.

  Local Lemma sub_shrunk (Z X Y : gset lt_atom) k :
    Z ⊆ X ∪ Y → Z ⊆ (X ∖ {[k]}) ∪ (Y ∪ {[k]}).
  Proof. move=> H x /H. apply in_shrunk. Qed.

  Local Lemma LtState_alive_dead_disj_aux (sa sd : gset lt_atom) k :
    sa ∩ sd = ∅ → k ∈ sa → k ∈ sd → False.
  Proof. set_solver. Qed.

  Local Lemma kill_cond_of (other sa sd : gset lt_atom) k :
    other ⊆ sa ∪ sd → ¬(other ⊆ sa ∖ {[k]}) → ¬(other ## sd ∪ {[k]}).
  Proof.
    move=> Hsub Hnot Hdisj. apply Hnot=> x Hx.
    have Hx' := Hsub _ Hx. apply elem_of_difference. split.
    - apply elem_of_union in Hx' as [?|Hx']; [done|].
      exfalso. apply (Hdisj x); [done|]. apply elem_of_union. by left.
    - rewrite elem_of_singleton=> ?. subst x. apply (Hdisj k); [done|].
      apply elem_of_union. right. by apply elem_of_singleton.
  Qed.

  (** Killing an atom leaves the minted set alone, and hands out the
    witness for the atom that just died. *)
  Local Lemma mint_kill (sa sd : gset lt_atom) k :
    k ∈ sa → MintAuth mint_name (sa ∪ sd) ==∗
    MintAuth mint_name ((sa ∖ {[k]}) ∪ (sd ∪ {[k]}))
      ∗ Minted mint_name {[k]}.
  Proof.
    move=> Hk. iIntros "A".
    iMod (minted_get mint_name (sa ∪ sd) with "A") as "[A #M]".
    replace ((sa ∖ {[k]}) ∪ (sd ∪ {[k]})) with (sa ∪ sd)
      by (apply set_eq=> x; destruct (decide (x = k)); set_solver).
    iModIntro. iFrame "A". iApply (minted_mono with "M"). set_solver.
  Qed.

  Local Lemma LtState_deads (L : list lt_atom) sa sd :
    (∀ k, k ∈ L → k ∈ sd) →
    LtState llft_name sa sd ⊢ [∗ list] k ∈ L, Dead llft_name k.
  Proof.
    move=> HL. induction L as [|k L IH]; [by iIntros|].
    iIntros "St". rewrite big_sepL_cons.
    iDestruct (LtState_entails_Dead llft_name k sa sd with "St") as "#D".
    { apply HL. set_solver. }
    iFrame "D". iApply IH; [|iExact "St"]. move=> x Hx. apply HL. set_solver.
  Qed.

  (** Storage for shared borrows. *)
  Definition shr_wsat : iProp Σ :=
    sinv_wsat (sinvGS0:=shrGS) (λ _ Px, bor_sem Px).

  (** The world satisfaction that lifetime inclusion guards live at. *)
  Definition llft_wsatG : iProp Σ :=
    WG ∗ shr_wsat ∗ box_wsat bor_sem ∗ llft_inv_main.

  (** The ambient world is one of the family's.

    This is the only thing the logic needs of [llft_Wat] besides its
    existence, and it is what lets a rule *use* a stored guard: the
    guard holds at every index, in particular at this one, and there it
    is a guard at [llft_wsatG], which is what the rule is holding.
    Producing a stored guard is the other direction and has no
    obligation here - a producer proves its guard at an arbitrary
    index, which every producer in this file already does, since each
    of them is [guard_intro] or [guard_trans] over a step that mentions
    no world satisfaction at all.

    It is not an obligation on the client: rather than ask that
    [llft_wsatG] be among [llft_Wat]'s worlds, the family is *extended*
    by it.  [None] is the ambient world and [Some i] is the client's
    [i], so [fguard_here] below is an instantiation and nothing has to
    be proved - which also keeps the whole thing out of the section's
    [Context], where [Set Default Proof Using "All"] would have forced
    every later lemma to carry it. *)
  Definition llft_Wat_ext (i : option llft_Wix) : iProp Σ :=
    match i with None => llft_wsatG | Some i => llft_wsatG ∗ llft_Wmore i end.

  (** *** A *stored* guard: one at every world of the family

    This is the shape every guard the lifetime logic keeps has: a
    lifetime inclusion, an indexed borrow's, an outlives guard.  Its
    combinators are the ordinary ones, each applied pointwise, which is
    all that is needed because every producer in this file is
    [guard_intro] or [guard_trans] over a step that mentions no world
    satisfaction at all. *)
  Definition fguard (P Q : iProp Σ) : iProp Σ :=
    ∀ i, P &&{llft_Wat_ext i}&&> Q.

  Local Notation "P &&{*}&&> Q" := (fguard P Q)
    (at level 99, Q at level 200, format "P  &&{*}&&>  Q") : bi_scope.

  #[export] Instance fguard_persistent {P Q} : Persistent (P &&{*}&&> Q).
  Proof. exact _. Qed.
  #[export] Instance fguard_ne {n} :
    Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) fguard.
  Proof. solve_proper. Qed.
  #[export] Instance fguard_proper : Proper ((≡) ==> (≡) ==> (≡)) fguard.
  Proof. solve_proper. Qed.

  Lemma fguard_intro {P Q} : □ (P -∗ Q ∗ (Q -∗ P)) ⊢ P &&{*}&&> Q.
  Proof. iIntros "#H" (i). by iApply guard_intro. Qed.

  Lemma fguard_refl {P} : ⊢ P &&{*}&&> P.
  Proof. iIntros (i). iApply guard_refl. Qed.

  Lemma fguard_trans {P Q R} :
    (P &&{*}&&> Q) -∗ (Q &&{*}&&> R) -∗ P &&{*}&&> R.
  Proof.
    iIntros "#A #B" (i). iApply (guard_trans with "[] []");
      [iApply "A"|iApply "B"].
  Qed.

  (** Taking a stored guard out at the ambient world.  This is the only
    thing [LlftWHere] is for. *)
  Lemma fguard_here {P Q} : (P &&{*}&&> Q) ⊢ P &&{llft_wsatG}&&> Q.
  Proof. iIntros "G". iApply ("G" $! None). Qed.

  (** ...and the converse, which is why the family costs so little: a
    guard at the ambient world is a guard at every world that contains
    it ([guard_wsat_sep]), and every world of the family does. *)
  Lemma fguard_of_here {P Q} : (P &&{llft_wsatG}&&> Q) ⊢ P &&{*}&&> Q.
  Proof.
    iIntros "#G" (i). destruct i as [i|]; [|iExact "G"].
    by iApply guard_wsat_sep.
  Qed.

  (** *** One execution level's half of it

    Everything in [llft_wsatG] that holds a formula or names a borrow -
    the shared-borrow family, the box, and the bookkeeping - against
    everything that does not.  The thesis's [∗_{k<j} Winv_k] is a list
    of the first; the second is held once, beside the list.

    What makes the split possible is that [llft_bor_inv] is *closed*:
    since the decoupling it mentions no [sa], no [sd] and no [log] of
    the shared half, only the level's own [lvState] - which is why
    several of them can be held apart. *)
  Definition llft_bor_wsat : iProp Σ :=
    shr_wsat ∗ box_wsat bor_sem ∗ llft_bor_inv.

  Lemma llft_wsatG_split :
    llft_wsatG ⊣⊢ (WG ∗ llft_inv_shared) ∗ llft_bor_wsat.
  Proof.
    rewrite /llft_wsatG /llft_bor_wsat llft_inv_main_split. iSplit.
    - iIntros "(WG & Shr & Box & Sh & Lv)". iFrame "WG Sh Shr Box Lv".
    - iIntros "((WG & Sh) & Shr & Box & Lv)". iFrame "WG Shr Box Sh Lv".
  Qed.

  #[export] Instance wsat_incl_llft_wsatG_bor :
    WsatIncl llft_wsatG llft_bor_wsat (WG ∗ llft_inv_shared).
  Proof. rewrite /WsatIncl llft_wsatG_split. by rewrite comm. Qed.

  (** Definitions of the lifetime tokens. *)

  Definition llft_alive (κ : lft) : iProp Σ := llft_alive_def κ.
  Definition llft_dead (κ : lft) : iProp Σ := llft_dead_def κ.

  Local Notation "@[ κ ]" := (llft_alive κ) (format "@[ κ ]") : bi_scope.
  Local Notation "[† κ ]" := (llft_dead κ) (format "[† κ ]") : bi_scope.

  (** LeLiLo-Incl-Guard.

    A *family*, one guard at every world the client offers, because an
    inclusion is stored - in an indexed borrow, and through
    [llft_augment_outlives] in the outlives guards - and taken out again
    at whatever world its holder has.  See [LlftWG]'s [llft_Wat].

    Nothing is lost by the strengthening: every inclusion this file
    builds is structural (see [llftl_incl_sub]) and so is proved at an
    arbitrary world already. *)
  Definition llft_incl (κ1 κ2 : lft) : iProp Σ :=
      @[ κ1 ] &&{*}&&> @[ κ2 ].

  Local Infix "⊑" := llft_incl (at level 70) : bi_scope.

  (** The rest of the lifetime invariant: Leaf's [↑NllftO].  Note that the
    stored inclusion guards are at [llft_wsatG], which does not contain this. *)
  (** One level's copy of the outlives relation, and the guards that go
    with it.  It is *not* the shared relation: the shared one grows
    whenever [llftl_augment_outlives] runs, which a body at execution
    level [j] cannot do to the levels at or above [j].  So a level's
    copy lags, bounded by the [Osub] fragment it carries - and that is
    all it needs, because [kill_run] and [outlives_consistent] are both
    antitone in the relation ([level.kill_run_anti]). *)
  (** The guards that make the outlives relation mean something: if
    [(κ, k)] is in it then [k] cannot die while [κ] lives.  They are
    keyed to the *shared* relation, and they are the one thing in the
    shared half that is still a function of the execution level - the
    world satisfaction they are taken over is a level's [llft_wsatG].
    Making them a family over levels, the way [st_incl] is already a
    family over interpretations, is what the levelled version needs;
    see the note on [llft_inv_other_split]. *)
  Definition llft_outlives_guards_at (ol : outlives_set) : iProp Σ :=
    ∀ o, ⌜o ∈ ol⌝ -∗
      (llft_alive_def' o.1 &&{*}&&> Alive llft_name o.2).

  (** One level's copy of the outlives relation.  It is *not* the shared
    one: the shared relation grows whenever [llftl_augment_outlives]
    runs, which a body at execution level [j] cannot do to the levels at
    or above [j].  So a level's copy lags, bounded by the [Osub]
    fragment it carries - and that bound is all it needs, because
    [kill_run] and [outlives_consistent] are both antitone in the
    relation ([level.kill_run_anti]). *)
  Definition llft_outlives (olk : outlives_set) : iProp Σ :=
    Outlives o_name olk ∗ Osub osub_name olk.

  (** Flat, because every rule below destructures it; the split into a
    shared half and a level's is [llft_inv_other_split]. *)
  Definition llft_inv_other : iProp Σ :=
    ∃ outlives olk, Outlives oset_name outlives ∗ Delayed d_name None
      ∗ OsetAuth osub_name outlives ∗ llft_outlives_guards_at outlives
      ∗ llft_outlives olk.

  Definition llft_other_shared : iProp Σ :=
    ∃ outlives, Outlives oset_name outlives ∗ Delayed d_name None
      ∗ OsetAuth osub_name outlives ∗ llft_outlives_guards_at outlives.
  Definition llft_bor_other : iProp Σ := ∃ olk, llft_outlives olk.

  (** [llft_bor_other] is closed - it is the level's half of the
    outlives bookkeeping and mentions nothing shared.
    [llft_other_shared] is held once, and everything in it but
    [llft_outlives_guards_at] is level-independent. *)
  Lemma llft_inv_other_split :
    llft_inv_other ⊣⊢ llft_other_shared ∗ llft_bor_other.
  Proof.
    rewrite /llft_inv_other /llft_other_shared /llft_bor_other. iSplit.
    - iIntros "(%outlives & %olk & Os & De & OA & #Og & O)".
      iSplitR "O"; [|by iExists olk]. iExists outlives.
      iFrame "Os De OA". iExact "Og".
    - iIntros "[(%outlives & Os & De & OA & #Og) (%olk & O)]".
      iExists outlives, olk. iFrame "Os De OA O". iExact "Og".
  Qed.

  (** The full world satisfaction of the lifetime logic. *)
  Definition llft_wsat : iProp Σ := llft_wsatG ∗ llft_inv_other.

  #[export] Instance wsat_incl_llft_wsat :
    WsatIncl llft_wsat llft_wsatG llft_inv_other.
  Proof. done. Qed.
  #[export] Instance wsat_incl_llft_wsatG_G :
    WsatIncl llft_wsatG WG (shr_wsat ∗ box_wsat bor_sem ∗ llft_inv_main).
  Proof. done. Qed.
  #[export] Instance wsat_incl_llft_wsatG_shr :
    WsatIncl llft_wsatG shr_wsat (WG ∗ box_wsat bor_sem ∗ llft_inv_main).
  Proof. rewrite /WsatIncl /llft_wsatG. iSplit; iIntros "(a&b&c&d)"; iFrame. Qed.
  #[export] Instance wsat_incl_llft_wsatG_box :
    WsatIncl llft_wsatG (box_wsat bor_sem) (WG ∗ shr_wsat ∗ llft_inv_main).
  Proof. rewrite /WsatIncl /llft_wsatG. iSplit; iIntros "(a&b&c&d)"; iFrame. Qed.
  #[export] Instance wsat_incl_llft_wsatG_main :
    WsatIncl llft_wsatG llft_inv_main (WG ∗ shr_wsat ∗ box_wsat bor_sem).
  Proof. rewrite /WsatIncl /llft_wsatG. iSplit; iIntros "(a&b&c&d)"; iFrame. Qed.

  (** The context is no longer an invariant assertion: its content lives in the
    world satisfaction.  It is kept so that the rule statements still read like
    the original ones. *)
  Definition llft_ctx : iProp Σ := True.

  Local Lemma set_map_inter (κ1 κ2: lft) :
      set_map LtAtomSwell (κ1 ⊓ κ2)
        = set_map LtAtomSwell κ1 ∪ (set_map LtAtomSwell κ2 : gset lt_atom).
  Proof. apply set_eq. apply set_map_union. Qed.

  Local Lemma set_map_singleton (x: nat) :
        (set_map LtAtomSwell ({[ x ]} : gset nat) : gset lt_atom)
          = ({[ LtAtomSwell x ]} : gset lt_atom).
  Proof. apply set_eq. apply set_map_singleton. Qed.

  Local Lemma big_sepS_set_map (κ: lft) :
      (([∗ set] k ∈ (set_map LtAtomSwell κ) , Alive llft_name k) ⊣⊢
      ([∗ set] k ∈ κ , Alive llft_name (LtAtomSwell k)))%I.
  Proof.
    induction κ as [|x T ? IH] using set_ind_L.
      - do 2 rewrite big_sepS_empty. done.
      - rewrite set_map_inter.
        do 2 (rewrite big_sepS_union; last by set_solver).
        rewrite set_map_singleton. do 2 (rewrite big_sepS_singleton).
        rewrite IH. done.
  Qed.

  Local Lemma dead_def_set_map (κ: lft) :
        (∃ k : nat, ⌜k ∈ κ⌝ ∗ Dead llft_name (LtAtomSwell k)) ⊣⊢
        (∃ k : lt_atom, ⌜k ∈ (set_map LtAtomSwell κ : gset lt_atom)⌝
          ∗ Dead llft_name k).
  Proof.
    iSplit.
      - iDestruct 1 as (k) "[%Hin Dead]". iExists (LtAtomSwell k). iFrame.
        iPureIntro. set_solver.
      - iDestruct 1 as (k) "[%Hin Dead]". rewrite elem_of_map in Hin.
        destruct Hin as [x [Heq Hin]]. subst k. iExists x. iFrame. done.
  Qed.

  Local Lemma swell_set_set_map (κ: gset nat) :
      swell_set (set_map LtAtomSwell κ).
  Proof.
      intros x. rewrite elem_of_map. intros [k [Heq Hin]]. rewrite Heq. done.
  Qed.

  Local Definition atom_unwrap (atom: lt_atom) : nat :=
    match atom with LtAtomSwell k => k | LtAtomNotSwell k => k end.

  Local Lemma atom_not_in_swell (k: nat) (s : gset lt_atom) :
      k ∉ (set_map atom_unwrap s : gset nat) →
      LtAtomSwell k ∉ s.
  Proof. intros Ha Hb. apply Ha. rewrite elem_of_map. exists (LtAtomSwell k); done. Qed.

  Local Lemma atom_not_in_not_swell (k: nat) (s : gset lt_atom) :
      k ∉ (set_map atom_unwrap s : gset nat) →
      LtAtomNotSwell k ∉ s.
  Proof. intros Ha Hb. apply Ha. rewrite elem_of_map. exists (LtAtomNotSwell k); done. Qed.

  (* end hide *)

  Local Ltac unseal := rewrite /llft_alive /llft_alive_def
    /llft_dead /llft_dead_def /llft_ctx.



  (** Lifetime tokens and their algebra *)

  Global Instance pers_llft_ctx : Persistent llft_ctx.
  Proof. unseal. typeclasses eauto. Qed.

  Global Instance pers_llft_dead κ : Persistent ([† κ ]).
  Proof. unseal. typeclasses eauto. Qed.

  Global Instance timeless_llft_alive κ : Timeless (@[ κ ]).
  Proof. unseal. typeclasses eauto. Qed.

  Global Instance timeless_llft_dead κ : Timeless ([† κ ]).
  Proof. unseal. typeclasses eauto. Qed.

  #[export] Instance point_prop_llft_alive κ : point_prop (@[ κ ])%I.
  Proof.
    unseal. apply point_prop_big_sepS=> ??. apply point_prop_own.
  Qed.

  (* begin hide *)
  Lemma llftl_not_own_end_unswell κ : llft_alive_def' κ -∗ llft_dead_def' κ -∗ False.
  Proof.
    iIntros "A D". iDestruct "D" as (k) "[%kk D]".
    iDestruct ((big_sepS_delete _ _ k) with "A") as "[A _]". { trivial. }
    iApply (lt_alive_dead_false llft_name k). iSplit; iFrame.
  Qed.
  (* end hide *)

  (** LeLiLo-Not-Own-End *)
  Lemma llftl_not_own_end κ : @[ κ ] -∗ [† κ ] -∗ False.
  Proof.
    unseal. iIntros "A D". iDestruct "D" as (k) "[%kk D]".
    iDestruct ((big_sepS_delete _ _ k) with "A") as "[A _]". { trivial. }
    iApply (lt_alive_dead_false llft_name (LtAtomSwell k)). iSplit; iFrame.
  Qed.

  Lemma llftl_not_own_end_and κ : @[ κ ] ∧ [† κ ] ⊢ False.
  Proof.
    unseal. iIntros "AD". rewrite bi.and_exist_l. iDestruct "AD" as (k) "AD".
    iApply (lt_alive_dead_false llft_name (LtAtomSwell k)).
    iAssert (⌜k ∈ κ⌝)%I as "%kk". { iDestruct "AD" as "[_ [D _]]".  iFrame. }
    iSplit; iFrame.
    { iDestruct "AD" as "[A _]".
      iDestruct ((big_sepS_delete _ _ k) with "A") as "[A _]". { trivial. } iFrame. }
    { iDestruct "AD" as "[_ [_ D]]". iFrame. }
  Qed.
  Local Lemma llft_alive_subset_split (κ sa : gset lt_atom) :
    κ ⊆ sa → llft_alive_def' sa ⊣⊢ llft_alive_def' κ ∗ llft_alive_def' (sa ∖ κ).
  Proof.
    intros Hsub. rewrite /llft_alive_def'.
    rewrite -big_sepS_union; last by set_solver.
    by rewrite -union_difference_L.
  Qed.

  (* begin hide *)
  Lemma llftl_incl_dead_implies_dead_unswell E κ κ' :
      ⊢ llft_ctx -∗ (llft_alive_def' κ &&{llft_wsatG}&&> llft_alive_def' κ') -∗
        llft_dead_def' κ' -∗ |=[llft_wsatG]{E}=> llft_dead_def' κ.
  Proof.
    iIntros "_ #incl #dead".
    (* The guard to the right-hand side becomes a guard to [False]. *)
    iAssert (llft_alive_def' κ &&{llft_wsatG}&&> False)%I as "#G2".
    { iApply (guard_trans with "incl"). iApply guard_intro. iIntros "!> A".
      iExFalso. iApply (llftl_not_own_end_unswell κ' with "A dead"). }
    (* The main invariant is a conjunct of the world satisfaction. *)
    iDestruct (guard_wsat_out (W:=llft_wsatG) (W':=llft_inv_main) (P:=True%I)) as "#ctx".
    iAssert (True &&{llft_wsatG}&&>
      ((∃ sa sd log ol pd s, ⌜ κ ⊆ sa ⌝ ∗ llft_inv_main_at sa sd log ol pd s)
       ∨ (∃ sa sd log ol pd s, ⌜ ¬(κ ⊆ sa) ⌝
            ∗ llft_inv_main_at sa sd log ol pd s)))%I
      as "#ctx'".
    { iApply (guard_trans with "ctx"). iApply guard_intro. iIntros "!> T".
      iSplitL.
      - iDestruct "T" as (sa sd log ol pd s) "T".
        have h : Decision (κ ⊆ sa) by solve_decision. destruct h as [h|n].
        + iLeft. iExists sa, sd, log, ol, pd, s. iFrame. by iPureIntro.
        + iRight. iExists sa, sd, log, ol, pd, s. iFrame. by iPureIntro.
      - iIntros "[T|T]".
        + iDestruct "T" as (sa sd log ol pd s) "[_ T]".
          by iExists sa, sd, log, ol, pd, s.
        + iDestruct "T" as (sa sd log ol pd s) "[_ T]".
          by iExists sa, sd, log, ol, pd, s. }
    (* The left disjunct guards [False], so it can be cancelled. *)
    iAssert ((∃ sa sd log ol pd s, ⌜ κ ⊆ sa ⌝
          ∗ llft_inv_main_at sa sd log ol pd s)
        &&{llft_wsatG}&&> False)%I as "#GF".
    { iApply (guard_trans with "[] G2"). iApply guard_intro.
      iIntros "!> T".
      iDestruct "T" as (sa sd log ol pd s) "[%ksa [state [alive rest]]]".
      rewrite (llft_alive_subset_split κ sa ksa).
      iDestruct "alive" as "[alive1 alive2]". iFrame "alive1". iIntros "alive1".
      iExists sa, sd, log, ol, pd, s. iSplitR; first by iPureIntro.
      iFrame "state".
      iSplitL "alive1 alive2".
      { rewrite (llft_alive_subset_split κ sa ksa). iFrame. }
      iFrame "rest". }
    iDestruct (guard_or_false with "ctx' GF") as "#G3".
    (* Now open the guard and produce the dead token. *)
    rewrite /modw. iIntros "Wsat".
    iDestruct (guard_acc with "G3 [//] Wsat") as "[J back]".
    iDestruct "J" as (sa sd log ol pd s)
      "[%k_sa [State [alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]]".
    destruct pure as [Hsd [Hpd [Hrun Howf]]].
    have the_k := not_subset_eq_get κ sa k_sa. destruct the_k as [k [k_in k_not_in]].
    have h : Decision (k ∈ sd) by solve_decision. destruct h as [h|n].
    - iDestruct (LtState_entails_Dead llft_name k sa sd with "State") as "#deadk";
        first done.
      iDestruct ("back" with "[State alive Auth Ol Del MA Lv]") as "[Wsat _]".
      { iExists sa, sd, log, ol, pd, s. iFrame. by iPureIntro. }
      iFrame "Wsat". iModIntro. iExists k. iFrame "deadk". by iPureIntro.
    - (* weird technicality: if [k] was never made alive in the first place,
        first create it, then immediately kill it.  It goes on the kill
        order like any other death, and the condition for that step is
        vacuous: nothing outlives an atom that did not exist.  The borrow
        bookkeeping is left behind and catches up later. *)
      iMod (new_lt llft_name k sa sd with "State") as "[State [al1 al2]]";
        [done|done|].
      iMod (kill_lt llft_name k (sa ∪ {[ k ]}) sd with "[State al1 al2]")
        as "[State #deadk]". { iFrame. }
      iMod (mono_list_auth_own_update_app [k] with "Auth") as "[Auth _]".
      iMod (minted_alloc_set mint_name (sa ∪ sd) {[k]} with "MA") as "[MA _]".
      replace ((sa ∪ sd) ∪ {[k]}) with (sa ∪ (sd ∪ {[k]})) by set_solver.
      (* The bookkeeping is not told: it is allowed to lag, and it picks
        this entry up with the rest when a lender next catches it up. *)
      replace (((sa ∪ {[k]}) ∖ {[k]})) with sa by set_solver.
      iDestruct ("back" with "[State alive Auth Ol Del MA Lv]") as "[Wsat _]".
      { iExists sa, (sd ∪ {[k]}), (log ++ [k]), ol, pd, s.
        iSplitR; [by iPureIntro|].
        iFrame "State alive Auth Ol Del MA Lv". iPureIntro.
        split. { rewrite log_sd_app Hsd. set_solver. }
        split; [done|].
        split.
        { apply kill_run_app. split; [done|]. simpl. split.
          { rewrite /log_sd in Hsd. set_solver. }
          split; [|done]. move=> other Hin.
          have Ho := Howf _ Hin. simpl in Ho. set_solver. }
        move=> o Ho. have [H1 H2] := Howf o Ho. split; set_solver. }
      iFrame "Wsat". iModIntro. iExists k. iFrame "deadk". by iPureIntro.
  Qed.
  (* end hide *)

  (** LeLiLo-Incl-Dead *)
  Lemma llftl_incl_dead_implies_dead E κ κ' :
      ⊢ llft_ctx -∗ κ ⊑ κ' -∗ [† κ' ] -∗ |=[llft_wsatG]{E}=> [† κ ].
  Proof.
      iIntros "#LFT #Incl #A".
      iDestruct (llftl_incl_dead_implies_dead_unswell E
        (set_map LtAtomSwell κ) (set_map LtAtomSwell κ') with "LFT [] []") as "J".
       - rewrite /llft_alive /llft_alive_def /llft_alive_def'.
         do 2 rewrite big_sepS_set_map.
         iApply fguard_here. rewrite /llft_incl /llft_alive
           /llft_alive_def. iExact "Incl".
       - rewrite /llft_dead /llft_dead_def /llft_dead_def'.
         iDestruct "A" as (k) "[%Hin Dead]". iExists (LtAtomSwell k).
         iFrame "Dead". iPureIntro. rewrite elem_of_map. exists k; split; trivial.
       - rewrite /modw. iIntros "W". iMod ("J" with "W") as "[$ J2]". iModIntro.
         rewrite /llft_dead /llft_dead_def /llft_dead_def'.
         iDestruct "J2" as (k) "[%Hin Dead]".
         rewrite elem_of_map in Hin. destruct Hin as [k0 [Heq Hin]]. subst k.
         iExists k0. iFrame "Dead". done.
  Qed.

  (** Inclusion of lifetimes is *structural*: it holds whenever the right
    lifetime's atoms are among the left one's.  Every inclusion the typing
    layer creates from nothing is of this shape, which matters because such
    an inclusion is storable - the proof mentions no interpretation. *)
  (** At an *arbitrary* world, since nothing about the world is used -
    which is what makes the family versions below immediate, and what
    the typing layer needs when it is proving a guard at some other
    interpretation's world rather than at the ambient one. *)
  Lemma llftl_incl_sub_at {W} κ κ' : κ' ⊆ κ → ⊢ @[κ] &&{W}&&> @[κ'].
  Proof.
    move=> Hsub. iApply guard_intro. unseal.
    iIntros "!> Alive". replace κ with (κ' ∪ (κ ∖ κ')).
    - rewrite big_sepS_union; [|set_solver].
      iDestruct "Alive" as "[A1 A2]". iFrame "A1". iIntros "A3". iFrame.
    - symmetry. by apply union_difference_L.
  Qed.

  Lemma llftl_intersect_incl_l_at {W} κ κ' : ⊢ @[κ ⊓ κ'] &&{W}&&> @[κ].
  Proof. apply llftl_incl_sub_at. unfold meet, llft_intersect. set_solver. Qed.

  Lemma llftl_intersect_incl_r_at {W} κ κ' : ⊢ @[κ' ⊓ κ] &&{W}&&> @[κ].
  Proof. apply llftl_incl_sub_at. unfold meet, llft_intersect. set_solver. Qed.

  Lemma llftl_incl_sub κ κ' : κ' ⊆ κ → ⊢ κ ⊑ κ'.
  Proof. move=> ?. iIntros (i). by iApply llftl_incl_sub_at. Qed.

  Lemma llftl_intersect_incl_l κ κ' : ⊢ (κ ⊓ κ') ⊑ κ.
  Proof. apply llftl_incl_sub. unfold meet, llft_intersect. set_solver. Qed.

  Lemma llftl_intersect_incl_r κ κ' : ⊢ (κ' ⊓ κ) ⊑ κ.
  Proof. apply llftl_incl_sub. unfold meet, llft_intersect. set_solver. Qed.

  Lemma llftl_incl_trans κ κ' κ'' : ⊢ κ ⊑ κ' -∗ κ' ⊑ κ'' -∗ κ ⊑ κ''.
  Proof. iIntros "#A #B". iApply (fguard_trans with "A B"). Qed.

  Lemma llftl_incl_glb_at {W} κ κ' κ'' :
      (@[κ] &&{W}&&> @[κ']) -∗ (@[κ] &&{W}&&> @[κ'']) -∗
      @[κ] &&{W}&&> @[κ' ⊓ κ''].
  Proof.
    iIntros "#A #B".
    iApply (guard_and (S:=@[κ' ⊓ κ'']%I) with "A B").
    unseal. do 3 rewrite -big_sepS_set_map.
    rewrite set_map_inter. apply alive_and_bigSepS.
  Qed.

  Lemma llftl_incl_glb κ κ' κ'' :
      κ ⊑ κ' -∗ κ ⊑ κ'' -∗ κ ⊑ (κ' ⊓ κ'').
  Proof.
    iIntros "#A #B" (i). iApply (llftl_incl_glb_at with "[] []");
      [iApply "A"|iApply "B"].
  Qed.

  Lemma llftl_incl_weaken_lhs_l κ κ' κ'' :
      κ ⊑ κ' ⊢ (κ ⊓ κ'') ⊑ κ'.
  Proof.
    iIntros "#incl". iApply (fguard_trans with "[] incl").
    iApply llftl_intersect_incl_l.
  Qed.

  Lemma llftl_incl_weaken_lhs_r κ κ' κ'' :
      κ ⊑ κ' ⊢ (κ'' ⊓ κ) ⊑ κ'.
  Proof.
      replace (κ'' ⊓ κ) with (κ ⊓ κ'')
        by (unfold meet, llft_intersect; set_solver).
      apply llftl_incl_weaken_lhs_l.
  Qed.

  Lemma llftl_tok_inter_l κ κ' :
      @[ κ ⊓ κ' ] ⊢ @[ κ ].
  Proof.
    iIntros "Alive".
    replace (κ ∪ κ') with (κ ∪ ((κ ∪ κ') ∖ κ)).
    - unseal. rewrite big_sepS_union.
      + iDestruct "Alive" as "[A1 A2]". iFrame "A1".
      + set_solver.
    - symmetry. apply union_difference_L. set_solver.
  Qed.

  Lemma llftl_tok_inter_r κ κ' :
      @[ κ ⊓ κ' ] ⊢ @[ κ' ].
  Proof.
    replace (κ ⊓ κ') with (κ' ⊓ κ).
    - apply llftl_tok_inter_l.
    - unfold meet, llft_intersect. set_solver.
  Qed.

  (** LeLiLo-Tok-Inter *)
  Lemma llftl_tok_inter_and κ κ' :
      @[ κ ⊓ κ' ] ⊣⊢ @[ κ ] ∧ @[ κ' ].
  Proof.
    iIntros. iSplit.
    - iIntros "t". iSplit.
      + iApply llftl_tok_inter_l. iFrame "t".
      + iApply llftl_tok_inter_r. iFrame "t".
    - unseal. iIntros.
      do 3 rewrite -big_sepS_set_map.
      rewrite set_map_inter.
      iApply alive_and_bigSepS. iFrame.
  Qed.

  (** LeLiLo-End-Inter *)
  Lemma llftl_end_inter κ κ' :
      [† κ ⊓ κ'] ⊣⊢ [† κ ] ∨ [† κ' ].
  Proof.
    unseal. iIntros. iSplit.
    - iIntros "t".  iDestruct "t" as (k) "[%kin t]".
      unfold meet, llft_intersect in kin. rewrite elem_of_union in kin.
      destruct kin as [h|h].
      + iLeft. iExists k. iFrame "t". iPureIntro. trivial.
      + iRight. iExists k. iFrame "t". iPureIntro. trivial.
    - iIntros "t". iDestruct "t" as "[h|h]".
      + iDestruct "h" as (k) "[%kin t]".
        iExists k. iFrame "t". iPureIntro. unfold meet, llft_intersect. set_solver.
      + iDestruct "h" as (k) "[%kin t]".
        iExists k. iFrame "t". iPureIntro. unfold meet, llft_intersect. set_solver.
  Qed.

  Lemma llftl_tok_unit : ⊢ @[ llft_empty ].
  Proof.
    unseal. unfold llft_empty. rewrite big_sepS_empty. iIntros. done.
  Qed.

  Lemma llftl_end_unit : [† llft_empty ] ⊢ False.
  Proof.
    unseal. unfold llft_empty.
    iIntros "t". iDestruct "t" as (k) "[%p t]".
    rewrite elem_of_empty in p. contradiction.
  Qed.

  (** Allocating a new lifetime token *)

  (* begin hide *)
  Local Lemma llftl_begin_maybe_swell' (b: bool) :
      llft_ctx ⊢ |=[llft_wsat]=>
        ∃ k, Alive llft_name (if b then LtAtomSwell k else LtAtomNotSwell k).
  Proof.
      iIntros "_". rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (ol2 olk)
        "[Ol2 [Delayed [OA [#Oguards [Ostate #Osb]]]]]".
      iDestruct "Main" as (sa sd log ol pd s)
        "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
      iDestruct (delayed_agree with "[$Del $Delayed]") as "%Hpdeq". subst pd.
      destruct pure as [Hsd [Hpd [Hrun Howf]]].
      assert (∃ k , (if b then LtAtomSwell k else LtAtomNotSwell k) ∉ (sa ∪ sd))
        as Fres. {
          exists (fresh (set_map atom_unwrap (sa ∪ sd) : gset nat)).
          destruct b.
           - apply atom_not_in_swell. apply is_fresh.
           - apply atom_not_in_not_swell. apply is_fresh.
      }
      destruct Fres as [k Fres].
      (* The borrow bookkeeping is not told about the new lifetime.  It
        learns of one when a borrow of it is first made there
        ([level.lv_borrow_ready]), which is all any rule needs. *)
      iMod (new_lt llft_name (if b then LtAtomSwell k else LtAtomNotSwell k) sa sd
        with "State") as "[State [A1 A2]]"; [set_solver|set_solver|].
      iMod (minted_alloc_set mint_name (sa ∪ sd)
        {[(if b then LtAtomSwell k else LtAtomNotSwell k)]} with "MA")
        as "[MA _]".
      replace ((sa ∪ sd)
          ∪ {[(if b then LtAtomSwell k else LtAtomNotSwell k)]})
        with ((sa ∪ {[(if b then LtAtomSwell k else LtAtomNotSwell k)]}) ∪ sd)
        by set_solver.
      iModIntro.
      iSplitR "A2"; last by iExists k; iFrame "A2".
      iFrame "WG Shr Box".
      iSplitR "Ol2 Delayed OA Ostate"; last by
        iExists ol2, olk; iFrame "Ol2 Delayed OA Oguards Ostate Osb".
      iExists (sa ∪ {[ (if b then LtAtomSwell k else LtAtomNotSwell k) ]}),
        sd, log, ol, None, s.
      iFrame "State Auth Ol Del MA Lv".
      iSplitL "Alive A1".
      { rewrite /llft_alive_def'.
        replace ((sa ∪ {[ (if b then LtAtomSwell k else LtAtomNotSwell k) ]}))
          with (({[ (if b then LtAtomSwell k else LtAtomNotSwell k) ]} ∪ sa))
          by set_solver.
        rewrite big_sepS_insert; last by set_solver. iFrame. }
      iPureIntro. split; [done|]. split; [done|]. split; [done|].
      move=> o Ho. have [H1 H2] := Howf o Ho. split.
      - apply (sub_grow sa); [apply union_subseteq_l|done].
      - apply (in_grow sa); [apply union_subseteq_l|done].
  Qed.
  (* end hide *)

  Lemma llftl_begin' :
      llft_ctx ⊢ |=[llft_wsat]=> ∃ κ, @[ κ ] ∗ ⌜κ ≠ llft_empty⌝.
  Proof.
      iIntros "LFT". iMod (llftl_begin_maybe_swell' true with "LFT") as (k) "S".
      unseal. iModIntro. iExists ({[ k ]}).
      rewrite big_sepS_singleton. iFrame. iPureIntro. set_solver.
  Qed.

  (* begin hide *)
  Local Lemma llftl_end_maybe_swell' (k: lt_atom) :
      llft_ctx -∗ Alive llft_name k -∗
      |=[llft_wsat]{↑NllftUsr ∪ ↑NllftUsr2}=> Dead llft_name k.
  Proof.
      iIntros "_ token". rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives1 olk)
        "[Ol2 [Delayed [OA [#O2 [O1 #Osb]]]]]".
      iDestruct (osub_agree osub_name olk outlives1 with "OA Osb")
        as "%Hkksub".
      iDestruct "Main" as (sa1 sd1 log ol pd s)
        "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
      iDestruct (outlives_agree with "[$Ol $Ol2]") as "%Heqol". subst ol.
      iDestruct (delayed_agree with "[$Del $Delayed]") as "%Heqpd". subst pd.
      destruct pure as [Hsd [_ [Hrun Howf]]].
      rewrite /log_sd /pend_sd /= right_id_L in Hsd.
      iAssert (⌜k ∈ sa1⌝)%I as "%k_sa1".
      { iApply (lt_state_alive llft_name k sa1 sd1). iSplit.
        { iFrame "State". } iFrame "token". }
      iDestruct (LtState_disjoint llft_name _ _ with "State") as "%Hdisj".
      rewrite {1}/llft_alive_def' (big_sepS_delete _ sa1 k); last done.
      iDestruct "Alive" as "[token2 Alive]".
      iMod (kill_lt llft_name k sa1 sd1 with "[State token token2]")
        as "[State #dead]". { iFrame. }
      iMod (mint_kill sa1 sd1 k with "MA") as "[MA #Mk]"; [done|].
      destruct (decide (filter (λ (o: (gset lt_atom * lt_atom)) ,
          o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1 = ∅)).
      {
        assert (∀ other , (other, k) ∈ outlives1 → ¬(other ⊆ sa1 ∖ {[k]}))
          as Houtlives.
        { intros other. intros Hin Hdisj2.
          assert ((other,  k) ∈ filter (λ o : gset lt_atom * lt_atom,
            o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1) as X.
          { rewrite elem_of_filter. set_solver. } rewrite e in X. set_solver. }
        (* The death goes on the kill order, and the bookkeeping is
          brought level with the whole order - which also absorbs
          whatever it had been lagging by. *)
        have Hrun' : kill_run {[default_dead]} outlives1 (log ++ [k]).
        { apply kill_run_app. split; [done|]. simpl. split.
          { rewrite -Hsd. move=> Hk. apply (LtState_alive_dead_disj_aux
              sa1 sd1 k); [done|done|done]. }
          split; [|done]. move=> other Hin.
          rewrite -Hsd. apply (kill_cond_of other sa1 sd1 k).
          { have Hwf := Howf _ Hin. by destruct Hwf. }
          { by apply Houtlives. } }
        have Hsd' : sd1 ∪ {[k]} = log_sd (log ++ [k]) ∪ pend_sd None.
        { rewrite /pend_sd /= right_id_L log_sd_app /log_sd -Hsd. done. }
        iMod (mono_list_auth_own_update_app [k] with "Auth") as "[Auth #Lbk]".
        iMod (minted_get mint_name ((sa1 ∖ {[k]}) ∪ (sd1 ∪ {[k]}))
          with "MA") as "[MA #Mall]".
        iDestruct (LtState_deads (log ++ [k]) (sa1 ∖ {[k]}) (sd1 ∪ {[k]})
          with "State") as "#Ds".
        { move=> x Hx. rewrite Hsd'. rewrite /log_sd /pend_sd /= right_id_L.
          rewrite elem_of_union. right. by apply elem_of_list_to_set. }
        (* The level replays the shared order with its *own* relation,
          which may be smaller - [kill_run] is antitone, and [Osub] is
          what says it is smaller. *)
        have Hrunk : kill_run {[default_dead]} olk (log ++ [k]).
        { apply (kill_run_anti _ outlives1); [exact Hkksub|exact Hrun']. }
        iDestruct (lv_catch_up_to_log llft_name log_name mint_name bn s
          olk (log ++ [k]) (DfracOwn 1) Hrunk with "Auth [] Ds [$Lv $O1]")
          as "X".
        { iApply (minted_mono with "Mall"). rewrite Hsd'.
          rewrite /log_sd /pend_sd /= right_id_L. set_solver. }
        iMod ("X" with "Box") as "[Box [Auth X]]".
        iDestruct "X" as (s') "[%Hlog' [Lv O1]]".
        iModIntro. iFrame "WG Shr Box dead".
        iSplitR "Ol2 Delayed OA O1"; last by
          iExists outlives1, olk; iFrame "Ol2 Delayed OA O2 O1 Osb".
        iExists (sa1 ∖ {[k]}), (sd1 ∪ {[k]}), (log ++ [k]), outlives1, None, s'.
        iFrame "State Alive Auth Ol Del MA Lv". iPureIntro.
        split; [done|]. split; [done|]. split; [done|].
        move=> o Ho. have Hwf := Howf _ Ho. split.
        - apply sub_shrunk. by destruct Hwf.
        - apply in_shrunk. by destruct Hwf.
      }
      (* case: something violates the outlives relation. derive a
        contradiction.  The shared dead set now runs one atom ahead of the
        kill order, which is what [Delayed] records. *)
      assert (∃ (x : gset lt_atom * lt_atom) , x ∈ filter
        (λ o : gset lt_atom * lt_atom, o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1)
        as Hex_x. { apply set_choose_L; trivial. }
      destruct Hex_x as [[oalive odead] Hex].
      rewrite elem_of_filter in Hex. simpl in Hex.
      destruct Hex as [[Hex1 Hex2] Hex3]. subst odead.
      iMod (delayed_update d_name None None (Some (k, sa1 ∖ {[k]}))
        with "[$Del $Delayed]") as "[Del Delayed]".
      iDestruct ("O2" $! ((oalive, k)) with "[]") as "#Oguard".
      { iPureIntro; trivial. }
      iDestruct (llftl_incl_dead_implies_dead_unswell
        (↑NllftUsr ∪ ↑NllftUsr2) oalive {[k]} with "[] [] []") as "OdeadUpd".
      { done. }
      { simpl. rewrite /llft_alive_def' big_sepS_singleton.
        iApply fguard_here. iExact "Oguard". }
      { rewrite /llft_dead_def'. iExists k. iFrame "dead". iPureIntro. set_solver. }
      iMod ("OdeadUpd" with "[WG Shr Box State Alive Auth Ol Del MA Lv]")
        as "[WsatG #Odead]".
      { rewrite /llft_wsatG. iFrame "WG Shr Box".
        iExists (sa1 ∖ {[k]}), (sd1 ∪ {[k]}), log, outlives1,
          (Some (k, sa1 ∖ {[k]})), s.
        iFrame "State Alive Auth Ol Del MA Lv". iPureIntro.
        split. { rewrite /pend_sd /= /log_sd -Hsd. done. }
        split. { by move=> p [= <-]. }
        split; [done|].
        move=> o Ho. have Hwf := Howf _ Ho. split.
        - apply sub_shrunk. by destruct Hwf.
        - apply in_shrunk. by destruct Hwf. }
      iDestruct "WsatG" as "[WG [Shr [Box Main]]]".
      iDestruct "Main" as (sa2 sd2 log2 ol2 pd2 s2)
        "[State [Alive [Auth [Ol [Del [%pure2 [MA2 Lv]]]]]]]".
      iDestruct (delayed_agree with "[$Del $Delayed]") as "%Dagree".
      subst pd2.
      destruct pure2 as [_ [Hpd2 _]]. have Hsa2 := Hpd2 _ eq_refl. simpl in Hsa2.
      subst sa2.
      iDestruct (big_sepS_subseteq _ _ oalive with "Alive") as "Alive";
        first done.
      iExFalso. iApply (llftl_not_own_end_unswell oalive with "[Alive] Odead").
      { rewrite /llft_alive_def'. iFrame "Alive". }
  Qed.
  (* end hide *)

  Lemma llftl_end' κ :
      κ ≠ llft_empty →
      llft_ctx -∗ @[ κ ] -∗ |=[llft_wsat]{↑NllftUsr ∪ ↑NllftUsr2}=> [† κ ].
  Proof.
      intros Hnotempty.
      assert (∃ k, k ∈ κ) as Hex_k. { apply set_choose_L; trivial. }
      destruct Hex_k as [k Hin_k].
      iIntros "LFT A".
      iMod (llftl_end_maybe_swell' (LtAtomSwell k) with "LFT [A]") as "J".
        - unseal. rewrite (big_sepS_delete _ _ k); last by trivial.
          iDestruct "A" as "[$ _]".
        - iModIntro. unseal. iExists k. iSplit; done.
  Qed.

  (** LeLiLo-Begin *)
  Lemma llftl_begin :
      llft_ctx ⊢ |=[llft_wsat]=> ∃ κ, @[ κ ] ∗
        □ (@[ κ ] -∗ |=[llft_wsat]{↑NllftUsr ∪ ↑NllftUsr2}=> [† κ ]).
  Proof.
    iIntros "#ctx".
    iMod (llftl_begin' with "ctx") as (κ) "[Alive %nonemp]".
    iModIntro. iExists κ. iFrame "Alive". iModIntro.
    iApply llftl_end'; done.
  Qed.

  (** Shared borrows *)

  Local Lemma shr_fml_sem_1 κ γc Px :
    bor_sem (shr_fml κ γc Px) ⊢ bor_sem Px ∨ (llft_dead_def' κ ∗ CCancel γc).
  Proof. apply bi.equiv_entails_1_1, shr_fml_sem. Qed.
  Local Lemma shr_fml_sem_2 κ γc Px :
    bor_sem Px ∨ (llft_dead_def' κ ∗ CCancel γc) ⊢ bor_sem (shr_fml κ γc Px).
  Proof. apply bi.equiv_entails_1_2, shr_fml_sem. Qed.

  (* begin hide *)
  (** The guard a shared borrow's token yields.  It is built from the token
    alone - no linear resource is consumed - so the same proof replays at
    *every* interpretation, which is what lets the guard be stored. *)
  Lemma llftl_shr_tok_guard κ γc sn (Px : FML $oi Σ) :
    sinv_tok (sinvGS0:=shrGS) sn (shr_fml κ γc Px) ⊢
      llft_alive_def' κ &&{llft_wsatG}&&> bor_sem Px.
  Proof.
    iIntros "#tok".
    iDestruct (sinv_tok_guard (sinvGS0:=shrGS) (sm := λ _ Qx, bor_sem Qx)
      with "tok") as "#Tguard".
    rewrite -/shr_wsat.
    iDestruct (guard_wsat_incl (W:=llft_wsatG) with "Tguard") as "#Tguard'".
    iAssert (llft_alive_def' κ &&{llft_wsatG}&&>
      bor_sem (shr_fml κ γc Px))%I as "#G".
    { iApply (guard_trans with "[] Tguard'"). iApply guard_true. }
    iAssert (bor_sem (shr_fml κ γc Px) &&{llft_wsatG}&&>
      ((llft_dead_def' κ ∗ CCancel γc) ∨ bor_sem Px))%I as "#Gswap".
    { iApply guard_intro. iIntros "!> Q".
      iDestruct (shr_fml_sem_1 with "Q") as "[P|D]".
      - iSplitL "P"; first by iRight. iIntros "X". iApply shr_fml_sem_2.
        iDestruct "X" as "[D|P]"; [by iRight|by iLeft].
      - iSplitL "D"; first by iLeft. iIntros "X". iApply shr_fml_sem_2.
        iDestruct "X" as "[D|P]"; [by iRight|by iLeft]. }
    iDestruct (guard_trans with "G Gswap") as "#Gor".
    iApply (guard_cancel_or (Q:=llft_alive_def' κ)
      (R:=(llft_dead_def' κ ∗ CCancel γc)%I) (S:=bor_sem Px) with "[] Gor").
    { iIntros "t".
      iAssert (llft_dead_def' κ) as "#D". { iDestruct "t" as "[_ [$ _]]". }
      iApply (llftl_not_own_end_unswell κ with "[t] D").
      { iDestruct "t"  as "[$ _]". } }
    { iApply guard_refl. }
  Qed.

  (* begin hide *)
  Local Lemma llftl_borrow_shared_alloc κ (Px : FML $oi Σ) :
      bor_sem Px -∗ |=[llft_wsatG]=> ∃ γc sn,
        sinv_tok (sinvGS0:=shrGS) sn (shr_fml κ γc Px) ∗
        (llft_dead_def' κ -∗ |=[llft_wsatG]=> bor_sem Px).
  Proof.
    iIntros "P". iMod new_cancel as (γc) "c1".
    rewrite {1}/modw /llft_wsatG. iIntros "[WG [Shr Rest]]".
    iDestruct (sinv_tok_alloc_suspend (sinvGS0:=shrGS)
      (sm := λ _ Qx, bor_sem Qx) (shr_fml κ γc Px) with "Shr") as (I) "Alloc".
    iMod ("Alloc" $! (fresh I) with "[]") as "[#tok Shr]".
    { iPureIntro. apply is_fresh. }
    iDestruct ("Shr" with "[P]") as "Shr".
    { iApply shr_fml_sem_2. by iLeft. }
    iModIntro. iFrame "WG Shr Rest". iExists γc, (fresh I). iFrame "tok".
    iIntros "#deadk". rewrite /modw /llft_wsatG.
    iIntros "[WG [Shr Rest]]".
    iDestruct (sinv_tok_acc (sm := λ _ Qx, bor_sem Qx) with "tok Shr")
      as "[J K]".
    iDestruct (shr_fml_sem_1 with "J") as "[P|[_ c2]]".
    + iDestruct ("K" with "[c1]") as "Shr".
      { iApply shr_fml_sem_2. iRight. iFrame "deadk c1". }
      iModIntro. by iFrame.
    + iDestruct (cancel_cancel_false γc with "[c1 c2]") as "J".
      { iFrame. } iExFalso. iFrame "J".
  Qed.

  Local Lemma llftl_borrow_shared_maybe_swell κ (Px : FML $oi Σ) :
      bor_sem Px -∗ |=[llft_wsatG]=>
        (llft_alive_def' κ &&{llft_wsatG}&&> bor_sem Px)
        ∗ (llft_dead_def' κ -∗ |=[llft_wsatG]=> bor_sem Px).
  Proof.
    iIntros "P W".
    iMod (llftl_borrow_shared_alloc κ Px with "P W")
      as "[W (%γc & %sn & #tok & Back)]".
    iModIntro. iFrame "W Back". by iApply llftl_shr_tok_guard.
  Qed.
  (* end hide *)

  (** LeLiLo-Shr-Borrow *)
  Lemma llftl_borrow_shared κ (Px : FML $oi Σ) :
      bor_sem Px -∗ |=[llft_wsatG]=>
        (@[ κ ] &&{llft_wsatG}&&> bor_sem Px)
        ∗ ([† κ ] -∗ |=[llft_wsatG]=> bor_sem Px).
  Proof.
      unseal. rewrite -big_sepS_set_map dead_def_set_map.
      apply (llftl_borrow_shared_maybe_swell (set_map LtAtomSwell κ)).
  Qed.

  (** The same, keeping the token: the guard it yields holds at every
    interpretation, the reclamation only at this one. *)
  Lemma llftl_borrow_shared_tok κ (Px : FML $oi Σ) :
      bor_sem Px -∗ |=[llft_wsatG]=> ∃ γc sn,
        sinv_tok (sinvGS0:=shrGS) sn
          (shr_fml (set_map LtAtomSwell κ) γc Px) ∗
        ([† κ ] -∗ |=[llft_wsatG]=> bor_sem Px).
  Proof.
    iIntros "P W".
    iMod (llftl_borrow_shared_alloc (set_map LtAtomSwell κ) Px with "P W")
      as "[$ (%γc & %sn & #tok & Back)]".
    iModIntro. iExists γc, sn. iFrame "tok". iIntros "#d".
    iApply "Back". unseal. by rewrite dead_def_set_map.
  Qed.
  Lemma llftl_shr_tok_guard_alive κ γc sn (Px : FML $oi Σ) :
      sinv_tok (sinvGS0:=shrGS) sn (shr_fml (set_map LtAtomSwell κ) γc Px) ⊢
        @[κ] &&{llft_wsatG}&&> bor_sem Px.
  Proof.
    iIntros "#tok". iDestruct (llftl_shr_tok_guard with "tok") as "#g".
    unseal. rewrite /llft_alive_def' -big_sepS_set_map. iApply "g".
  Qed.

  (** LeLiLo-Shr-Pers *)
  Lemma llftl_borrow_shared_persistent κ (Px : FML $oi Σ) :
      Persistent (@[ κ ] &&{llft_wsatG}&&> bor_sem Px).
  Proof. typeclasses eauto. Qed.

End LlftWsat.

Notation "@[ κ ]" := (llft_alive κ) (format "@[ κ ]") : bi_scope.
Notation "[† κ ]" := (llft_dead κ) (format "[† κ ]") : bi_scope.
Infix "⊑" := llft_incl (at level 70) : bi_scope.

(** ** A storable lifetime inclusion and a storable semantic alteration

  A full borrow

    [∃ sn κ', κ ⊑ κ' ∗ (∃ Px', □ (bor_sem Px' ↔ bor_sem Px) ∗ sinv_tok sn Px')
       ∗ OwnBorState …]

  mentions the interpretation twice, and in a way that does not transport to
  another one: [κ ⊑ κ'] is a guard over [llft_wsatG], which contains
  [box_wsat bor_sem], and the [↔] is the borrow's semantic alteration.  That
  is why a full borrow cannot be stored in a formula - see
  [nola/verus_halt/typing/README.md].

  Neither is a thing the lifetime logic *inspects*: the inclusion is only ever
  composed ([guard_trans], [llftl_incl_glb]) and eliminated into a guard, and
  the alteration is only ever composed and eliminated into the [↔].  So both
  become parameters.  The intended instance interprets each at *every*
  interpretation at once, which is what makes a borrow storable:

    [st_incl κ κ' := □ ∀ δ, @[κ] &&{verus_halt_WGuard_at δ}&&> @[κ']]
    [st_iff Px Qx := □ ∀ δ, ⟦ Px ⟧ᶜ(δ) ∗-∗ ⟦ Qx ⟧ᶜ(δ)]

  Over *every* [δ] and not just the good ones: "good" is [Deriv], [Deriv]
  is defined from [Jsem], and both of these sit inside a judgment's
  semantics, so restricting the quantifier would close that cycle.  See
  [nola/verus_halt/typing/inst.v].

  The closure properties live in [StBor], which does not mention the
  interpretation; the two elimination rules live in [StBorSem], which does,
  and which a model instantiates once per interpretation. *)
Class StBor (FML : oFunctor) (Σ : gFunctors) : Type := STBOR {
  st_incl : lft → lft → iProp Σ;
  st_iff : FML $oi Σ → FML $oi Σ → iProp Σ;
  #[global] st_incl_persistent :: ∀ κ κ', Persistent (st_incl κ κ');
  #[global] st_iff_persistent :: ∀ Px Qx, Persistent (st_iff Px Qx);
  #[global] st_iff_ne :: NonExpansive2 st_iff;
  st_incl_refl {κ} : ⊢ st_incl κ κ;
  st_incl_trans {κ κ' κ''} :
    st_incl κ κ' -∗ st_incl κ' κ'' -∗ st_incl κ κ'';
  st_incl_meet_l {κ κ'} : ⊢ st_incl (κ ⊓ κ') κ;
  st_incl_meet_r {κ κ'} : ⊢ st_incl (κ' ⊓ κ) κ;
  st_incl_glb {κ κ' κ''} :
    st_incl κ κ' -∗ st_incl κ κ'' -∗ st_incl κ (κ' ⊓ κ'');
  st_iff_refl {Px} : ⊢ st_iff Px Px;
  st_iff_sym {Px Qx} : st_iff Px Qx -∗ st_iff Qx Px;
  st_iff_trans {Px Qx Rx} : st_iff Px Qx -∗ st_iff Qx Rx -∗ st_iff Px Rx;
}.

Section LlftLogic.
  #[local] Set Default Proof Using "All".
  Context {Σ: gFunctors} {FML : oFunctor}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS_gen hlc Σ}.
  Context `{!sinvGS FML Σ, !BorSem FML Σ}.
  (** A second simple-invariant instance, holding the contents of shared
    borrows.  The box uses the ambient [sinvGS]; this one is separate.  It is
    introduced as a plain ghost name rather than a [Context] of class type, so
    that it does not become a typeclass instance and get picked up by the box. *)
  Context `{!LlftWG Σ}.
  Local Notation shr_name := llft_shr_name.
  Context `{!ShrBorSem FML Σ}.
  (** [unnest] needs the formula language to express borrow-state ownership. *)
  Context `{!LlftBorNames Σ, !BorStateFml bor_name}.
  (** The user's guarding world satisfaction, Leaf's [↑NllftG] minus the
    lifetime logic's own invariants. *)
  Local Notation WG := llft_WG.

  Context `{!StBor FML Σ}.

  Local Notation "@[ κ ]" := (llft_alive κ) (format "@[ κ ]") : bi_scope.
  Local Notation "[† κ ]" := (llft_dead κ) (format "[† κ ]") : bi_scope.
  Local Infix "⊑" := llft_incl (at level 70) : bi_scope.

  (** The two elimination rules, at this interpretation. *)
  Class StBorSem : Prop := STBORSEM {
    st_incl_incl {κ κ'} : st_incl κ κ' ⊢ κ ⊑ κ';
    st_iff_iff {Px Qx} : st_iff Px Qx ⊢ □ (bor_sem Px ↔ bor_sem Qx);
    st_iff_sep {Px Px' Qx Qx'} :
      st_iff Px Px' -∗ st_iff Qx Qx' -∗
        st_iff (bor_sep Px Qx) (bor_sep Px' Qx');
  }.
  Context `{!StBorSem}.

  Local Notation "P &&{*}&&> Q" := (fguard P Q)
    (at level 99, Q at level 200, format "P  &&{*}&&>  Q") : bi_scope.

  Local Notation bn := (BorNames bor_name o_name).

  Local Ltac unseal := rewrite /llft_alive /llft_alive_def
    /llft_dead /llft_dead_def /llft_ctx.

  (*** Lifetime logic, continued ***)

  (** Indexed borrows and full borrows *)

  Definition Idx: Type := ra.slice_name * gset nat.

  (* begin hide *)
  Local Definition idx_bor_def' (κ: gset lt_atom) (idx: Idx) (Px: FML $oi Σ)
    : iProp Σ :=
      let (sn, κ') := idx in
        (llft_alive_def' κ &&{*}&&> @[κ'])
          ∗ (∃ Px', □ (bor_sem Px' ↔ bor_sem Px) ∗ sinv_tok sn Px').

  Local Definition idx_bor_def (κ: lft) (idx: Idx) (Px: FML $oi Σ) : iProp Σ :=
      let (sn, κ') := idx in
        st_incl κ κ' ∗ (∃ Px', st_iff Px' Px ∗ sinv_tok sn Px').

  Local Definition full_bor_def (κ: lft) (Px: FML $oi Σ) : iProp Σ :=
      ∃ sn κ' ,
        st_incl κ κ'
          ∗ (∃ Px', st_iff Px' Px ∗ sinv_tok sn Px')
          ∗ OwnBorState bor_name sn
              (Borrow (set_map LtAtomSwell κ') {[default_dead]}).
  (* end hide *)

  Definition idx_bor (κ: lft) (idx: Idx) (Px: FML $oi Σ) : iProp Σ :=
    idx_bor_def κ idx Px.

  Definition full_bor (κ: lft) (Px: FML $oi Σ) : iProp Σ := full_bor_def κ Px.

  (* begin hide *)
  Local Ltac unseal_bor :=
    try unfold idx_bor; try unfold idx_bor_def;
    try unfold full_bor; try unfold full_bor_def.
  (* end hide *)

  Global Instance pers_idx_bor κ idx Px : Persistent (idx_bor κ idx Px).
  Proof. destruct idx. unseal_bor. typeclasses eauto. Qed.

  (** The raw forms of the two abstract components, for the internal
    accessors ([idx_bor_def']), which still speak of a guard and a [↔]. *)
  Local Lemma st_slice_raw {sn} {Px : FML $oi Σ} :
    (∃ Px', st_iff Px' Px ∗ sinv_tok sn Px') ⊢
      ∃ Px', □ (bor_sem Px' ↔ bor_sem Px) ∗ sinv_tok sn Px'.
  Proof.
    iIntros "(%Px' & #Hi & S)". iExists Px'. iFrame "S". by iApply st_iff_iff.
  Qed.

  Definition idx_bor_tok (idx: Idx) : iProp Σ :=
      let (sn, κ') := idx in
          OwnBorState bor_name sn
            (Borrow (set_map LtAtomSwell κ') {[default_dead]}).

  Lemma idx_bor_tok_unfold idx :
    idx_bor_tok idx = OwnBorState bor_name idx.1
      (Borrow (set_map LtAtomSwell idx.2) {[default_dead]}).
  Proof. by destruct idx. Qed.

  Notation "&{ κ }" := (full_bor κ) (format "&{ κ }") : bi_scope.
  Notation "&{ κ , i }" := (idx_bor κ i) (format "&{ κ , i }") : bi_scope.

  Global Instance full_bor_nonexpansive κ : NonExpansive (&{κ})%I.
  Proof. unseal_bor. solve_proper. Qed.

  Global Instance full_bor_proper κ : Proper ((≡) ==> (≡)) (&{κ})%I.
  Proof. apply ne_proper, _. Qed.

  Global Instance idx_bor_nonexpansive κ i : NonExpansive (&{κ, i})%I.
  Proof. destruct i. unseal_bor. solve_proper. Qed.

  Global Instance idx_bor_proper κ i : Proper ((≡) ==> (≡)) (&{κ, i})%I.
  Proof. apply ne_proper, _. Qed.

  Global Instance timeless_idx_bor_tok i : Timeless (idx_bor_tok i).
  Proof. destruct i. typeclasses eauto. Qed.

  Lemma llftl_bor_idx κ Px :
      &{κ} Px ⊣⊢ ∃ idx , &{κ, idx} Px ∗ idx_bor_tok idx.
  Proof.
    unseal_bor. iIntros. iSplit.
    { iIntros "F". iDestruct "F" as (sn κ') "[F [G H]]". iExists (sn, κ'). iFrame. }
    { iIntros "F". iDestruct "F" as (idx) "[F G]". destruct idx as [sn κ'].
      iDestruct "F" as "[F H]". iExists sn, κ'. iFrame. }
  Qed.

  Lemma llftl_bor_idx_to_full κ idx Px :
      &{κ, idx} Px -∗ idx_bor_tok idx -∗ &{κ} Px.
  Proof.
    iIntros "A B". iApply llftl_bor_idx. iExists idx. iFrame.
  Qed.

  Lemma llftl_idx_shorten κ κ' idx Px :
      st_incl κ' κ -∗ &{κ, idx} Px -∗ &{κ', idx} Px.
  Proof.
      unseal_bor. destruct idx as [sn κ2]. iIntros "#g [#g2 #slice]".
      iFrame "slice". iApply (st_incl_trans with "g g2").
  Qed.

  (* begin hide *)
  (** Minting whatever of [new] does not exist yet.  It no longer
    touches the borrow bookkeeping: a level hears of a lifetime when a
    borrow of it is first made there ([level.lv_borrow_ready]). *)
  Local Lemma make_everything_alive new sa sd :
      LtState llft_name sa sd -∗ llft_alive_def' sa -∗
      MintAuth mint_name (sa ∪ sd) -∗ |==> ∃ sa' ,
      ⌜ new ⊆ sa' ∪ sd ∧ sa ⊆ sa' ⌝
      ∗ LtState llft_name sa' sd ∗ llft_alive_def' sa'
      ∗ MintAuth mint_name (sa' ∪ sd) ∗ Minted mint_name (sa' ∪ sd).
  Proof.
    induction new as [|x T ? IH] using set_ind_L.
    - iIntros "State Alive MA".
      iMod (minted_get mint_name (sa ∪ sd) with "MA") as "[MA #M]".
      iModIntro. iExists sa. iSplitR; [iPureIntro; set_solver|].
      iFrame "State Alive MA". iExact "M".
    - iIntros "State Alive MA".
      iMod (IH with "State Alive MA")
        as (sa') "[[%HTin %Hsub] [State [Alive [MA _]]]]".
      destruct (decide (x ∈ sa' ∪ sd)) as [Hin|Hout].
      + iMod (minted_get mint_name (sa' ∪ sd) with "MA") as "[MA #M]".
        iModIntro. iExists sa'. iSplitR; [iPureIntro; set_solver|].
        iFrame "State Alive MA". iExact "M".
      + iMod (new_lt llft_name x sa' sd with "State") as "[State [Al1 Al2]]".
        { set_solver. } { set_solver. }
        iMod (minted_alloc_set mint_name (sa' ∪ sd) {[x]} with "MA")
          as "[MA #M]".
        replace ((sa' ∪ sd) ∪ {[x]}) with ((sa' ∪ {[x]}) ∪ sd)
          by set_solver.
        iModIntro. iExists (sa' ∪ {[x]}).
        iSplitR; [iPureIntro; set_solver|].
        iFrame "State MA". iSplitL "Alive Al1"; last by iExact "M".
        rewrite /llft_alive_def' big_sepS_union; last by set_solver.
        iFrame "Alive". rewrite big_sepS_singleton. iFrame "Al1".
  Qed.

  Local Lemma alive_alive_disjoint κ κ' sa :
    κ ⊆ sa →
    llft_alive_def' sa -∗ llft_alive_def' κ -∗ llft_alive_def' κ' -∗ ⌜κ ## κ'⌝.
  Proof.
    rewrite /llft_alive_def'. intros Hksa. iIntros "Set1 Set2 Set3".
    destruct (decide (κ ## κ')) as [Hdisj|Hnotdisj];
      first by iPureIntro; trivial.
    assert (∃ x , x ∈ κ ∩ κ') as Hex_x. { apply set_choose_L; set_solver. }
    destruct Hex_x as [x Hxin].
    rewrite (big_sepS_delete _ sa x); last by set_solver.
    rewrite (big_sepS_delete _ κ x); last by set_solver.
    rewrite (big_sepS_delete _ κ' x); last by set_solver.
    iDestruct "Set1" as "[Alive1 _]".
    iDestruct "Set2" as "[Alive2 _]".
    iDestruct "Set3" as "[Alive3 _]".
    iExFalso. iApply alive_alive_alive_false. iFrame "Alive1". iFrame.
  Qed.

  Local Lemma lv_dead_sub log pend s :
    lv_log s `prefix_of` log → lv_dead s ⊆ log_sd log ∪ pend_sd pend.
  Proof.
    move=> [ks ->]. rewrite /lv_dead /log_sd list_to_set_app_L. set_solver.
  Qed.

  Local Lemma llft_outlives_guards (ol : outlives_set) κ κ' :
    (llft_alive_def' κ &&{*}&&> llft_alive_def' κ') -∗
    (∀ o, ⌜o ∈ ol⌝ -∗
      (llft_alive_def' o.1 &&{*}&&> Alive llft_name o.2)) -∗
    (∀ o, ⌜o ∈ ol ∪ (set_map (λ k, (κ, k)) κ')⌝ -∗
      (llft_alive_def' o.1 &&{*}&&> Alive llft_name o.2)).
  Proof.
    iIntros "#Hincl #Hf" (o) "%Hoin".
    destruct (decide (o ∈ ol)) as [Hin|Hno].
    { by iApply "Hf". }
    assert (o.2 ∈ κ' ∧ o.1 = κ) as [Hx Heq].
    { rewrite elem_of_union in Hoin. destruct Hoin as [?|Ho]; [done|].
      rewrite elem_of_map in Ho. destruct Ho as [x [-> Hx]]. done. }
    rewrite Heq.
    iApply (fguard_trans with "Hincl"). iApply fguard_intro. iIntros "!> A".
    rewrite /llft_alive_def'.
    iDestruct (big_sepS_elem_of_acc _ κ' o.2 with "A") as "[$ A]"; first done.
    iIntros "Al". by iApply "A".
  Qed.
  (** A level's copy of the outlives relation is bounded by the shared
    one.  This is the only thing a rule has to know about the lag. *)
  Local Lemma llft_outlives_sub ol olk :
    OsetAuth osub_name ol -∗ llft_outlives olk -∗ ⌜olk ⊆ ol⌝.
  Proof. iIntros "A [_ B]". by iApply (osub_agree with "A B"). Qed.

  Local Lemma llft_augment_outlives sa sd s ol olk κ κ' :
    (κ ⊆ sa) →
    (κ' ⊆ sa) →
    (sa ## sd) →
    (lv_dead s ⊆ sd) →
    (olk ⊆ ol) →
    (llft_alive_def' κ &&{*}&&> llft_alive_def' κ')
    -∗ Minted mint_name (κ ∪ κ')
    -∗ llft_outlives_guards_at ol
    -∗ OsetAuth osub_name ol
    -∗ Outlives oset_name ol -∗ Outlives oset_name ol
    -∗ llft_outlives olk
    -∗ lv_inv (FML:=FML) llft_name log_name mint_name bn s
    -∗ |=[box_wsat bor_sem]=> ∃ ol' olk' ,
    ⌜ (∀ k : lt_atom, k ∈ κ' → (κ, k) ∈ ol')
      ∧ ol ⊆ ol'
      ∧ olk ⊆ olk'
      ∧ olk' ⊆ ol'
      ∧ (∀ k : lt_atom, k ∈ κ' → (κ, k) ∈ olk')
      ∧ (∀ o , o ∈ ol' → o ∉ ol → o.1 = κ ∧ o.2 ∈ κ') ⌝
    ∗ llft_outlives_guards_at ol'
    ∗ OsetAuth osub_name ol'
    ∗ Outlives oset_name ol' ∗ Outlives oset_name ol'
    ∗ llft_outlives olk'
    ∗ lv_inv (FML:=FML) llft_name log_name mint_name bn (lv_know (κ ∪ κ') s).
  Proof.
    intros Hk Hk' Hdisj Hdsub Hksub.
    iIntros "#Hincl #Mkk #Hf OA Os1 Os2 [Outlives #Osb] Lv".
    iDestruct (lv_outlives_cond with "Lv Outlives")
      as "([%Howf %Hoc] & Lv & Outlives)".
    pose (new := (set_map (λ k, (κ, k)) κ') : outlives_set).
    pose (ol' := (ol ∪ new) : outlives_set).
    pose (olk' := (olk ∪ new) : outlives_set).
    have Hnewin : ∀ o , o ∈ new → o.1 = κ ∧ o.2 ∈ κ'.
    { move=> o Ho. rewrite elem_of_map in Ho.
      destruct Ho as [x [-> Hx]]. done. }
    have Hnew2 : ∀ o , o ∈ ol' → o ∉ ol → o.2 ∈ κ' ∧ o.1 = κ.
    { move=> o Ho Hno. rewrite elem_of_union in Ho.
      destruct Ho as [?|Ho]; [done|]. have [H1 H2] := Hnewin o Ho. done. }
    have Hnew : ∀ o , o ∈ ol' → o ∉ ol → o.2 ∈ sa.
    { move=> o Ho Hno. have [H1 _] := Hnew2 o Ho Hno. by apply Hk'. }
    have Hnew3 : ∀ o , o ∈ ol' → o ∉ ol → o.1 = κ ∧ o.2 ∈ κ'.
    { move=> o Ho Hno. have [H1 H2] := Hnew2 o Ho Hno. done. }
    have Hkk : olk' ⊆ ol'. { rewrite /olk' /ol'. set_solver. }
    (* The level's relation is brought up only by the *new* pairs; it
      may still lag the shared one by everything added while this level
      was not held, which is what [Osub] bounds. *)
    iMod (lv_augment_outlives llft_name log_name mint_name bn s (κ ∪ κ')
      olk olk' with "Mkk [$Lv $Outlives]") as "[Lv Outlives]".
    { set_solver. }
    { move=> o Ho. rewrite elem_of_union in Ho. destruct Ho as [Hin|Ho].
      - have [H1 H2] := Howf o Hin. split; set_solver.
      - have [H1 H2] := Hnewin o Ho. rewrite H1. split; set_solver. }
    { move=> o Ho Hd. rewrite elem_of_union in Ho. destruct Ho as [Hin|Ho].
      - by apply Hoc.
      - exfalso. have [H1 H2] := Hnewin o Ho.
        have Ho2 : o.2 ∈ sa by apply Hk'.
        have := Hdsub _ Hd. set_solver. }
    iMod (outlives_update oset_name ol ol ol' with "[$Os1 $Os2]") as "[Os1 Os2]".
    iMod (osub_alloc_set osub_name ol new with "OA") as "[OA #Osb0]".
    iDestruct (osub_mono osub_name olk' ol' with "Osb0") as "#Osb'";
      [exact Hkk|].
    iDestruct (llft_outlives_guards ol κ κ' with "Hincl Hf") as "#Hf'".
    iModIntro. iExists ol', olk'. iSplitR.
    { iPureIntro. split; [|split; [set_solver|split; [set_solver|
        split; [exact Hkk|split; [|done]]]]].
      - move=> k Hkin. rewrite elem_of_union. right. rewrite elem_of_map.
        by exists k.
      - move=> k Hkin. rewrite elem_of_union. right. rewrite elem_of_map.
        by exists k. }
    iSplitR; [iExact "Hf'"|]. iFrame "OA Os1 Os2".
    iSplitR "Lv"; [|iExact "Lv"].
    rewrite /llft_outlives. iSplitL "Outlives"; [iExact "Outlives"|].
    iExact "Osb'".
  Qed.

  (* end hide *)

  (* begin hide *)
  Local Lemma llftl_idx_acc_fwd E κ idx Px :
      llft_ctx -∗ idx_bor_def' κ idx Px -∗
        idx_bor_tok idx -∗ llft_alive_def' κ -∗ |=[llft_wsat]{E}=> bor_sem Px
          ∗ OwnBorState bor_name (idx.1)
              (Unborrow κ (set_map LtAtomSwell idx.2) {[default_dead]}).
  Proof.
      destruct idx as [sn κ']. iIntros "_ [#Incl #Slice] OwnBor k".
      rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives olk)
        "[Oset [Delayed [OA [#Oguards [Ostate #Osb]]]]]".
      iDestruct "Main" as (sa sd log ol pend s)
        "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
      iDestruct (outlives_agree with "[$Ol $Oset]") as "%Heqol". subst ol.
      iDestruct (delayed_agree with "[$Del $Delayed]") as "%Heqpd". subst pend.
      destruct pure as [Hsd [_ [Hrun Howf]]].
      iDestruct (lv_log_prefix with "Auth Lv") as "%Hpre".
      iDestruct (lv_inv_wf with "Lv") as "%Hwfs".
      have Hdsub : lv_dead s ⊆ sd. { rewrite Hsd. by apply lv_dead_sub. }
      have Hdd : default_dead ∈ sd.
      { rewrite Hsd /pend_sd /= right_id_L. apply log_sd_dd. }
      iMod (make_everything_alive
        (κ ∪ (set_map LtAtomSwell κ') ∪ {[default_dead]}) sa sd
        with "State Alive MA")
        as (sa') "[[%Hsa %Hsasub] [State [Alive [MA #Mall]]]]".
      iDestruct (lt_state_alive_set llft_name κ sa' sd with "[State k]")
        as "%Hksa'". { iFrame. }
      iDestruct (LtState_disjoint llft_name _ _ with "State") as "%Hdisj".
      destruct (decide (set_map LtAtomSwell κ' ⊆ sa')) as [Hk'sa'|Hk'sa'].
      { iDestruct (lv_blocked_disj llft_name log_name mint_name bn s κ sa' Hksa'
          with "Alive k Lv") as "%Hbldisj".
        iDestruct (osub_agree osub_name olk outlives with "OA Osb")
          as "%Hkksub".
        iDestruct (llft_augment_outlives sa' sd s outlives olk κ
          (set_map LtAtomSwell κ')
          with "[] [] Oguards OA Oset Ol [$Ostate $Osb] Lv") as "X";
          [done|done|by apply inter_disj|done|done| | |].
        { rewrite /llft_alive_def' big_sepS_set_map. unseal.
          iExact "Incl". }
        { iApply (minted_mono with "Mall"). set_solver. }
        iMod ("X" with "Box") as "[Box X]".
        iDestruct "X" as (ol' olk')
          "[[%Ho' [%Hsub' [%Hksub' [%Hkk' [%Hok' %Hnew']]]]]
            [#Oguards' [OA [Oset [Ol [[Ostate #Osb'] Lv]]]]]]".
        iDestruct "Slice" as (Px') "[#PEquiv #Slice']".
        set s1 := lv_know (κ ∪ set_map LtAtomSwell κ') s.
        have Hdeq : lv_dead s1 = lv_dead s by done.
        have Hcreq : lv_created s1 = lv_created s ∪ (κ ∪ set_map LtAtomSwell κ')
          by done.
        iDestruct (lv_unborrow_start llft_name log_name mint_name bn s1 olk'
          sn κ (set_map LtAtomSwell κ') {[default_dead]} Px'
          with "[$Lv $Ostate $OwnBor $Slice' $k]") as "X".
        { apply lv_know_alive; [apply sub_mid2|].
          apply (disj_of_alive _ sa' sd); [done|done|done]. }
        { rewrite Hcreq.
          apply (dd_sub (lv_dead s)); [apply lv_dead_dd|].
          etrans; [exact Hwfs|]. apply union_subseteq_l. }
        { apply dd_not_disj, lv_dead_dd. }
        { done. }
        { apply lv_know_alive; [apply sub_mid|].
          apply (disj_of_alive _ sa' sd); [done|done|done]. }
        { move=> x Hx. by apply Hok'. }
        iMod ("X" with "Box") as "[Box (Lv & Ostate & OwnBor & P)]".
        iModIntro. iFrame "WG Shr Box". iSplitR "P OwnBor"; last first.
        { iFrame "OwnBor". by iApply "PEquiv". }
        iSplitR "OA Oset Delayed Ostate"; last first.
        { iExists ol', olk'.
          iFrame "Oset Delayed OA Oguards' Ostate Osb'". }
        iExists sa', sd, log, ol', None, (lv_block κ s1).
        iFrame "State Alive Auth Ol Del MA Lv". iPureIntro.
        split; [done|]. split; [done|]. split.
        { apply (kill_run_mono _ outlives); [|done].
          move=> o Ho Hno. have [_ Hx] := Hnew' o Ho Hno.
          rewrite /pend_sd /= right_id_L in Hsd.
          apply (notin_log sa' sd); [done|done|set_solver]. }
        move=> o Ho. destruct (decide (o ∈ outlives)) as [Hin|Hno].
        - have [H1 H2] := Howf o Hin. split.
          + by apply (sub_grow sa).
          + by apply (in_grow sa).
        - have [H1 H2] := Hnew' o Ho Hno. rewrite H1. split.
          + by apply sub_l.
          + apply in_l. set_solver. }
      assert (∃ x , x ∈ (set_map LtAtomSwell κ') ∩ sd) as Hex_x.
      { apply set_choose_L.
          assert ((set_map LtAtomSwell κ' : gset lt_atom) ⊆ sa' ∪ sd) as X
            by (etrans; [|exact Hsa]; set_solver).
          clear -X Hk'sa'. set_solver. }
      destruct Hex_x as [x Hex].
      iDestruct (LtState_entails_Dead llft_name x sa' sd with "State")
        as "#Deadx". { clear -Hex. set_solver. }
      iDestruct (llftl_incl_dead_implies_dead_unswell E κ
        (set_map LtAtomSwell κ') with "[] [] []") as "HdeadkUpd".
      { done. }
      { rewrite /llft_alive_def' big_sepS_set_map. unseal.
        iApply fguard_here. iExact "Incl". }
      { rewrite /llft_dead_def'. iExists x. iFrame "Deadx". iPureIntro.
        clear -Hex. set_solver. }
      iMod ("HdeadkUpd" with "[WG Shr Box State Alive Auth Ol Del MA Lv]")
        as "[_ #Hdeadk]".
      { rewrite /llft_wsatG. iFrame "WG Shr Box".
        iExists sa', sd, log, outlives, None, s.
        iFrame "State Alive Auth Ol Del MA Lv". iPureIntro.
        split; [done|]. split; [done|]. split; [done|].
        move=> o Ho. have [H1 H2] := Howf o Ho. split.
        - by apply (sub_grow sa).
        - by apply (in_grow sa). }
      iExFalso. iApply (llftl_not_own_end_unswell κ with "k Hdeadk").
  Qed.
  (* end hide *)

  Local Instance pers_idx_bor_def' κ idx Px : Persistent (idx_bor_def' κ idx Px).
  Proof. destruct idx. rewrite /idx_bor_def'. typeclasses eauto. Qed.

  (* begin hide *)
  Local Lemma llftl_idx_acc_back_vs κ idx Px Qx :
      llft_ctx -∗ idx_bor_def' κ idx Px -∗
        OwnBorState bor_name (idx.1)
          (Unborrow κ (set_map LtAtomSwell idx.2) {[default_dead]}) -∗
        bor_sem Qx -∗
        (bor_sem Qx ∗ llft_dead_def' κ ={↑NllftUsr ∪ ↑NllftUsr2}=∗ bor_sem Px)
        -∗ |=[llft_wsat]=> ∃ sn, sinv_tok sn Qx
            ∗ idx_bor_tok (sn, idx.2) ∗ llft_alive_def' κ.
  Proof.
      destruct idx as [sn κ']. iIntros "_ #idxbor OwnBor Q vs".
      iDestruct "idxbor" as "[#incl #slice]".
      rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Main" as (sa sd log ol pend s)
        "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
      iDestruct "slice" as (Px') "[#PEquiv #slice']".
      iDestruct (lv_unborrow_end llft_name log_name mint_name bn s sn κ
        (set_map LtAtomSwell κ') {[default_dead]} Px' Qx
        with "[$Lv $OwnBor $slice' vs Q]") as "X".
      { apply swell_set_set_map. } { apply swell_set_default_dead. }
      { iFrame "Q". iIntros "A". iMod ("vs" with "A") as "P". iModIntro.
        by iApply "PEquiv". }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn2) "(Lv & OwnBor & #slice2 & %Hbl & Ret)".
      iModIntro. iSplitR "OwnBor Ret".
      { iFrame "WG Shr Box Other".
        iExists sa, sd, log, ol, pend, (lv_unblock κ s).
        iFrame "State Alive Auth Ol Del MA Lv". iPureIntro. exact pure. }
      iExists sn2. by iFrame "Ret OwnBor slice2".
  Qed.

  Local Lemma llftl_idx_acc_back_at_same_idx κ idx Px :
      llft_ctx -∗ idx_bor_def' κ idx Px -∗
        OwnBorState bor_name (idx.1)
          (Unborrow κ (set_map LtAtomSwell idx.2) {[default_dead]}) -∗
        bor_sem Px
        -∗ |=[llft_wsat]=> idx_bor_tok idx ∗ llft_alive_def' κ.
  Proof.
      destruct idx as [sn κ']. iIntros "_ #idxbor OwnBor Q".
      iDestruct "idxbor" as "[#incl #slice]".
      rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Main" as (sa sd log ol pend s)
        "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
      iDestruct "slice" as (Px') "[#PEquiv #slice']".
      iDestruct (lv_unborrow_end_at_same_idx llft_name log_name mint_name bn s sn κ
        (set_map LtAtomSwell κ') {[default_dead]} Px'
        with "[$Lv $OwnBor $slice' Q]") as "X".
      { apply swell_set_set_map. } { apply swell_set_default_dead. }
      { by iApply "PEquiv". }
      iMod ("X" with "Box") as "[Box (Lv & OwnBor & %Hbl & Ret)]".
      iModIntro. iSplitR "OwnBor Ret".
      { iFrame "WG Shr Box Other".
        iExists sa, sd, log, ol, pend, (lv_unblock κ s).
        iFrame "State Alive Auth Ol Del MA Lv". iPureIntro. exact pure. }
      iFrame.
  Qed.

  Lemma llftl_bor_acc_maybe_swell' E Px κ' κ :
      llft_ctx -∗ (llft_alive_def' κ' &&{*}&&> @[κ]) -∗ &{κ} Px -∗
        llft_alive_def' κ' -∗ |=[llft_wsat]{E}=> bor_sem Px ∗
          (∀ Qx, (bor_sem Qx ={↑NllftUsr ∪ ↑NllftUsr2}=∗ bor_sem Px) -∗
            bor_sem Qx -∗ |=[llft_wsat]=> (&{κ} Qx) ∗ llft_alive_def' κ').
  Proof.
    iIntros "#ctx #incl1 fb alive". unseal_bor.
    iDestruct "fb" as (sn κ'') "[#incl [#slice OwnBor]]".
    iDestruct (st_incl_incl with "incl") as "#inclr".
    iDestruct (st_slice_raw with "slice") as "#slicer".
    iDestruct (fguard_trans with "incl1 inclr") as "#incl2".
    iMod (llftl_idx_acc_fwd E κ' (sn, κ'') Px with "ctx [] OwnBor alive")
      as "[P OwnBor]".
      { rewrite /idx_bor_def'. iFrame "incl2 slicer". }
    iModIntro. iFrame "P". iIntros (Qx) "vs Q".
    iMod (llftl_idx_acc_back_vs κ' (sn, κ'') Px Qx
      with "ctx [] OwnBor Q [vs]") as (sn2) "[#bor2 [tok2 alive]]".
      { rewrite /idx_bor_def'. iFrame "incl2 slicer". }
      { iIntros "[Q _]". by iApply "vs". }
    iModIntro. iFrame "alive". iExists sn2, κ''. iFrame "incl tok2".
    iExists Qx. iFrame "bor2". iApply st_iff_refl.
  Qed.
  (* end hide *)

  Lemma llftl_bor_acc' E Px κ' κ :
      llft_ctx -∗ κ' ⊑ κ -∗ &{κ} Px -∗ @[κ'] -∗ |=[llft_wsat]{E}=> bor_sem Px ∗
          (∀ Qx, (bor_sem Qx ={↑NllftUsr ∪ ↑NllftUsr2}=∗ bor_sem Px) -∗
            bor_sem Qx -∗ |=[llft_wsat]=> (&{κ} Qx) ∗ @[κ']).
  Proof.
    iIntros "ctx Incl Bor Alive".
    iMod (llftl_bor_acc_maybe_swell' E Px (set_map LtAtomSwell κ') κ
      with "ctx [Incl] Bor [Alive]") as "[P R]".
      - rewrite /llft_incl /llft_alive_def' big_sepS_set_map. iFrame.
      - rewrite /llft_alive_def' big_sepS_set_map. unseal. iFrame.
      - iModIntro. iFrame "P". iIntros (Qx) "A B".
        iMod ("R" $! Qx with "A B") as "[$ A]".
        iModIntro. rewrite /llft_alive_def' big_sepS_set_map. unseal. iFrame.
  Qed.

  Lemma llftl_bor_acc E Px κ :
      llft_ctx -∗ &{κ} Px -∗ @[κ] -∗ |=[llft_wsat]{E}=> bor_sem Px ∗
          (∀ Qx, (bor_sem Qx ∗ [†κ] ={↑NllftUsr ∪ ↑NllftUsr2}=∗ bor_sem Px) -∗
            bor_sem Qx -∗ |=[llft_wsat]=> (&{κ} Qx) ∗ @[κ]).
  Proof.
    iIntros "#ctx fb alive". unseal_bor.
    iDestruct "fb" as (sn κ') "[#incl [#slice OwnBor]]".
    iDestruct (st_incl_incl with "incl") as "#inclr".
    iDestruct (st_slice_raw with "slice") as "#slicer".
    iMod (llftl_idx_acc_fwd E (set_map LtAtomSwell κ) (sn, κ') Px
      with "ctx [] OwnBor [alive]") as "[P OwnBor]".
      { rewrite /idx_bor_def' /llft_alive_def' big_sepS_set_map. unseal.
        iFrame "inclr". iFrame "slicer". }
      { rewrite /llft_alive_def' big_sepS_set_map. unseal. iFrame "alive". }
    iModIntro. iFrame "P". iIntros (Qx) "vs Q".
    iMod (llftl_idx_acc_back_vs (set_map LtAtomSwell κ) (sn, κ') Px Qx
      with "ctx [] OwnBor Q [vs]") as (sn2) "[#bor2 [tok2 alive]]".
      { rewrite /idx_bor_def' /llft_alive_def' big_sepS_set_map. unseal.
        iFrame "inclr". iFrame "slicer". }
      { rewrite /llft_dead_def' -dead_def_set_map. unseal. iFrame "vs". }
    iModIntro. iSplitR "alive".
    { iExists sn2, κ'. iFrame "incl tok2". iExists Qx. iFrame "bor2".
      iApply st_iff_refl. }
    rewrite /llft_alive_def' big_sepS_set_map. unseal. iFrame "alive".
  Qed.

  (** The atomic accessor keeps the lifetime invariant open: in Leaf that is
    the mask change [|={↑Nllft,∅}=> ... |={∅,↑Nllft}=>], here it is that the
    world satisfaction is handed in and only given back at the end. *)
  Lemma llftl_bor_acc_atomic E Px κ :
      llft_ctx -∗ &{κ} Px -∗ llft_wsat -∗ |={E}=>
          (bor_sem Px ∗ (∀ Qx,
             (bor_sem Qx ∗ [†κ] ={↑NllftUsr ∪ ↑NllftUsr2}=∗ bor_sem Px) -∗
             bor_sem Qx ==∗ llft_wsat ∗ &{κ} Qx))
          ∨ (llft_wsat ∗ [†κ]).
  Proof.
      iIntros "_ fb". unseal_bor.
      iDestruct "fb" as (sn κ') "[#Incls [#slice OwnBor]]".
      iDestruct (st_incl_incl with "Incls") as "#Incl".
      rewrite {1}/llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives olk)
        "[Oset [Delayed [OA [#Oguards [Ostate #Osb]]]]]".
      iDestruct "Main" as (sa sd log ol pend s)
        "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
      iDestruct (outlives_agree with "[$Ol $Oset]") as "%Heqol". subst ol.
      iDestruct (delayed_agree with "[$Del $Delayed]") as "%Heqpd". subst pend.
      destruct pure as [Hsd [_ [Hrun Howf]]].
      iDestruct (lv_log_prefix with "Auth Lv") as "%Hpre".
      iDestruct (lv_inv_wf with "Lv") as "%Hwfs".
      have Hdsub : lv_dead s ⊆ sd. { rewrite Hsd. by apply lv_dead_sub. }
      have Hdd : default_dead ∈ sd.
      { rewrite Hsd /pend_sd /= right_id_L. apply log_sd_dd. }
      iMod (make_everything_alive
        (set_map LtAtomSwell κ ∪ set_map LtAtomSwell κ') sa sd
        with "State Alive MA")
        as (sa') "[[%Hsa %Hsasub] [State [Alive [MA #Mall]]]]".
      iDestruct (LtState_disjoint llft_name _ _ with "State") as "%Hdisj".
      destruct (decide (set_map LtAtomSwell κ ⊆ sa')) as [Hksa'|Hksa']; last first.
      { assert (∃ x , x ∈ (set_map LtAtomSwell κ : gset lt_atom) ∩ sd)
          as Hex_x. { apply set_choose_L. clear -Hsa Hksa'. set_solver. }
        destruct Hex_x as [x Hex].
        iDestruct (LtState_entails_Dead llft_name x sa' sd with "State")
          as "#Deadx". { clear -Hex. set_solver. }
        iModIntro. iRight. iSplitR "".
        { rewrite /llft_wsat /llft_wsatG. iFrame "WG Shr Box".
          iSplitR "Oset Delayed OA Ostate".
          - iExists sa', sd, log, outlives, None, s.
            iFrame "State Alive Auth Ol Del MA Lv". iPureIntro.
            split; [done|]. split; [done|]. split; [done|].
            move=> o Ho. have [H1 H2] := Howf o Ho. split.
            * by apply (sub_grow sa).
            * by apply (in_grow sa).
          - iExists outlives, olk.
          iFrame "Oset Delayed OA Oguards Ostate Osb". }
        unseal. rewrite dead_def_set_map. iExists x. iFrame "Deadx".
        iPureIntro. clear -Hex. set_solver. }
      destruct (decide (set_map LtAtomSwell κ' ⊆ sa')) as [Hk'sa'|Hk'sa']; last first.
      { assert (∃ x , x ∈ (set_map LtAtomSwell κ' : gset lt_atom) ∩ sd)
          as Hex_x. { apply set_choose_L. clear -Hsa Hk'sa'. set_solver. }
        destruct Hex_x as [x Hex].
        iDestruct (LtState_entails_Dead llft_name x sa' sd with "State")
          as "#Deadx". { clear -Hex. set_solver. }
        iDestruct (llftl_incl_dead_implies_dead E κ κ'
          with "[] Incl [Deadx]") as "Upd".
        { done. }
        { unseal. rewrite dead_def_set_map. iExists x. iFrame "Deadx".
          iPureIntro. clear -Hex. set_solver. }
        iMod ("Upd" with "[WG Shr Box State Alive Auth Ol Del MA Lv]")
          as "[WsatG #Hdeadk]".
        { rewrite /llft_wsatG. iFrame "WG Shr Box".
          iExists sa', sd, log, outlives, None, s.
          iFrame "State Alive Auth Ol Del MA Lv". iPureIntro.
          split; [done|]. split; [done|]. split; [done|].
          move=> o Ho. have [H1 H2] := Howf o Ho. split.
          - by apply (sub_grow sa).
          - by apply (in_grow sa). }
        iModIntro. iRight. iFrame "Hdeadk".
        rewrite /llft_wsat. iFrame "WsatG". iExists outlives, olk.
          iFrame "Oset Delayed OA Oguards Ostate Osb". }
      iDestruct (osub_agree osub_name olk outlives with "OA Osb")
        as "%Hkksub".
      iDestruct (llft_augment_outlives sa' sd s outlives olk
        (set_map LtAtomSwell κ) (set_map LtAtomSwell κ')
        with "[] [] Oguards OA Oset Ol [$Ostate $Osb] Lv") as "X";
        [done|done|by apply inter_disj|done|done| | |].
      { rewrite /llft_alive_def'. do 2 rewrite big_sepS_set_map. unseal.
        iFrame "Incl". }
      { iApply (minted_mono with "Mall"). set_solver. }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (ol' olk')
        "[[%Ho' [%Hsub' [%Hksub' [%Hkk' [%Hok' %Hnew']]]]]
          [#Oguards' [OA [Oset [Ol [[Ostate #Osb'] Lv]]]]]]".
      iDestruct "slice" as (Px') "[#PEq #slice']".
      iDestruct (st_iff_iff with "PEq") as "#PEquiv".
      set s1 := lv_know (set_map LtAtomSwell κ ∪ set_map LtAtomSwell κ') s.
      have Hpure1 : sd = log_sd log ∪ pend_sd None
        ∧ (∀ p : lt_atom * gset lt_atom , None = Some p → p.2 = sa')
        ∧ kill_run {[default_dead]} ol' log
        ∧ (∀ o , o ∈ ol' → o.1 ⊆ sa' ∪ sd ∧ o.2 ∈ sa' ∪ sd).
      { split; [done|]. split; [done|]. split.
        { apply (kill_run_mono _ outlives); [|done].
          move=> o Ho Hno. have [_ Hx] := Hnew' o Ho Hno.
          rewrite /pend_sd /= right_id_L in Hsd.
          apply (notin_log sa' sd); [done|done|set_solver]. }
        move=> o Ho. destruct (decide (o ∈ outlives)) as [Hin|Hno].
        - have [H1 H2] := Howf o Hin. split.
          + by apply (sub_grow sa).
          + by apply (in_grow sa).
        - have [H1 H2] := Hnew' o Ho Hno. rewrite H1. split.
          + by apply sub_l.
          + apply in_l. set_solver. }
      iDestruct (lv_unborrow_atomic llft_name log_name mint_name bn s1 olk' sn
        (set_map LtAtomSwell κ) (set_map LtAtomSwell κ')
        {[default_dead]} Px' with "[$Lv $Ostate $OwnBor $slice']") as "X".
      { apply lv_know_alive; [apply sub_mid2|].
        apply (disj_of_alive _ sa' sd); [done|done|done]. }
      { apply dd_not_disj, lv_dead_dd. }
      { move=> x Hx. by apply Hok'. }
      iMod ("X" with "Box") as "[Box [P X]]".
      iModIntro. iLeft. iSplitL "P". { by iApply "PEquiv". }
      iIntros (Qx) "vs Q". iDestruct ("X" $! Qx) as "X".
      iDestruct ("X" with "[vs Q]") as "X".
      { iFrame "Q". iIntros "A".
        iMod ("vs" with "[A]") as "Y".
        { unseal. rewrite dead_def_set_map. iFrame "A". }
        iModIntro. by iApply "PEquiv". }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn2) "(Lv & Ostate & OwnBor & #slice2)".
      iModIntro. iSplitR "OwnBor".
      { rewrite /llft_wsat /llft_wsatG. iFrame "WG Shr Box".
        iSplitR "OA Oset Delayed Ostate".
        - iExists sa', sd, log, ol', None, s1.
          iFrame "State Alive Auth Ol Del MA Lv". iPureIntro. exact Hpure1.
        - iExists ol', olk'.
          iFrame "Oset Delayed OA Oguards' Ostate Osb'". }
      iExists sn2, κ'. iFrame "Incls OwnBor". iExists Qx. iFrame "slice2".
      iApply st_iff_refl.
  Qed.

  (* begin hide *)
  Local Lemma llftl_bor_idx_acc_maybe_swell E Px κ idx :
      llft_ctx -∗ idx_bor_def' κ idx Px -∗ idx_bor_tok idx -∗
        llft_alive_def' κ -∗ |=[llft_wsat]{E}=> bor_sem Px ∗
          (bor_sem Px -∗ |=[llft_wsat]=> idx_bor_tok idx ∗ llft_alive_def' κ).
  Proof.
    destruct idx as [sn κ'].
    iIntros "#ctx [#Incl X] OwnBor alive". iDestruct "X" as (Px') "[#HIff #slice]".
    iMod (llftl_idx_acc_fwd E κ (sn, κ') Px with "ctx [] OwnBor alive")
      as "[P OwnBor]".
      { rewrite /idx_bor_def'. iFrame "#". }
    iModIntro. iFrame "P". iIntros "P".
    iMod (llftl_idx_acc_back_at_same_idx κ (sn, κ') Px with "ctx [] OwnBor P")
      as "[tok alive]".
      { rewrite /idx_bor_def'. iFrame "#". }
    iModIntro. iFrame.
  Qed.
  (* end hide *)

  Lemma llftl_bor_idx_acc E Px κ idx :
      llft_ctx -∗ &{κ, idx} Px -∗ idx_bor_tok idx -∗ @[κ] -∗
        |=[llft_wsat]{E}=> bor_sem Px ∗
          (bor_sem Px -∗ |=[llft_wsat]=> idx_bor_tok idx ∗ @[κ]).
  Proof.
    iIntros "#ctx #bor tok alive".
    iMod (llftl_bor_idx_acc_maybe_swell E Px (set_map LtAtomSwell κ) idx
      with "ctx [] tok [alive]") as "[$ A]".
    { destruct idx as [sn κ']. unseal_bor. iDestruct "bor" as "[#I #S]".
      rewrite /idx_bor_def' /llft_alive_def' big_sepS_set_map. unseal.
      iDestruct (st_incl_incl with "I") as "#I'". rewrite /llft_incl. unseal.
      iFrame "I'". by iApply st_slice_raw. }
    { rewrite /llft_alive_def' big_sepS_set_map. unseal. iFrame "alive". }
    iIntros "!> P". iMod ("A" with "P") as "[$ a]". iModIntro.
    rewrite /llft_alive_def' big_sepS_set_map. unseal. iFrame "a".
  Qed.

  (* begin hide *)
  Local Lemma llftl_borrow_fwd Px (κ: gset nat) :
      llft_ctx -∗ bor_sem Px -∗ |=[llft_wsat]=> ∃ sn1 sn2 ,
          sinv_tok sn1 Px
          ∗ sinv_tok sn2 Px
          ∗ OwnBorState bor_name sn1
              (Borrow (set_map LtAtomSwell κ : gset lt_atom) {[default_dead]})
          ∗ OwnBorState bor_name sn2
              (Borrow ∅ (set_map LtAtomSwell κ : gset lt_atom)).
  Proof.
      iIntros "_ P". rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives olk)
        "[Oset [Delayed [OA [#Oguards [Ostate #Osb]]]]]".
      iDestruct "Main" as (sa sd log ol pend s)
        "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
      iDestruct (outlives_agree with "[$Ol $Oset]") as "%Heqol". subst ol.
      iDestruct (delayed_agree with "[$Del $Delayed]") as "%Heqpd". subst pend.
      destruct pure as [Hsd [_ [Hrun Howf]]].
      iMod (make_everything_alive (set_map LtAtomSwell κ) sa sd
        with "State Alive MA")
        as (sa') "[[%Hsa' %Hsasub] [State [Alive [MA #Mall]]]]".
      (* the level is told about [κ] on the spot *)
      iDestruct (lv_know_one llft_name log_name mint_name bn s
        (set_map LtAtomSwell κ) with "[] Lv") as "X";
        [iApply (minted_mono with "Mall"); set_solver|].
      iMod ("X" with "Box") as "[Box Lv]".
      set s1 := lv_know (set_map LtAtomSwell κ) s.
      iDestruct (lv_borrow_create llft_name log_name mint_name bn s1
        (set_map LtAtomSwell κ) Px with "[$Lv $P]") as "X".
      { apply swell_set_set_map. } { rewrite /lv_know /=. set_solver. }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn1 sn2)
        "(Lv & OwnBor1 & OwnBor2 & #slice1 & #slice2)".
      iModIntro. iSplitR "OwnBor1 OwnBor2".
      { iFrame "WG Shr Box". iSplitR "Oset Delayed OA Ostate".
        - iExists sa', sd, log, outlives, None, s1.
          iFrame "State Alive Auth Ol Del MA Lv". iPureIntro.
          split; [done|]. split; [done|]. split; [done|].
          move=> o Ho. have [H1 H2] := Howf o Ho. split.
          + by apply (sub_grow sa).
          + by apply (in_grow sa).
        - iExists outlives, olk.
          iFrame "Oset Delayed OA Oguards Ostate Osb". }
      iExists sn1, sn2. iFrame "OwnBor1 OwnBor2". iFrame "slice1 slice2".
  Qed.

  (** Reclaiming a borrow after the lifetime has died.  This is the
    first rule that needs the bookkeeping to *know* the lifetime is
    dead, so it catches the level up to the kill order first - and that
    is why it carries the lifetime logic's own mask, which running
    [future_vs] needs. *)
  Local Lemma llftl_borrow_rev Px (κ: gset nat) sn :
      llft_ctx -∗ sinv_tok sn Px -∗
        OwnBorState bor_name sn (Borrow ∅ (set_map LtAtomSwell κ)) -∗ [†κ] -∗
        |=[llft_wsat]{↑NllftUsr ∪ ↑NllftUsr2}=> bor_sem Px.
  Proof.
      iIntros "_ #slice OwnBor #Dead". rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives olk)
        "[Oset [Delayed [OA [#Oguards [Ostate #Osb]]]]]".
      iDestruct "Main" as (sa sd log ol pend s)
        "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
      iDestruct (outlives_agree with "[$Ol $Oset]") as "%Heqol". subst ol.
      iDestruct (delayed_agree with "[$Del $Delayed]") as "%Heqpd". subst pend.
      destruct pure as [Hsd [_ [Hrun Howf]]].

      have Hlogsd : log_sd log = sd.
      { rewrite Hsd /pend_sd /= right_id_L. done. }
      iMod (minted_get mint_name (sa ∪ sd) with "MA") as "[MA #Mall0]".
      iDestruct (LtState_deads log sa sd with "State") as "#Ds".
      { move=> x Hx. rewrite -Hlogsd /log_sd elem_of_union. right.
        by apply elem_of_list_to_set. }
      iDestruct (osub_agree osub_name olk outlives with "OA Osb")
        as "%Hkksub".
      have Hrunk : kill_run {[default_dead]} olk log.
      { apply (kill_run_anti _ outlives); [exact Hkksub|exact Hrun]. }
      iDestruct (lv_catch_up_to_log llft_name log_name mint_name bn s
        olk log (DfracOwn 1) Hrunk with "Auth [] Ds [$Lv $Ostate]")
        as "X".
      { iApply (minted_mono with "Mall0"). rewrite -Hlogsd /log_sd.
        set_solver. }
      iMod ("X" with "Box") as "[Box [Auth X]]".
      iDestruct "X" as (s0) "[%Hlog0 [Lv Ostate]]".
      have Hds : lv_dead s0 = sd.
      { rewrite /lv_dead Hlog0 -Hlogsd /log_sd. done. }
      iMod (make_everything_alive (set_map LtAtomSwell κ) sa sd
        with "State Alive MA")
        as (sa') "[[%Hsa' %Hsasub] [State [Alive [MA #Mall]]]]".
      unseal. iDestruct "Dead" as (k) "[%Hkdead Deadkin]".
      iAssert (⌜ LtAtomSwell k ∈ sd ⌝)%I as "%Hksd".
      { iApply (lt_state_dead llft_name (LtAtomSwell k) sa' sd).
        iSplitL; iFrame. iFrame "#". }
      iDestruct (lv_know_one llft_name log_name mint_name bn s0
        (set_map LtAtomSwell κ) with "[] Lv") as "X";
        [iApply (minted_mono with "Mall"); set_solver|].
      iMod ("X" with "Box") as "[Box Lv]".
      set s1 := lv_know (set_map LtAtomSwell κ) s0.
      iDestruct (lv_unborrow_start llft_name log_name mint_name bn s1 olk
        sn ∅ ∅ (set_map LtAtomSwell κ) Px
        with "[$Lv $Ostate $OwnBor $slice]") as "X".
      { apply empty_subseteq. }
      { rewrite /lv_know /=. apply union_subseteq_r. }
      { rewrite /lv_know /lv_dead /= -/(lv_dead s0) Hds.
        apply (not_disj_of _ _ (LtAtomSwell k)); [|done].
        apply elem_of_map_2. done. }
      { apply disjoint_empty_l. }
      { apply empty_subseteq. }
      { move=> k0 /elem_of_empty []. }
      { by rewrite big_sepS_empty. }
      iMod ("X" with "Box") as "[Box (Lv & Ostate & OwnBor & P)]".
      iModIntro. iFrame "P". iFrame "WG Shr Box".
      iSplitR "Oset Delayed OA Ostate".
      - iExists sa', sd, log, outlives, None, (lv_block ∅ s1).
        iFrame "State Alive Auth Ol Del MA Lv". iPureIntro.
        split; [done|]. split; [done|]. split; [done|].
        move=> o Ho. have [H1 H2] := Howf o Ho. split.
        + by apply (sub_grow sa).
        + by apply (in_grow sa).
      - iExists outlives, olk.
        iFrame "Oset Delayed OA Oguards Ostate Osb".
  Qed.

  Local Lemma llftl_weaken sn (κ κ' : gset nat) Px :
      llft_ctx -∗
        OwnBorState bor_name sn
          (Borrow (set_map LtAtomSwell κ) {[default_dead]}) -∗
        sinv_tok sn Px -∗ |=[llft_wsat]=>
          ∃ sn' , OwnBorState bor_name sn'
            (Borrow (set_map LtAtomSwell κ ∪ set_map LtAtomSwell κ')
              {[default_dead]}) ∗ sinv_tok sn' Px.
  Proof.
    iIntros "_ OwnBor #slice". rewrite /modw /llft_wsat /llft_wsatG.
    iIntros "[[WG [Shr [Box Main]]] Other]".
    iDestruct "Other" as (outlives olk)
      "[Oset [Delayed [OA [#Oguards [Ostate #Osb]]]]]".
    iDestruct "Main" as (sa sd log ol pend s)
      "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
    iDestruct (outlives_agree with "[$Ol $Oset]") as "%Heqol". subst ol.
    iDestruct (delayed_agree with "[$Del $Delayed]") as "%Heqpd". subst pend.
    destruct pure as [Hsd [_ [Hrun Howf]]].
    iMod (make_everything_alive (set_map LtAtomSwell κ') sa sd
      with "State Alive MA")
      as (sa') "[[%Hsa %Hsasub] [State [Alive [MA #Mall]]]]".
    iDestruct (lv_know_one llft_name log_name mint_name bn s
      (set_map LtAtomSwell κ') with "[] Lv") as "X";
      [iApply (minted_mono with "Mall"); set_solver|].
    iMod ("X" with "Box") as "[Box Lv]".
    set s1 := lv_know (set_map LtAtomSwell κ') s.
    iDestruct (lv_reborrow llft_name log_name mint_name bn s1 Px sn
      (set_map LtAtomSwell κ) (set_map LtAtomSwell κ')
      with "[$Lv $OwnBor $slice]") as "X".
    { apply swell_set_set_map. }
    { rewrite /lv_know /=. apply union_subseteq_r. }
    iMod ("X" with "Box") as "[Box X]".
    iDestruct "X" as (sn1 sn2) "(Lv & OwnBor1 & OwnBor2 & #slice1 & #slice2)".
    iModIntro. iSplitR "OwnBor1".
    { iFrame "WG Shr Box". iSplitR "Oset Delayed OA Ostate".
      - iExists sa', sd, log, outlives, None, s1.
        iFrame "State Alive Auth Ol Del MA Lv". iPureIntro.
        split; [done|]. split; [done|]. split; [done|].
        move=> o Ho. have [H1 H2] := Howf o Ho. split.
        + by apply (sub_grow sa).
        + by apply (in_grow sa).
      - iExists outlives, olk.
        iFrame "Oset Delayed OA Oguards Ostate Osb". }
    iExists sn1. iFrame "OwnBor1". iFrame "slice1".
  Qed.
  (* end hide *)

  (** LeLiLo-Borrow *)
  Lemma llftl_borrow κ Px :
      llft_ctx -∗ bor_sem Px -∗ |=[llft_wsat]=>
        &{κ} Px ∗ ([†κ] -∗
          |=[llft_wsat]{↑NllftUsr ∪ ↑NllftUsr2}=> bor_sem Px).
  Proof.
    iIntros "#ctx P". unseal_bor.
    iMod (llftl_borrow_fwd Px κ with "ctx P")
      as (sn1 sn2) "[#slice1 [#slice2 [OwnBor1 OwnBor2]]]".
    iModIntro. iSplitL "OwnBor1".
    { iExists sn1, κ. iFrame "OwnBor1". iSplitR. { iApply st_incl_refl. }
      iExists Px. iFrame "slice1". iApply st_iff_refl. }
    iIntros "#kdead".
    iApply (llftl_borrow_rev Px κ sn2 with "ctx slice2 OwnBor2 kdead").
  Qed.

  (** LeLiLo-Sep-Split *)
  Lemma llftl_sep_split E Px Qx κ :
      llft_ctx -∗ &{κ} (bor_sep Px Qx) -∗ |=[llft_wsat]{E}=>
        &{κ} Px ∗ &{κ} Qx.
  Proof.
      iIntros "_ fbPQ". unseal_bor.
      iDestruct "fbPQ" as (sn κ') "[#incl [#slice OwnBor]]".
      rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives olk)
        "[Oset [Delayed [OA [#Oguards [Ostate #Osb]]]]]".
      iDestruct "Main" as (sa sd log ol pend s)
        "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
      iDestruct "slice" as (PQ) "[#PQEq #slice']".
      iDestruct (st_iff_iff with "PQEq") as "#PQEquiv".
      iDestruct (lv_iff llft_name log_name mint_name bn s sn
        (set_map LtAtomSwell κ') {[default_dead]} PQ (bor_sep Px Qx)
        with "[$Lv $OwnBor $slice' $PQEquiv]") as "X".
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn0) "(Lv & OwnBor & #slice0)".
      iDestruct (lv_split llft_name log_name mint_name bn s sn0
        (set_map LtAtomSwell κ') {[default_dead]} Px Qx
        with "[$Lv $OwnBor $slice0]") as "X".
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn1 sn2) "(Lv & OwnBor1 & OwnBor2 & #slice1 & #slice2)".
      iModIntro. iSplitR "OwnBor1 OwnBor2".
      { iFrame "WG Shr Box". iSplitR "Oset Delayed OA Ostate".
        - iExists sa, sd, log, ol, pend, s.
          iFrame "State Alive Auth Ol Del MA Lv". iPureIntro. exact pure.
        - iExists outlives, olk.
          iFrame "Oset Delayed OA Oguards Ostate Osb". }
      iSplitL "OwnBor1".
      { iExists sn1, κ'. iFrame "OwnBor1 incl". iExists Px.
        iFrame "slice1". iApply st_iff_refl. }
      { iExists sn2, κ'. iFrame "OwnBor2 incl". iExists Qx.
        iFrame "slice2". iApply st_iff_refl. }
  Qed.

  (** LeLiLo-Sep-Join *)
  Lemma llftl_sep_join E Px Qx κ :
      llft_ctx -∗ &{κ} Px -∗ &{κ} Qx -∗ |=[llft_wsat]{E}=>
        &{κ} (bor_sep Px Qx).
  Proof.
      iIntros "#ctx fbP fbQ". unseal_bor.
      iDestruct "fbP" as (sn1 κ1) "[#incl1 [Hs1 OwnBor1]]".
      iDestruct "fbQ" as (sn2 κ2) "[#incl2 [Hs2 OwnBor2]]".
      iDestruct "Hs1" as (Px') "[#PEquiv #slice1]".
      iDestruct "Hs2" as (Qx') "[#QEquiv #slice2]".
      iMod (llftl_weaken sn1 κ1 κ2 with "ctx OwnBor1 slice1")
        as (sn1') "[OwnBor1 #slice1']".
      iMod (llftl_weaken sn2 κ2 κ1 with "ctx OwnBor2 slice2")
        as (sn2') "[OwnBor2 #slice2']".
      replace ((set_map LtAtomSwell κ2 : gset lt_atom) ∪ set_map LtAtomSwell κ1)
        with ((set_map LtAtomSwell κ1 : gset lt_atom) ∪ set_map LtAtomSwell κ2)
        by set_solver.
      rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives olk)
        "[Oset [Delayed [OA [#Oguards [Ostate #Osb]]]]]".
      iDestruct "Main" as (sa sd log ol pend s)
        "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
      iDestruct (lv_inv_wf with "Lv") as "%Hwfs".
      iDestruct (lv_join llft_name log_name mint_name bn s sn1' sn2'
        (set_map LtAtomSwell κ1 ∪ set_map LtAtomSwell κ2) {[default_dead]}
        Px' Qx' with "[$Lv $OwnBor1 $OwnBor2 $slice1' $slice2']") as "X".
      { apply swell_set_default_dead. }
      { apply (dd_sub (lv_dead s)); [apply lv_dead_dd|exact Hwfs]. }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn) "(Lv & OwnBor & #slice)".
      iModIntro. iSplitR "OwnBor".
      { iFrame "WG Shr Box". iSplitR "Oset Delayed OA Ostate".
        - iExists sa, sd, log, ol, pend, s.
          iFrame "State Alive Auth Ol Del MA Lv". iPureIntro. exact pure.
        - iExists outlives, olk.
          iFrame "Oset Delayed OA Oguards Ostate Osb". }
      iExists sn, (κ1 ∪ κ2). rewrite set_map_inter. iFrame "OwnBor".
      iSplitR. { iApply st_incl_glb; iFrame "#". }
      iExists (bor_sep Px' Qx'). iFrame "slice".
      iApply (st_iff_sep with "PEquiv QEquiv").
  Qed.

  (** LeLiLo-Unnest *)
  Lemma llftl_idx_bor_unnest E κ κ' idx Px :
      llft_ctx -∗ &{κ, idx} Px -∗
        &{κ'} (bor_state_fml idx.1
          (Borrow (set_map LtAtomSwell idx.2) {[default_dead]})) -∗
        |=[llft_wsat]{E}=> &{κ ⊓ κ'} Px.
  Proof.
      destruct idx as [sn κ2]. unseal_bor.
      iIntros "_ [#incl #slice] fb".
      iDestruct "fb" as (sn' κ2') "[#incl2 [Hs2 OwnBor2]]".
      rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives olk)
        "[Oset [Delayed [OA [#Oguards [Ostate #Osb]]]]]".
      iDestruct "Main" as (sa sd log ol pend s)
        "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
      iDestruct "slice" as (Px') "[#PEquiv #slice']".
      iDestruct "Hs2" as (Pibt) "[#PibtEq #slice2]".
      iDestruct (st_iff_iff with "PEquiv") as "#PEquivr".
      iDestruct (st_iff_iff with "PibtEq") as "#PibtEquiv".
      iDestruct (lv_iff llft_name log_name mint_name bn s sn'
        (set_map LtAtomSwell κ2') {[default_dead]} Pibt
        (bor_state_fml sn (Borrow (set_map LtAtomSwell κ2) {[default_dead]}))
        with "[$Lv $OwnBor2 $slice2 $PibtEquiv]") as "X".
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn0) "(Lv & OwnBor2 & #slice0)".
      (* unnesting is done here rather than through a wrapper, because it
        is the one rule that needs [BorStateFml bor_name] *)
      rewrite lv_inv_unfold.
      iDestruct "Lv" as "(%Hwfs & #Lb & #Mint & Inv & Blk)".
      iDestruct (inner_unnest llft_name bor_name o_name o_name
        (lv_alive s) (lv_dead s) (lv_blocked s) sn sn0
        (set_map LtAtomSwell κ2) (set_map LtAtomSwell κ2') Px'
        with "[$Inv $slice' $OwnBor2 $slice0]") as "X".
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn2) "(Inv & OwnBor & #slice3)".
      iModIntro. iSplitR "OwnBor".
      { iFrame "WG Shr Box". iSplitR "Oset Delayed OA Ostate".
        - iExists sa, sd, log, ol, pend, s.
          iFrame "State Alive Auth Ol Del".
          iSplitR; [iPureIntro; exact pure|]. iFrame "MA".
          rewrite lv_inv_unfold. iSplitR; [by iPureIntro|].
          iFrame "Lb Mint".
          iSplitL "Inv"; [iExact "Inv"|iExact "Blk"].
        - iExists outlives, olk.
          iFrame "Oset Delayed OA Oguards Ostate Osb". }
      iExists sn2, (κ2 ∪ κ2'). rewrite set_map_inter. iFrame "OwnBor".
      iSplitR.
      { iApply st_incl_glb.
        - iApply (st_incl_trans with "[] incl"). iApply st_incl_meet_l.
        - iApply (st_incl_trans with "[] incl2"). iApply st_incl_meet_r. }
      iExists Px'. iFrame "slice3". iFrame "PEquiv".
  Qed.

  (** LeLiLo-Bor-Fake *)
  (** As with [llftl_borrow_rev], a fake borrow needs the bookkeeping to
    know the lifetime is dead, so it catches the level up first and
    carries the lifetime logic's own mask. *)
  Lemma llftl_bor_fake κ Px :
    llft_ctx -∗ [†κ] -∗
    |=[llft_wsat]{↑NllftUsr ∪ ↑NllftUsr2}=> &{κ} Px.
  Proof.
      iIntros "_ #dead". unseal_bor. rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives olk)
        "[Oset [Delayed [OA [#Oguards [Ostate #Osb]]]]]".
      iDestruct "Main" as (sa sd log ol pend s)
        "[State [Alive [Auth [Ol [Del [%pure [MA Lv]]]]]]]".
      iDestruct (outlives_agree with "[$Ol $Oset]") as "%Heqol". subst ol.
      iDestruct (delayed_agree with "[$Del $Delayed]") as "%Heqpd". subst pend.
      destruct pure as [Hsd [Hpd [Hrun Howf]]].
      have Hlogsd : log_sd log = sd.
      { rewrite Hsd /pend_sd /= right_id_L. done. }
      iMod (minted_get mint_name (sa ∪ sd) with "MA") as "[MA #Mall0]".
      iDestruct (LtState_deads log sa sd with "State") as "#Ds".
      { move=> x Hx. rewrite -Hlogsd /log_sd elem_of_union. right.
        by apply elem_of_list_to_set. }
      iDestruct (osub_agree osub_name olk outlives with "OA Osb")
        as "%Hkksub".
      have Hrunk : kill_run {[default_dead]} olk log.
      { apply (kill_run_anti _ outlives); [exact Hkksub|exact Hrun]. }
      iDestruct (lv_catch_up_to_log llft_name log_name mint_name bn s
        olk log (DfracOwn 1) Hrunk with "Auth [] Ds [$Lv $Ostate]")
        as "X".
      { iApply (minted_mono with "Mall0"). rewrite -Hlogsd /log_sd.
        set_solver. }
      iMod ("X" with "Box") as "[Box [Auth X]]".
      iDestruct "X" as (s0) "[%Hlog0 [Lv Ostate]]".
      have Hds : lv_dead s0 = sd.
      { rewrite /lv_dead Hlog0 -Hlogsd /log_sd. done. }
      unseal. iDestruct "dead" as (k) "[%HkK deadk]".
      iAssert (⌜LtAtomSwell k ∈ sd⌝)%I as "%Hksd".
      { iApply lt_state_dead. iSplit. { iFrame "State". } iFrame "deadk". }
      iDestruct (lv_fake llft_name log_name mint_name bn s0
        (set_map LtAtomSwell κ) {[default_dead]} Px with "Lv") as "X".
      { rewrite Hds. apply (not_disj_of _ _ (LtAtomSwell k)); [|done].
        by apply elem_of_map_2. }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn) "(Lv & OwnBor & #slice)".
      iModIntro. iSplitR "OwnBor".
      { iFrame "WG Shr Box". iSplitR "Oset Delayed OA Ostate".
        - iExists sa, sd, log, outlives, None, s0.
          iFrame "State Alive Auth Ol Del MA Lv". iPureIntro.
          split; [done|]. split; [done|]. split; [done|]. done.
        - iExists outlives, olk.
          iFrame "Oset Delayed OA Oguards Ostate Osb". }
      iExists sn, κ. iFrame "OwnBor". iSplitR. { iApply st_incl_refl. }
      iExists Px. iFrame "slice". iApply st_iff_refl.
  Qed.

  (** Indexed borrows and guards *)

  (* begin hide *)
  Local Lemma llft_alive_sing_1 k :
    llft_alive_def' {[k]} ⊢ Alive llft_name k.
  Proof. rewrite /llft_alive_def'. by rewrite big_sepS_singleton. Qed.
  Local Lemma llft_alive_sing_2 k :
    Alive llft_name k ⊢ llft_alive_def' {[k]}.
  Proof. rewrite /llft_alive_def'. by rewrite big_sepS_singleton. Qed.

  Local Lemma llft_alive_set_map_1 κ :
    llft_alive_def' (set_map LtAtomSwell κ) ⊢ @[κ].
  Proof. rewrite /llft_alive_def' big_sepS_set_map. by unseal. Qed.
  Local Lemma llft_alive_set_map_2 κ :
    @[κ] ⊢ llft_alive_def' (set_map LtAtomSwell κ).
  Proof. rewrite /llft_alive_def' big_sepS_set_map. by unseal. Qed.

  (** The borrow's slice is full.  The original asked for
    [set_map LtAtomSwell κ' ⊆ alive]; here it asks for
    [set_map LtAtomSwell κ' ## dead], which is the same thing by
    [inv.subseteq_alive_iff] and is what a caller can produce when the
    bookkeeping's view of the dead set is its own. *)
  Local Lemma guard_helper2 sn κ' b alive dead blocked :
      idx_bor_tok (sn, κ')
      ∧ (inner_inv llft_name bor_name o_name alive dead blocked
          ∗ ⌜set_map LtAtomSwell κ' ## dead⌝
          ∗ box_own_auth sn (●E b))
      ⊢ ⌜b = true⌝.
  Proof.
    iIntros "A".
    iAssert (⌜set_map LtAtomSwell κ' ## dead⌝)%I as "%Hdisj'".
    { iDestruct "A" as "[_ (_ & $ & _)]". }
    rewrite /inner_inv.
    rewrite bi.sep_exist_r.
    setoid_rewrite bi.sep_exist_r. setoid_rewrite bi.sep_exist_r.
    setoid_rewrite bi.sep_exist_r.
    rewrite bi.and_exist_l.
    setoid_rewrite bi.and_exist_l. setoid_rewrite bi.and_exist_l.
    setoid_rewrite bi.and_exist_l.
    iDestruct "A" as (mbs mprops Ptotal outlives) "A".
    iAssert (⌜inv.map_wf alive dead blocked outlives mbs⌝)%I as "%Hwf".
    { iDestruct "A" as "[_ [(? & ? & ? & ? & ? & %Hall & ?) _]]".
      iPureIntro. by destruct Hall as [_ [? _]]. }
    have Hdisj : alive ## dead by apply Hwf.
    have Hdd : default_dead ∈ dead by destruct Hwf as [_ [_ [? _]]].
    iDestruct (agree_bor_state_borrow_lts_and bor_name sn mbs dead
      (set_map LtAtomSwell κ') {[default_dead]} with "[A]") as (de') "%Hde'".
    { done. }
    { iSplit.
      - iDestruct "A" as "[A _]". iFrame "A".
      - iDestruct "A" as "[_ ((? & ? & ? & ?) & ? & ?)]". iFrame. }
    destruct Hde' as [Hmbssn Hx].
    have Hal : set_map LtAtomSwell κ' ⊆ alive.
    { destruct Hwf as [_ [_ [_ [Hall2 _]]]].
      have Hb := Hall2 sn _ Hmbssn. destruct Hb as [Hsub2 _].
      apply (inv.subseteq_alive_iff Hdisj); [set_solver|done]. }
    iDestruct "A" as "[_ ((_ & _ & _ & Box & _) & _ & BoxOwnAuth)]".
    assert (boxmap alive dead mbs !! sn = Some true) as Htrue.
    { unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. simpl.
      f_equiv. rewrite bool_decide_eq_true. split; [done|]. set_solver. }
    iAssert (⌜true = b⌝)%I with "[Box BoxOwnAuth]" as "%Heq";
      last by iPureIntro.
    iApply (box_own_auth_agree_and (γ:=sn)). iSplit.
    - rewrite /box. iDestruct "Box" as (Φ) "[_ A]".
      rewrite (big_sepM_delete _ _ sn); last by apply Htrue.
      iDestruct "A" as "[[A B] _]". iFrame "A".
    - iFrame "BoxOwnAuth".
  Qed.

  (** The state the guard sees: the main invariant together with the slice's
    own cell, packaged as a single existential so that the persistent facts
    can be pinned down by [guard_exist_strengthen]. *)
  Local Definition guard_body (sn : ra.slice_name) (Px' : FML $oi Σ)
    (a : gset lt_atom * gset lt_atom * lvState * bool) : iProp Σ :=
    (∃ log ol pend, llft_inv_main_at a.1.1.1 a.1.1.2 log ol pend a.1.2)
    ∗ (box_own_auth sn (●E a.2) ∗ (if a.2 then bor_sem Px' else True%I)).

  Local Lemma guard_body_eq_1 sn Px' :
    (slice_body bor_sem sn Px' ∗ llft_inv_main) ⊢ ∃ a, guard_body sn Px' a.
  Proof.
    rewrite /llft_inv_main /slice_body /guard_body.
    iIntros "[(%b & H2) (%sa & %sd & %log & %ol & %pend & %s & H)]".
    iExists (sa, sd, s, b). simpl. iSplitR "H2"; [|iFrame].
    iExists log, ol, pend. iFrame.
  Qed.
  Local Lemma guard_body_eq_2 sn Px' :
    (∃ a, guard_body sn Px' a) ⊢ slice_body bor_sem sn Px' ∗ llft_inv_main.
  Proof.
    rewrite /llft_inv_main /slice_body /guard_body.
    iIntros "(%a & H1 & H2)". destruct a as [[[sa sd] s] b]. simpl.
    iSplitL "H2". { iExists b. iFrame. }
    iDestruct "H1" as (log ol pend) "H1".
    iExists sa, sd, log, ol, pend, s. iFrame.
  Qed.
  (* end hide *)

  #[export] Instance wsat_incl_llft_wsatG_box_main :
    WsatIncl llft_wsatG (box_wsat bor_sem ∗ llft_inv_main) (WG ∗ shr_wsat).
  Proof.
    rewrite /WsatIncl /llft_wsatG. iSplit.
    - iIntros "(a&b&c&d)". iFrame.
    - iIntros "((c&d)&(a&b))". iFrame.
  Qed.

  (** LeLiLo-Idx-Bor-Guard *)
  Lemma llftl_idx_bor_guard' κ i Px G :
    llft_ctx -∗ &{ κ, i } Px -∗
      (G &&{llft_wsatG}&&> @[κ]) -∗
      (G &&{llft_wsatG}&&> idx_bor_tok i) -∗
      G &&{llft_wsatG}&&> (@[κ] ∗ bor_sem Px).
  Proof.
    destruct i as [sn κ']. unseal_bor.
    iIntros "_ [#Incls #Slice] #Galive #Gtok".
    iDestruct "Slice" as (Px') "[#PEq #slice]".
    iDestruct (st_iff_iff with "PEq") as "#PEquiv".
    iDestruct (st_incl_incl with "Incls") as "#Incl".
    (* Combine the slice's guard with the one for the main invariant. *)
    iDestruct (guard_wsat_out (W:=llft_inv_main) (W':=llft_inv_main)
      (P:=True%I)) as "#gmain".
    iDestruct (sinv_tok_guard (sm := λ γ Qx, slice_body bor_sem γ Qx)
      with "slice") as "#gslice".
    iDestruct (guard_sep_wsat with "gslice gmain") as "#gB".
    iDestruct (guard_wsat_incl (W:=llft_wsatG) with "gB") as "#gB'".
    iAssert (G &&{llft_wsatG}&&> ∃ a, guard_body sn Px' a)%I as "#g1".
    { iDestruct (guard_true (P:=G) (W:=llft_wsatG)) as "#gt".
      iDestruct (guard_trans with "gt gB'") as "#gC".
      iAssert ((slice_body bor_sem sn Px' ∗ llft_inv_main)
        &&{llft_wsatG}&&> ∃ a, guard_body sn Px' a)%I as "#gD".
      { iApply guard_intro. iIntros "!> X".
        iDestruct (guard_body_eq_1 with "X") as "X". iFrame "X".
        iIntros "Y". by iApply guard_body_eq_2. }
      iApply (guard_trans with "gC gD"). }
    (* First fact: every atom of [κ ⊓ κ'] is alive. *)
    iDestruct (llftl_incl_glb _ _ κ with "Incl []") as "#Incl2".
    { iApply fguard_refl. }
    iDestruct (fguard_here with "Incl2") as "#Incl2h".
    iDestruct (guard_trans with "Galive Incl2h") as "#GaliveM".
    iDestruct (guard_exist_strengthen
      (S := λ a, ⌜set_map LtAtomSwell κ ∪ set_map LtAtomSwell κ'
                   ⊆ a.1.1.1⌝%I) with "GaliveM g1") as "#g2".
    { intros a. iIntros "A".
      iAssert (∀ k, ⌜ k ∈ κ ∪ κ' → LtAtomSwell k ∈ a.1.1.1 ⌝)%I
        with "[A]" as "%J".
      { iIntros (k) "%Hk".
        iApply (lt_state_alive llft_name (LtAtomSwell k) a.1.1.1 a.1.1.2).
        iSplit.
        { iDestruct "A" as "[_ [H _]]".
          iDestruct "H" as (log ol pend) "[A _]". iFrame. }
        { iDestruct "A" as "[A _]". unseal.
          iDestruct (big_sepS_elem_of_acc _ (κ' ⊓ κ) k with "A") as "[$ _]".
          unfold meet, llft_intersect. set_solver. } }
      iPureIntro. intro x. rewrite elem_of_union !elem_of_map.
      intros [[x0 [Heq Hin]]|[x0 [Heq Hin]]]; subst x; apply J; set_solver. }
    (* Second fact: the slice is full.  The bookkeeping's own dead set is
      behind the shared one, so a lifetime the caller holds a token for is
      not dead there either - which is all [guard_helper2] needs. *)
    iDestruct (guard_exist_strengthen
      (S := λ a, ⌜a.2 = true⌝%I) with "Gtok g2") as "#g3".
    { intros a. iIntros "A".
      iApply (guard_helper2 sn κ' a.2
        (lv_alive a.1.2) (lv_dead a.1.2) (lv_blocked a.1.2)). iSplit.
      - iDestruct "A" as "[$ _]".
      - iDestruct "A" as "[_ [[H [Box _]] %Hfacts]]".
        iDestruct "H" as (log ol pend)
          "(LtState & Alive & Auth & Ol & Del & %pure & MA & Lv)".
        destruct pure as [Hsd [_ [_ _]]].
        iDestruct (LtState_disjoint with "LtState") as "%Hdisj".
        iDestruct (lv_log_prefix with "Auth Lv") as "%Hpre".
        iDestruct "Lv" as "(%Hwfs & #Lb & #Mint & Inv & Blk)".
        iFrame "Inv Box". iPureIntro.
        have Hdsub : lv_dead a.1.2 ⊆ a.1.1.2.
        { rewrite Hsd. by apply lv_dead_sub. }
        apply (disj_of_alive _ a.1.1.1 a.1.1.2); [set_solver|done|done]. }
    (* Now read the borrowed proposition off. *)
    iApply (guard_trans with "g3"). iApply guard_intro. iIntros "!> X".
    iDestruct "X" as (a) "[[B %Hsub] %Hb]".
    destruct a as [[[sa sd] s] b]. simpl in Hsub, Hb. subst b.
    iDestruct "B" as "[H [BoxAuth P]]".
    iDestruct "H" as (log ol pend)
      "(LtState & Alive & Auth & Ol & Del & %pure & MA & Lv)".
    rewrite (llft_alive_subset_split (set_map LtAtomSwell κ) sa);
      last by set_solver.
    iDestruct "Alive" as "[Alive1 Alive2]".
    iSplitL "Alive1 P".
    { iSplitL "Alive1". { by iApply llft_alive_set_map_1. }
      by iApply "PEquiv". }
    iIntros "[Alive1 P]".
    iDestruct (llft_alive_set_map_2 with "Alive1") as "Alive1".
    iExists (sa, sd, s, true). simpl.
    iSplitR ""; last by iPureIntro.
    iSplitR ""; last by iPureIntro.
    rewrite /guard_body /=. iSplitR "BoxAuth P"; last first.
    { iFrame "BoxAuth". by iApply "PEquiv". }
    iExists log, ol, pend.
    iFrame "LtState Auth Ol Del MA Lv". iSplitL "Alive1 Alive2"; last first.
    { iPureIntro. exact pure. }
    rewrite (llft_alive_subset_split (set_map LtAtomSwell κ) sa);
      last by set_solver. iFrame.
  Qed.

  Lemma llftl_idx_bor_guard κ i Px :
    llft_ctx -∗ &{ κ, i } Px -∗
      (@[κ] ∗ &{ κ, i } Px ∗ idx_bor_tok i) &&{llft_wsatG}&&>
        (@[κ] ∗ bor_sem Px).
  Proof.
    iIntros "#ctx #idx". iApply (llftl_idx_bor_guard' with "ctx idx").
    - iApply guard_intro. iIntros "!> (A & B & C)". iFrame. by iIntros "$".
    - iApply guard_intro. iIntros "!> (A & B & C)". iFrame. by iIntros "$".
  Qed.

  Lemma llftl_idx_bor_iff κ i Px Px' :
    st_iff Px Px' -∗ &{κ,i} Px -∗ &{κ,i} Px'.
  Proof.
    destruct i as [sn κ'']. unseal_bor. iIntros "#Eq [#Incl #S]".
    iDestruct "S" as (Px'') "[#Eq' slice]". iFrame "Incl". iExists Px''.
    iFrame "slice". iApply (st_iff_trans with "Eq' Eq").
  Qed.

  (** Derived rules about full borrows *)

  Lemma llftl_bor_shorten κ κ' Px :
      st_incl κ' κ -∗ &{κ} Px -∗ &{κ'} Px.
  Proof.
      rewrite llftl_bor_idx. rewrite llftl_bor_idx.
      iIntros "#incl fb". iDestruct "fb" as (idx) "[idx tok]".
      iDestruct (llftl_idx_shorten κ κ' with "incl idx") as "idx".
      iExists idx. iFrame.
  Qed.

  Lemma llftl_bor_iff κ Px Px' :
    st_iff Px Px' -∗ &{κ} Px -∗ &{κ} Px'.
  Proof.
    rewrite !llftl_bor_idx. iIntros "#HP Hbor".
    iDestruct "Hbor" as (i) "[Hbor Htok]". iExists i. iFrame "Htok".
    iApply llftl_idx_bor_iff; done.
  Qed.

  (** Reborrowing *without* an inclusion: the result lives at [κ ⊓ κ'],
    which needs nothing of the caller.  [llftl_reborrow] shortens it, and
    that *does* need a storable inclusion, since the result is a borrow. *)
  Lemma llftl_reborrow_meet E κ κ' Px :
      llft_ctx -∗ &{κ} Px -∗ |=[llft_wsat]{E}=>
        &{κ ⊓ κ'} Px ∗
          ([†κ'] -∗ |=[llft_wsat]{↑NllftUsr ∪ ↑NllftUsr2}=> &{κ} Px).
  Proof.
      iIntros "#ctx fb". rewrite llftl_bor_idx.
      iDestruct "fb" as (idx) "[#idx tok]". destruct idx as [sn κ2].
      iMod (llftl_borrow κ'
        (bor_state_fml sn (Borrow (set_map LtAtomSwell κ2) {[default_dead]}))
        with "ctx [tok]") as "[tokbor back]".
      { by iApply bi.equiv_entails_1_2; [apply bor_state_fml_sem|]. }
      iMod (llftl_idx_bor_unnest E κ κ' (sn, κ2) Px with "ctx idx tokbor")
        as "fullbor".
      iModIntro. iFrame "fullbor".
      iIntros "#dead". iMod ("back" with "dead") as "tok". iModIntro.
      iExists (sn, κ2). iFrame "idx".
      by iApply bi.equiv_entails_1_1; [apply bor_state_fml_sem|].
  Qed.

  Lemma llftl_reborrow E κ κ' Px :
      llft_ctx -∗ st_incl κ' κ -∗ &{κ} Px -∗ |=[llft_wsat]{E}=>
        &{κ'} Px ∗
          ([†κ'] -∗ |=[llft_wsat]{↑NllftUsr ∪ ↑NllftUsr2}=> &{κ} Px).
  Proof.
      iIntros "#ctx #incl fb".
      iMod (llftl_reborrow_meet E κ κ' Px with "ctx fb") as "[fullbor $]".
      iModIntro. iApply (llftl_bor_shorten with "[] fullbor").
      iApply st_incl_glb. { iFrame "incl". } iApply st_incl_refl.
  Qed.

  Lemma llftl_bor_freeze `{!Inhabited T} E κ (Pxs : T → FML $oi Σ) Qx :
      ↑NllftUsr ∪ ↑NllftUsr2 ⊆ E →
      (bor_sem Qx ⊣⊢ ∃ x : T, bor_sem (Pxs x)) →
      llft_ctx -∗ &{κ} Qx -∗ |=[llft_wsat]{E}=> ∃ x : T, &{κ} (Pxs x).
  Proof.
      intros HE Hsem.
      have Hs1 := bi.equiv_entails_1_1 _ _ Hsem.
      have Hs2 := bi.equiv_entails_1_2 _ _ Hsem.
      iIntros "#ctx fb". rewrite /modw. iIntros "Wsat".
      iMod (llftl_bor_acc_atomic E Qx κ with "ctx fb Wsat")
        as "[[P back]|[Wsat #dead]]".
      - iDestruct (Hs1 with "P") as (x) "P".
        iMod ("back" $! (Pxs x) with "[] P") as "[Wsat fb]".
        { iIntros "[P k]". iModIntro. iApply Hs2. by iExists x. }
        iModIntro. iFrame "Wsat". by iExists x.
      - iApply (fupd_mask_mono (↑NllftUsr ∪ ↑NllftUsr2)); [done|].
        iDestruct (llftl_bor_fake κ (Pxs inhabitant) with "ctx dead") as "X".
        iMod ("X" with "Wsat") as "[Wsat fb]".
        iModIntro. iFrame "Wsat". by iExists inhabitant.
  Qed.

  Lemma llftl_bor_pers_from_wand E κ Px (Q : iProp Σ) `{!Persistent Q} :
      ↑NllftUsr ∪ ↑NllftUsr2 ⊆ E →
      llft_ctx -∗ &{κ} Px -∗ (bor_sem Px -∗ Q) -∗ |=[llft_wsat]{E}=>
        &{κ} Px ∗ (Q ∨ [†κ]).
  Proof.
      intros HE. iIntros "#ctx fb wand". rewrite /modw. iIntros "Wsat".
      iMod (llftl_bor_acc_atomic E Px κ with "ctx fb Wsat")
        as "[[P back]|[Wsat #dead]]".
      - iDestruct ("wand" with "P") as "#Q".
        iMod ("back" $! Px with "[] P") as "[Wsat fb]".
        { iIntros "[P2 dead]". by iFrame. }
        iModIntro. iFrame "Wsat fb". iLeft. iFrame "Q".
      - iApply (fupd_mask_mono (↑NllftUsr ∪ ↑NllftUsr2)); [done|].
        iDestruct (llftl_bor_fake κ Px with "ctx dead") as "X".
        iMod ("X" with "Wsat") as "[Wsat fb]".
        iModIntro. iFrame "Wsat fb". iRight. iFrame "dead".
  Qed.

  Lemma llftl_bor_pers_from_wand2 E κ Px (Q R : iProp Σ) `{!Persistent Q} :
      ↑NllftUsr ∪ ↑NllftUsr2 ⊆ E →
      llft_ctx -∗ &{κ} Px -∗ (R -∗ bor_sem Px -∗ Q) -∗ R -∗
        |=[llft_wsat]{E}=> &{κ} Px ∗ (Q ∨ [†κ]) ∗ R.
  Proof.
      intros HE. iIntros "#ctx fb wand R". rewrite /modw. iIntros "Wsat".
      iMod (llftl_bor_acc_atomic E Px κ with "ctx fb Wsat")
        as "[[P back]|[Wsat #dead]]".
      - iDestruct ("wand" with "R P") as "#Q".
        iMod ("back" $! Px with "[] P") as "[Wsat fb]".
        { iIntros "[P2 dead]". by iFrame. }
        iModIntro. iFrame "Wsat fb R". iLeft. iFrame "Q".
      - iApply (fupd_mask_mono (↑NllftUsr ∪ ↑NllftUsr2)); [done|].
        iDestruct (llftl_bor_fake κ Px with "ctx dead") as "X".
        iMod ("X" with "Wsat") as "[Wsat fb]".
        iModIntro. iFrame "Wsat fb R". iRight. iFrame "dead".
  Qed.

  Lemma llftl_bor_pers E κ Px `{!Persistent (bor_sem Px)} :
      ↑NllftUsr ∪ ↑NllftUsr2 ⊆ E →
      llft_ctx -∗ &{κ} Px -∗ |=[llft_wsat]{E}=>
        &{κ} Px ∗ (bor_sem Px ∨ [†κ]).
  Proof.
      intros HE. iIntros "#ctx fb".
      iApply (llftl_bor_pers_from_wand E κ Px (bor_sem Px) HE
        with "ctx fb []").
      by iIntros "$".
  Qed.

  Lemma llftl_bor_simple_atomic E Px κ :
    llft_ctx -∗ &{κ} Px -∗ llft_wsat -∗ |={E}=>
        (bor_sem Px ∗ (bor_sem Px ==∗ llft_wsat ∗ &{κ} Px))
        ∨ (llft_wsat ∗ [†κ]).
  Proof.
    iIntros "ctx bor Wsat".
    iMod (llftl_bor_acc_atomic E Px κ with "ctx bor Wsat")
      as "[[P back]|[Wsat dead]]".
    - iModIntro. iLeft. iFrame "P". iIntros "P".
      iApply ("back" $! Px with "[] P"). by iIntros "[$ _]".
    - iModIntro. iRight. iFrame.
  Qed.

  (** LeLiLo-Bor-Unnest.  The borrowed borrow is given syntactically: [Sx idx]
    denotes the (persistent) indexed borrow and the borrow-state formula
    denotes its token.  Note the conclusion is a plain update: the original
    needed [|={E}▷=>] only because the inner borrow sat under a later. *)
  Lemma llftl_bor_unnest E κ κ' Px (Sx : Idx → FML $oi Σ) Qx :
      ↑NllftUsr ∪ ↑NllftUsr2 ⊆ E →
      (∀ idx, bor_sem (Sx idx) ⊣⊢ &{κ, idx} Px) →
      (bor_sem Qx ⊣⊢ ∃ idx : Idx, bor_sem (bor_sep (Sx idx)
          (bor_state_fml idx.1
            (Borrow (set_map LtAtomSwell idx.2) {[default_dead]})))) →
      llft_ctx -∗ &{κ'} Qx -∗ |=[llft_wsat]{E}=> &{κ ⊓ κ'} Px.
  Proof.
      intros HE HS HQ.
      assert (∀ i0, Persistent (bor_sem (Sx i0))) as Hpers.
      { intros i0. rewrite (HS i0). apply _. }
      iIntros "#ctx fb".
      iMod (llftl_bor_freeze E κ' (λ idx, bor_sep (Sx idx)
        (bor_state_fml idx.1
          (Borrow (set_map LtAtomSwell idx.2) {[default_dead]}))) Qx HE HQ
        with "ctx fb") as (idx) "fb".
      iMod (llftl_sep_split E (Sx idx) (bor_state_fml idx.1
        (Borrow (set_map LtAtomSwell idx.2) {[default_dead]})) κ'
        with "ctx fb") as "[fb1 fb2]".
      iMod (llftl_bor_pers E κ' (Sx idx) HE with "ctx fb1")
        as "[fb1 [#idxbor|#dead]]".
      - iDestruct (bi.equiv_entails_1_1 _ _ (HS idx) with "idxbor")
          as "#idxbor'".
        destruct idx as [sn κ2].
        iApply (llftl_idx_bor_unnest E κ κ' (sn, κ2) Px with "ctx idxbor' fb2").
      - rewrite /modw. iIntros "Wsat".
        iDestruct (llftl_bor_fake (κ ⊓ κ') Px with "ctx []") as "X".
        { rewrite llftl_end_inter. by iRight. }
        iApply (fupd_mask_mono (↑NllftUsr ∪ ↑NllftUsr2)); [done|].
        by iApply "X".
  Qed.

  (** Guarded accessors

    To use the guarded accessor laws without incurring a later, Leaf has to go
    through a non-swell temporary lifetime, because ending a swell lifetime
    costs a step.  Later-free, no lifetime costs a step, but the construction
    is kept as it is also what makes the guard's left-hand side a token. *)

  (* begin hide *)
  Local Lemma llftl_guarded_tok_to_tmp E Gx κ :
    llft_ctx -∗
    (bor_sem Gx &&{llft_wsatG}&&> @[κ]) -∗
    bor_sem Gx -∗ |=[llft_wsat]{E}=> ∃ κ' : gset lt_atom,
        (llft_alive_def' κ' &&{llft_wsatG}&&> @[κ]) ∗
        llft_alive_def' κ' ∗
        □ (llft_alive_def' κ' -∗
            |=[llft_wsat]{↑NllftUsr ∪ ↑NllftUsr2}=> llft_dead_def' κ') ∗
        (llft_dead_def' κ' -∗ |=[llft_wsatG]=> bor_sem Gx).
  Proof.
    iIntros "#ctx #Gk G".
    iMod (llftl_begin_maybe_swell' false with "ctx") as (κ1) "A1".
    iMod (llftl_borrow_shared_maybe_swell ({[ LtAtomNotSwell κ1 ]}) Gx
      with "G") as "[#G1 back]".
    iDestruct (guard_trans with "G1 Gk") as "#Incl".
    iModIntro. iExists ({[ LtAtomNotSwell κ1 ]}). iFrame "Incl".
    iSplitL "A1". { by iApply llft_alive_sing_2. }
    iSplitR; last first.
    { iIntros "A". iApply ("back" with "A"). }
    iIntros "!> Alive". iDestruct (llft_alive_sing_1 with "Alive") as "Alive".
    iMod (llftl_end_maybe_swell' (LtAtomNotSwell κ1) with "ctx Alive") as "D".
    iModIntro. rewrite /llft_dead_def'. iExists (LtAtomNotSwell κ1). iFrame "D".
    iPureIntro. set_solver.
  Qed.
  (* end hide *)

  Lemma llftl_bor_idx_acc_guarded E Gx κ idx Px :
    llft_ctx -∗
    &{κ, idx} Px -∗
    idx_bor_tok idx -∗
    (bor_sem Gx &&{llft_wsatG}&&> @[κ]) -∗
    bor_sem Gx -∗ |=[llft_wsat]{E}=>
        bor_sem Px ∗ (bor_sem Px -∗
          |=[llft_wsat]{↑NllftUsr ∪ ↑NllftUsr2}=> idx_bor_tok idx ∗ bor_sem Gx).
  Proof.
    iIntros "#ctx #bor tok #Gk G".
    iMod (llftl_guarded_tok_to_tmp E Gx κ with "ctx Gk G")
      as (κ') "(#Incl & Alive & #Kill & Back)".
    iMod (llftl_bor_idx_acc_maybe_swell E Px κ' idx with "ctx [] tok Alive")
      as "[P Pback]".
    { destruct idx as [sn κ2]. unseal_bor. rewrite /idx_bor_def'.
      iDestruct "bor" as "[B1 B2]". iSplitR; last by iApply st_slice_raw.
      iDestruct (st_incl_incl with "B1") as "#B1'".
      iApply (fguard_trans with "[] B1'"). by iApply fguard_of_here. }
    iModIntro. iFrame "P". iIntros "P". iMod ("Pback" with "P") as "[tok alive]".
    iMod ("Kill" with "alive") as "X".
    iMod ("Back" with "X") as "G". iModIntro. iFrame.
  Qed.

  Lemma llftl_bor_acc_guarded E Gx κ Px :
    llft_ctx -∗
    &{κ} Px -∗
    (bor_sem Gx &&{llft_wsatG}&&> @[κ]) -∗
    bor_sem Gx -∗ |=[llft_wsat]{E}=>
        bor_sem Px ∗ (∀ Qx,
          (bor_sem Qx ={↑NllftUsr ∪ ↑NllftUsr2}=∗ bor_sem Px) -∗ bor_sem Qx -∗
          |=[llft_wsat]{↑NllftUsr ∪ ↑NllftUsr2}=> (&{κ} Qx) ∗ bor_sem Gx).
  Proof.
    iIntros "#ctx bor #Gk G".
    iMod (llftl_guarded_tok_to_tmp E Gx κ with "ctx Gk G")
      as (κ') "(#Incl & Alive & #Kill & Back)".
    iDestruct (fguard_of_here with "Incl") as "#Inclf".
    iMod (llftl_bor_acc_maybe_swell' E Px κ' κ with "ctx Inclf bor Alive")
      as "[P Pback]".
    iModIntro. iFrame "P". iIntros (Qx) "vs Q".
    iMod ("Pback" $! Qx with "vs Q") as "[fb alive]".
    iMod ("Kill" with "alive") as "X". iMod ("Back" with "X") as "G".
    iModIntro. iFrame.
  Qed.

End LlftLogic.

(** Initializing the lifetime logic

  Leaf allocates two Iris invariants here ([Nmain] and [NllftO]); later-free,
  the same content becomes the world satisfaction [llft_wsat], which the client
  threads instead of opening. *)

(** The ghost state is allocated *before* the interpretation and the
  client's guarding world satisfaction are known, and both are taken
  afterwards: [verus_halt_WG] mentions [llctx_interp], which needs the
  [llft_logicGS] this very call allocates, and [bor_sem] in the model is
  [⟦⟧ᶜ(der)], whose [Csem] needs the ghost state too.  The lemma never looks
  inside either, so handing them in last breaks the cycle. *)
(** The shared half's persistent witnesses.

  Everything a *further* execution level needs to know about the state
  that is already there: that [default_dead] has been minted and is
  dead, that the empty list is a prefix of the kill order, and that the
  empty outlives relation is within the shared one.  All four are
  persistent, and [llft_bor_wsat_alloc] is what consumes them. *)
Definition llft_shared_wits {Σ : gFunctors} `{!llft_logicGS Σ} : iProp Σ :=
  Minted mint_name {[default_dead]} ∗
  mono_list_lb_own log_name ([] : list lt_atom) ∗
  Dead llft_name default_dead ∗ Osub osub_name ∅.

#[export] Instance llft_shared_wits_persistent {Σ} `{!llft_logicGS Σ} :
  Persistent (llft_shared_wits (Σ:=Σ)).
Proof. exact _. Qed.

Lemma llft_wsat_alloc {Σ : gFunctors} {FML : oFunctor} {hlc}
  `{!llft_logicGpreS Σ, !sinvGpreS FML Σ, !invGS_gen hlc Σ,
    !Inhabited (FML $oi Σ)} :
  ⊢ |==> ∃ (_ : llft_logicGS Σ) (_ : LlftBorNames Σ) (_ : sinvGS FML Σ)
      (shr_name : gname),
    llft_shared_wits ∗
    ∀ (BorSem0 : BorSem FML Σ) (WG : iProp Σ)
      (Wix : Type) (Wmore : Wix → iProp Σ), WG -∗
      llft_wsat (LlftWG0 := LlftWGS Σ shr_name WG Wix Wmore).
Proof.
  (* the two halves of [LtRa] now allocate at two names, and the kill
    order gets one of its own *)
  iMod lt_alloc as (γ) "J".
  iMod bor_alloc as (γb) "[Ab Modulo]".
  iMod (outlives_alloc ∅) as (γo) "[O1 O2]".
  iMod (outlives_alloc ∅) as (γos) "[Os1 Os2]".
  iMod (delayed_alloc None) as (γd) "[D1 D2]".
  iMod (mono_list_own_alloc ([] : list lt_atom)) as (γlog) "[Auth #Lb0]".
  iMod (own_alloc (● ({[default_dead]} : gsetUR lt_atom)
      ⋅ ◯ ({[default_dead]} : gsetUR lt_atom))) as (γmint) "[MA #Mint0]".
  { by apply auth_both_valid_discrete. }
  iMod (own_alloc (● (∅ : gsetUR (gset lt_atom * lt_atom))
      ⋅ ◯ (∅ : gsetUR (gset lt_atom * lt_atom)))) as (γosub) "[OAuth #Osub0]".
  { by apply auth_both_valid_discrete. }
  iMod (new_lt γ default_dead ∅ ∅ with "J") as "J"; [set_solver|set_solver|].
  iMod (kill_lt γ default_dead with "J") as "[J #dd]".
  iMod (modulo_dead_new γb default_dead ∅ with "Modulo") as "Modulo".
  iMod sinv_wsat_alloc as (Hbox) "Wbox".
  iMod sinv_wsat_alloc_name as (shr_name) "Wshr".
  iModIntro.
  iExists (LlftLogicG _ _ γ γd γlog γmint γos γosub),
    (LlftBorNamesS Σ γb γo), Hbox, shr_name.
  rewrite /llft_shared_wits. iSplitR; [by iFrame "Mint0 Lb0 dd Osub0"|].
  iIntros (BorSem0 WG Wix Wmore) "WG".
  iDestruct ("Wbox" $! (λ γ' Px, slice_body bor_sem γ' Px) with "[]") as "Wbox".
  { iIntros (?). iApply ne_internal_ne. solve_proper. }
  iDestruct ("Wshr" $! (λ _ Px, bor_sem Px) with "[]") as "Wshr".
  { iIntros (?). iApply ne_internal_ne. solve_proper. }
  rewrite /llft_wsat /llft_wsatG /shr_wsat /llft_inv_other /llft_outlives
    /llft_inv_main /box_wsat /llft_shr_name /llft_WG /=.
  iFrame "WG Wshr Wbox".
  iSplitR "D2 O2 Os2 OAuth"; last first.
  { iExists ∅, ∅. iFrame "Os2 D2 OAuth O2 Osub0".
    rewrite /llft_outlives_guards_at. iIntros (o) "%Ho". set_solver. }
  iExists ∅, {[default_dead]}, [], ∅, None,
    (LvState {[default_dead]} [] ∅).
  rewrite /llft_inv_main_at.
  replace ((∅ ∪ {[default_dead]}) ∖ {[default_dead]}) with (∅ : gset lt_atom);
    last by set_solver.
  replace (∅ ∪ {[default_dead]}) with ({[default_dead]} : gset lt_atom);
    last by set_solver.
  iFrame "J Auth Os1 D1 MA". rewrite /llft_alive_def' !big_sepS_empty.
  iSplitR; first by done.
  iSplitR.
  { iPureIntro. split.
    { rewrite /log_sd /pend_sd /=. set_solver. }
    split; [done|]. split; [done|].
    intros o3 Ho3. set_solver. }
  have Hd0 : lv_dead (LvState {[default_dead]} [] ∅) = {[default_dead]}.
  { rewrite /lv_dead /=. set_solver. }
  rewrite /lv_inv /lv_wf /lv_alive Hd0 /= !big_sepS_empty.
  iSplitR. { iPureIntro. set_solver. }
  iSplitR. { iExact "Lb0". }
  iSplitR. { iExact "Mint0". }
  iSplitL; last by done.
  replace (({[default_dead]} ∖ {[default_dead]}) : gset lt_atom)
    with (∅ : gset lt_atom) by set_solver.
  iExists ∅, ∅, emp%I, ∅.
  iFrame "Ab O1 Modulo".
  iSplitR.
  { iIntros "!>" (d) "%Hd".
    have ->: d = default_dead by set_solver. iFrame "dd". }
  iSplitL. { rewrite /boxmap fmap_empty. iApply box_alloc. }
  iSplitL. { rewrite future_vs_def. iIntros (k) "[%Hk _]". set_solver. }
  iSplitL.
  { iPureIntro. split; trivial. split.
    - rewrite /inv.map_wf.
      split. { set_solver. }
      split. { set_solver. }
      split. { set_solver. }
      split. { intros sn bs Hl. rewrite lookup_empty in Hl. discriminate. }
      split. { intros sn1 bs1 sn2 bs2 Hne Hl. rewrite lookup_empty in Hl.
        discriminate. }
      intros o Ho. set_solver.
    - intros o Ho. set_solver. }
  rewrite big_sepM_empty. done.
Qed.

(** ** A further execution level's borrow machinery

  [llft_wsat_alloc] allocates the shared state and *one* level together.
  A second level needs its own borrow bookkeeping, box and shared-borrow
  family over the *same* lifetime algebra, kill order, minted set and
  outlives authority - which is exactly what [LlftBorNames] separates
  out, and exactly the shape [typing/level_ctx.v] needs to build
  [∗_{k<j} Wbor_k].

  The new level starts at the **empty prefix** of the kill order, and
  that is sound only because a level may lag: [lv_inv] asks that its log
  be *some* prefix of the shared one, not that it be level with it, and
  a rule that needs an atom dead at this level catches it up first
  ([level.lv_catch_up_to_log]).  Before that change this lemma could not
  have been stated, because a fresh level would have had to be born
  knowing every kill that had already happened.

  The four hypotheses are the shared half's witnesses, all persistent. *)
Lemma llft_bor_wsat_alloc {Σ : gFunctors} {FML : oFunctor} {hlc}
  `{!llft_logicGS Σ, !sinvGpreS FML Σ, !invGS_gen hlc Σ,
    !Inhabited (FML $oi Σ)} :
  llft_shared_wits -∗
  |==> ∃ (bn : LlftBorNames Σ) (box : sinvGS FML Σ) (shr : gname),
    ∀ (BorSem0 : BorSem FML Σ) (WG : iProp Σ)
      (Wix : Type) (Wmore : Wix → iProp Σ),
      @llft_bor_wsat Σ FML _ hlc _ box BorSem0 (LlftWGS Σ shr WG Wix Wmore) bn
      ∗ @llft_bor_other Σ _ bn.
Proof.
  iIntros "#(Mint0 & Lb0 & dd & Osub0)".
  iMod bor_alloc as (γb) "[Ab Modulo]".
  iMod (outlives_alloc ∅) as (γo) "[O1 O2]".
  iMod (modulo_dead_new γb default_dead ∅ with "Modulo") as "Modulo".
  iMod sinv_wsat_alloc as (Hbox) "Wbox".
  iMod sinv_wsat_alloc_name as (shr) "Wshr".
  iModIntro. iExists (LlftBorNamesS Σ γb γo), Hbox, shr.
  iIntros (BorSem0 WG Wix Wmore).
  iDestruct ("Wbox" $! (λ γ' Px, slice_body bor_sem γ' Px) with "[]") as "Wbox".
  { iIntros (?). iApply ne_internal_ne. solve_proper. }
  iDestruct ("Wshr" $! (λ _ Px, bor_sem Px) with "[]") as "Wshr".
  { iIntros (?). iApply ne_internal_ne. solve_proper. }
  rewrite /llft_bor_wsat /llft_bor_other /llft_outlives /shr_wsat
    /llft_bor_inv /box_wsat /llft_shr_name /=.
  iFrame "Wshr Wbox".
  iSplitR "O2"; last first.
  { iExists ∅. iFrame "O2". iExact "Osub0". }
  iExists (LvState {[default_dead]} [] ∅).
  have Hd0 : lv_dead (LvState {[default_dead]} [] ∅) = {[default_dead]}.
  { rewrite /lv_dead /=. set_solver. }
  rewrite /lv_inv /lv_wf /lv_alive Hd0 /= !big_sepS_empty.
  iSplitR. { iPureIntro. set_solver. }
  iSplitR. { iExact "Lb0". }
  iSplitR. { iExact "Mint0". }
  iSplitL; last by done.
  replace (({[default_dead]} ∖ {[default_dead]}) : gset lt_atom)
    with (∅ : gset lt_atom) by set_solver.
  iExists ∅, ∅, emp%I, ∅.
  have He : (∅ ∪ {[default_dead]} : gset lt_atom) = {[default_dead]}
    by set_solver.
  rewrite He.
  iFrame "Ab O1 Modulo".
  iSplitR.
  { iIntros "!>" (d) "%Hd".
    have ->: d = default_dead by set_solver. iFrame "dd". }
  iSplitL. { rewrite /boxmap fmap_empty. iApply box_alloc. }
  iSplitL. { rewrite future_vs_def. iIntros (k) "[%Hk _]". set_solver. }
  iSplitL.
  { iPureIntro. split; trivial. split.
    - rewrite /inv.map_wf.
      split. { set_solver. }
      split. { set_solver. }
      split. { set_solver. }
      split. { intros sn bs Hl. rewrite lookup_empty in Hl. discriminate. }
      split. { intros sn1 bs1 sn2 bs2 Hne Hl. rewrite lookup_empty in Hl.
        discriminate. }
      intros o Ho. set_solver.
    - intros o Ho. set_solver. }
  rewrite big_sepM_empty. done.
Qed.

Notation "@[ κ ]" := (llft_alive κ) (format "@[ κ ]") : bi_scope.
Notation "[† κ ]" := (llft_dead κ) (format "[† κ ]") : bi_scope.

(** [llft_incl], [full_bor] and [idx_bor] take their arguments in an order the
  notations cannot express before [LlftWG] is fixed, so the typing layer
  defines them (see [nola.verus_halt.typing.ctx]). *)
