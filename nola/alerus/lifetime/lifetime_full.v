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

From nola.alerus Require Import boxes own_and.
From nola.alerus.lifetime Require Import ra inv augment_outlives new_lt expire_lt
  iff join split reborrow unborrow unnest.
From nola.bi Require Import guard modw.
From nola.iris Require Export iprop sinv.
From nola.iris Require Import point guard.
Require Import stdpp.base.
Require Import stdpp.namespaces.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import excl.
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
  llft_boxG : boxG Σ
}.

Class llft_logicGS Σ := LlftLogicG {
  llft_in_preG : llft_logicGpreS Σ;

  llft_name : gname;
  o_name : gname;
  d_name : gname;
}.
Global Existing Instance llft_in_preG.

Local Existing Instance llft_boxG.
Local Existing Instance llft_logic_inG.

Definition llft_logicΣ : gFunctors := #[
  ra.llft_logicΣ ;
  boxΣ
].

Global Instance subG_lt_logicΣ Σ : subG llft_logicΣ Σ → llft_logicGpreS Σ.
Proof. solve_inG. Qed.

Section LlftLogic.
  Context {Σ: gFunctors} {FML : oFunctor}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS_gen hlc Σ}.
  Context `{!sinvGS FML Σ, !BorSem FML Σ}.
  (** The user's guarding world satisfaction, Leaf's [↑NllftG] minus the
    lifetime logic's own invariants. *)
  Context (WG : iProp Σ).

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

  (** The main part of the lifetime invariant: Leaf's [↑Nmain]. *)
  Definition llft_inv_main : iProp Σ :=
    ∃ (sa sd blocked : gset lt_atom),
      LtState llft_name sa sd
        ∗ llft_alive_def' sa
        ∗ outer_inv llft_name o_name d_name sa sd blocked
        ∗ llft_alive_def' blocked.

  (** The world satisfaction that lifetime inclusion guards live at. *)
  Definition llft_wsatG : iProp Σ := WG ∗ box_wsat bor_sem ∗ llft_inv_main.

  (** The rest of the lifetime invariant: Leaf's [↑NllftO].  Note that the
    stored inclusion guards are at [llft_wsatG], which does not contain this. *)
  Definition llft_inv_other : iProp Σ :=
    ∃ outlives, Delayed d_name None ∗ Outlives o_name outlives
      ∗ (∀ o, ⌜o ∈ outlives⌝ -∗
          (llft_alive_def' o.1 &&{llft_wsatG}&&> Alive llft_name o.2)).

  (** The full world satisfaction of the lifetime logic. *)
  Definition llft_wsat : iProp Σ := llft_wsatG ∗ llft_inv_other.

  #[export] Instance wsat_incl_llft_wsat :
    WsatIncl llft_wsat llft_wsatG llft_inv_other.
  Proof. done. Qed.
  #[export] Instance wsat_incl_llft_wsatG_G :
    WsatIncl llft_wsatG WG (box_wsat bor_sem ∗ llft_inv_main).
  Proof. done. Qed.
  #[export] Instance wsat_incl_llft_wsatG_box :
    WsatIncl llft_wsatG (box_wsat bor_sem) (WG ∗ llft_inv_main).
  Proof. rewrite /WsatIncl /llft_wsatG. iSplit.
    - iIntros "($ & $ & $)".
    - iIntros "($ & $ & $)".
  Qed.
  #[export] Instance wsat_incl_llft_wsatG_main :
    WsatIncl llft_wsatG llft_inv_main (WG ∗ box_wsat bor_sem).
  Proof. rewrite /WsatIncl /llft_wsatG. iSplit.
    - iIntros "($ & $ & $)".
    - iIntros "($ & $ & $)".
  Qed.

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

  (** Definitions of the lifetime tokens. *)

  Definition llft_alive (κ : lft) : iProp Σ := llft_alive_def κ.
  Definition llft_dead (κ : lft) : iProp Σ := llft_dead_def κ.

  Local Ltac unseal := rewrite /llft_alive /llft_alive_def
    /llft_dead /llft_dead_def /llft_ctx.

  Local Instance pers_dead2 γlt k : Persistent (Dead γlt k).
  Proof. apply own_core_persistent. unfold CoreId. trivial. Qed.

  Notation "@[ κ ]" := (llft_alive κ) (format "@[ κ ]") : bi_scope.
  Notation "[† κ ]" := (llft_dead κ) (format "[† κ ]") : bi_scope.

  (** LeLiLo-Incl-Guard *)
  Definition llft_incl (κ1 κ2 : lft) : iProp Σ :=
      @[ κ1 ] &&{llft_wsatG}&&> @[ κ2 ].

  Infix "⊑" := llft_incl (at level 70) : bi_scope.

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
      ((∃ sa sd blocked : gset lt_atom, ⌜ κ ⊆ sa ⌝ ∗ LtState llft_name sa sd
          ∗ llft_alive_def' sa
          ∗ outer_inv llft_name o_name d_name sa sd blocked
          ∗ llft_alive_def' blocked)
       ∨ (∃ sa sd blocked : gset lt_atom, ⌜ ¬(κ ⊆ sa) ⌝ ∗ LtState llft_name sa sd
          ∗ llft_alive_def' sa
          ∗ outer_inv llft_name o_name d_name sa sd blocked
          ∗ llft_alive_def' blocked)))%I as "#ctx'".
    { iApply (guard_trans with "ctx"). iApply guard_intro. iIntros "!> T".
      iSplitL.
      - iDestruct "T" as (sa sd blocked) "T".
        have h : Decision (κ ⊆ sa) by solve_decision. destruct h as [h|n].
        + iLeft. iExists sa, sd, blocked. iFrame. by iPureIntro.
        + iRight. iExists sa, sd, blocked. iFrame. by iPureIntro.
      - iIntros "[T|T]".
        + iDestruct "T" as (sa sd blocked) "[_ T]". by iExists sa, sd, blocked.
        + iDestruct "T" as (sa sd blocked) "[_ T]". by iExists sa, sd, blocked. }
    (* The left disjunct guards [False], so it can be cancelled. *)
    iAssert ((∃ sa sd blocked : gset lt_atom, ⌜ κ ⊆ sa ⌝ ∗ LtState llft_name sa sd
          ∗ llft_alive_def' sa
          ∗ outer_inv llft_name o_name d_name sa sd blocked
          ∗ llft_alive_def' blocked) &&{llft_wsatG}&&> False)%I as "#GF".
    { iApply (guard_trans with "[] G2"). iApply guard_intro.
      iIntros "!> T". iDestruct "T" as (sa sd blocked) "[%ksa [state [alive rest]]]".
      rewrite (llft_alive_subset_split κ sa ksa).
      iDestruct "alive" as "[alive1 alive2]". iFrame "alive1". iIntros "alive1".
      iExists sa, sd, blocked. iSplitR; first by iPureIntro. iFrame "state".
      iSplitL "alive1 alive2".
      { rewrite (llft_alive_subset_split κ sa ksa). iFrame. }
      iFrame "rest". }
    iDestruct (guard_or_false with "ctx' GF") as "#G3".
    (* Now open the guard and produce the dead token. *)
    rewrite /modw. iIntros "Wsat".
    iDestruct (guard_acc with "G3 [//] Wsat") as "[J back]".
    iDestruct "J" as (sa sd blocked) "[%k_sa [State [alive [ou Blo]]]]".
    have the_k := not_subset_eq_get κ sa k_sa. destruct the_k as [k [k_in k_not_in]].
    have h : Decision (k ∈ sd) by solve_decision. destruct h as [h|n].
    - iDestruct (LtState_entails_Dead llft_name k sa sd with "State") as "#deadk";
        first done.
      iDestruct ("back" with "[State alive ou Blo]") as "[Wsat _]".
      { iExists sa, sd, blocked. iFrame. by iPureIntro. }
      iFrame "Wsat". iModIntro. iExists k. iFrame "deadk". by iPureIntro.
    - (* weird technicality: if [k] was never made alive in the first place,
        first create it, then immediately kill it *)
      iMod (new_lt llft_name k sa sd with "State") as "[State [al1 al2]]";
        [done|done|].
      iMod (kill_lt llft_name k (sa ∪ {[ k ]}) sd with "[State al1 al2]")
        as "[State #deadk]". { iFrame. }
      iDestruct (outer_instant_kill_lt llft_name o_name d_name sa sd blocked k
        with "[ou]") as "ou". { set_solver. } { iFrame. iFrame "deadk". }
      iMod (fupd_mask_mono with "ou") as "ou". { set_solver. }
      iDestruct ("back" with "[State alive ou Blo]") as "[Wsat _]".
      { iExists sa, (sd ∪ {[k]}), blocked.
        replace (((sa ∪ {[k]}) ∖ {[k]})) with sa by set_solver.
        iFrame. by iPureIntro. }
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
       - rewrite /llft_incl /llft_alive /llft_alive_def /llft_alive_def'.
         do 2 rewrite big_sepS_set_map. iFrame "Incl".
       - rewrite /llft_dead /llft_dead_def /llft_dead_def'.
         iDestruct "A" as (k) "[%Hin Dead]". iExists (LtAtomSwell k).
         iFrame "Dead". iPureIntro. rewrite elem_of_map. exists k; split; trivial.
       - rewrite /modw. iIntros "W". iMod ("J" with "W") as "[$ J2]". iModIntro.
         rewrite /llft_dead /llft_dead_def /llft_dead_def'.
         iDestruct "J2" as (k) "[%Hin Dead]".
         rewrite elem_of_map in Hin. destruct Hin as [k0 [Heq Hin]]. subst k.
         iExists k0. iFrame "Dead". done.
  Qed.

  Lemma llftl_intersect_incl_l κ κ' : ⊢ (κ ⊓ κ') ⊑ κ.
  Proof.
    rewrite /llft_incl. iApply guard_intro. unseal. iIntros "!> Alive".
    replace (κ ∪ κ') with (κ ∪ ((κ ∪ κ') ∖ κ)).
    - rewrite big_sepS_union.
      + iDestruct "Alive" as "[A1 A2]". iFrame "A1". iIntros "A3". iFrame.
      + set_solver.
    - symmetry. apply union_difference_L. set_solver.
  Qed.

  Lemma llftl_intersect_incl_r κ κ' : ⊢ (κ' ⊓ κ) ⊑ κ.
  Proof.
    replace (κ' ⊓ κ) with (κ ⊓ κ') by (unfold meet, llft_intersect; set_solver).
    apply llftl_intersect_incl_l.
  Qed.

  Lemma llftl_incl_trans κ κ' κ'' : ⊢ κ ⊑ κ' -∗ κ' ⊑ κ'' -∗ κ ⊑ κ''.
  Proof. apply guard_trans. Qed.

  Lemma llftl_incl_glb κ κ' κ'' :
      κ ⊑ κ' -∗ κ ⊑ κ'' -∗ κ ⊑ (κ' ⊓ κ'').
  Proof.
    iIntros "A B".
    iApply (guard_and (S:=@[κ' ⊓ κ'']%I) with "A B").
    unseal. do 3 rewrite -big_sepS_set_map.
    rewrite set_map_inter. apply alive_and_bigSepS.
  Qed.

  Lemma llftl_incl_weaken_lhs_l κ κ' κ'' :
      κ ⊑ κ' ⊢ (κ ⊓ κ'') ⊑ κ'.
  Proof.
    iIntros "#incl". iApply (guard_trans with "[] incl").
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
      iIntros "[[WG [Box Main]] Other]".
      iDestruct "Main" as (sa sd blocked) "[State [Alive [Ou Blo]]]".
      assert (∃ k , (if b then LtAtomSwell k else LtAtomNotSwell k) ∉ (sa ∪ sd))
        as Fres. {
          exists (fresh (set_map atom_unwrap (sa ∪ sd) : gset nat)).
          destruct b.
           - apply atom_not_in_swell. apply is_fresh.
           - apply atom_not_in_not_swell. apply is_fresh.
      }
      destruct Fres as [k Fres].
      iDestruct "Other" as (outlives) "[Delayed [O1 O2]]".
      iDestruct (outer_new_lt llft_name o_name d_name sa sd blocked
        (if b then LtAtomSwell k else LtAtomNotSwell k) with "[Ou Delayed]")
        as "X"; first by set_solver. { iFrame "Ou Delayed". }
      iMod ("X" with "Box") as "[Box [Ou Delayed]]".
      iMod (new_lt llft_name (if b then LtAtomSwell k else LtAtomNotSwell k) sa sd
        with "State") as "[State [A1 A2]]"; [set_solver|set_solver|].
      iModIntro. iFrame "WG Box". iSplitR "A2"; last by iExists k; iFrame "A2".
      iSplitR "Delayed O1 O2"; last by iExists outlives; iFrame.
      iExists (sa ∪ {[ (if b then LtAtomSwell k else LtAtomNotSwell k) ]}), sd, blocked.
      iFrame "State Ou Blo". rewrite /llft_alive_def'.
      replace ((sa ∪ {[ (if b then LtAtomSwell k else LtAtomNotSwell k) ]}))
        with (({[ (if b then LtAtomSwell k else LtAtomNotSwell k) ]} ∪ sa))
        by set_solver.
      rewrite big_sepS_insert; last by set_solver. iFrame.
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
      iIntros "[[WG [Box Main]] Other]".
      iDestruct "Other" as (outlives1) "[Delayed [O1 O2]]".
      iDestruct "Main" as (sa1 sd1 blocked1) "[State Alive]".
      iAssert (⌜k ∈ sa1⌝)%I as "%k_sa1".
      { iApply (lt_state_alive llft_name k sa1 sd1). iSplit.
        { iFrame "State". } iFrame "token". }
      iDestruct (LtState_disjoint llft_name _ _ with "State") as "%Hdisj".
      rewrite {1}/llft_alive_def' (big_sepS_delete _ sa1 k); last done.
      iDestruct "Alive" as "[[token2 Alive] [Ou Blo]]".
      iMod (kill_lt llft_name k sa1 sd1 with "[State token token2]")
        as "[State #dead]". { iFrame. }
      iDestruct (outer_kill_lt_step1 llft_name o_name d_name sa1 sd1 blocked1 k
        with "[Ou Delayed]") as "X"; [done|set_solver| |].
      { iFrame "Ou Delayed". }
      iMod ("X" with "Box") as "[Box [Ou Delayed]]".
      destruct (decide (filter (λ (o: (gset lt_atom * lt_atom)) ,
          o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1 = ∅)).
      {
        assert (∀ other , (other, k) ∈ outlives1 → ¬(other ⊆ sa1 ∖ {[k]}))
          as Houtlives.
        { intros other. intros Hin Hdisj2.
          assert ((other,  k) ∈ filter (λ o : gset lt_atom * lt_atom,
            o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1) as X.
          { rewrite elem_of_filter. set_solver. } rewrite e in X. set_solver. }
        destruct (decide (k ∈ blocked1)). {
          iDestruct (big_sepS_delete _ _ k with "Blo") as "[B Blo]"; trivial.
          iExFalso. iApply (lt_alive_dead_false llft_name k). iSplit.
          { iFrame. } iFrame "dead".
        }
        iDestruct (outer_kill_lt_step2 llft_name o_name d_name
          (sa1 ∖ {[k]}) (sd1 ∪ {[k]}) blocked1 outlives1 k (sa1 ∖ {[k]}) true
          with "[Ou Delayed O1]") as "X"; [done|done| | |].
        { intros other Hin Hsub. by apply (Houtlives other). }
        { iFrame "Ou Delayed O1". iFrame "dead". }
        iMod ("X" with "Box") as "[Box [Ou [Outlives Delayed]]]".
        iModIntro. iFrame "WG Box dead". iSplitR "Outlives Delayed O2".
        { iExists (sa1 ∖ {[k]}), (sd1 ∪ {[k]}), blocked1. iFrame. }
        iExists outlives1. iFrame.
      }
      (* case: something violates the outlives relation. derive a contradiction. *)
      assert (∃ (x : gset lt_atom * lt_atom) , x ∈ filter
        (λ o : gset lt_atom * lt_atom, o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1)
        as Hex_x. { apply set_choose_L; trivial. }
      destruct Hex_x as [[oalive odead] Hex].
      rewrite elem_of_filter in Hex. simpl in Hex.
      destruct Hex as [[Hex1 Hex2] Hex3]. subst odead.
      iDestruct ("O2" $! ((oalive, k)) with "[]") as "#Oguard".
      { iPureIntro; trivial. }
      iDestruct (llftl_incl_dead_implies_dead_unswell
        (↑NllftUsr ∪ ↑NllftUsr2) oalive {[k]} with "[] [] []") as "OdeadUpd".
      { done. }
      { simpl. rewrite /llft_alive_def' big_sepS_singleton. iFrame "Oguard". }
      { rewrite /llft_dead_def'. iExists k. iFrame "dead". iPureIntro. set_solver. }
      iMod ("OdeadUpd" with "[WG Box State Alive Ou Blo]") as "[WsatG #Odead]".
      { rewrite /llft_wsatG. iFrame "WG Box".
        iExists (sa1 ∖ {[k]}), (sd1 ∪ {[k]}), blocked1. iFrame. }
      iDestruct "WsatG" as "[WG [Box Main]]".
      iDestruct "Main" as (sa2 sd2 blocked2) "[State [Alive [Ou Blo]]]".
      iDestruct "Ou" as (opt_k) "[Delayed2 X]".
      iDestruct (delayed_agree with "[Delayed Delayed2]") as "%Dagree".
      { iFrame "Delayed Delayed2". }
      subst opt_k. iDestruct "X" as "[X1 %Hsa2eq]".
      destruct Hsa2eq as [_ [_ Hsa2eq]]. subst sa2.
      iDestruct (big_sepS_subseteq _ _ oalive with "Alive") as "Alive"; first done.
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

End LlftLogic.
