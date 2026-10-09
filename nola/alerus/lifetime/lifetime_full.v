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
From iris.algebra.lib Require Import excl_auth.
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
  Local Definition shrGS : sinvGS FML Σ := SinvGS FML Σ sinvGS_pre shr_name.
  Context `{!ShrBorSem FML Σ}.
  (** [unnest] needs the formula language to express borrow-state ownership. *)
  Context `{!BorStateFml llft_name}.
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

  (** The main part of the lifetime invariant: Leaf's [↑Nmain]. *)
  Definition llft_inv_main : iProp Σ :=
    ∃ (sa sd blocked : gset lt_atom),
      LtState llft_name sa sd
        ∗ llft_alive_def' sa
        ∗ outer_inv llft_name o_name d_name sa sd blocked
        ∗ llft_alive_def' blocked.

  (** Storage for shared borrows. *)
  Definition shr_wsat : iProp Σ :=
    sinv_wsat (sinvGS0:=shrGS) (λ _ Px, bor_sem Px).

  (** The world satisfaction that lifetime inclusion guards live at. *)
  Definition llft_wsatG : iProp Σ :=
    WG ∗ shr_wsat ∗ box_wsat bor_sem ∗ llft_inv_main.

  (** The rest of the lifetime invariant: Leaf's [↑NllftO].  Note that the
    stored inclusion guards are at [llft_wsatG], which does not contain this. *)
  Definition llft_outlives (outlives : outlives_set) : iProp Σ :=
    Outlives o_name outlives ∗
      (∀ o, ⌜o ∈ outlives⌝ -∗
        (llft_alive_def' o.1 &&{llft_wsatG}&&> Alive llft_name o.2)).

  Definition llft_inv_other : iProp Σ :=
    ∃ outlives, Delayed d_name None ∗ llft_outlives outlives.

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
      iIntros "[[WG [Shr [Box Main]]] Other]".
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
      iModIntro. iFrame "WG Shr Box". iSplitR "A2"; last by iExists k; iFrame "A2".
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
      iIntros "[[WG [Shr [Box Main]]] Other]".
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
        iModIntro. iFrame "WG Shr Box dead". iSplitR "Outlives Delayed O2".
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
      iMod ("OdeadUpd" with "[WG Shr Box State Alive Ou Blo]")
        as "[WsatG #Odead]".
      { rewrite /llft_wsatG. iFrame "WG Shr Box".
        iExists (sa1 ∖ {[k]}), (sd1 ∪ {[k]}), blocked1. iFrame. }
      iDestruct "WsatG" as "[WG [Shr [Box Main]]]".
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

  (** Shared borrows *)

  Local Lemma shr_fml_sem_1 κ γc Px :
    bor_sem (shr_fml κ γc Px) ⊢ bor_sem Px ∨ (llft_dead_def' κ ∗ CCancel γc).
  Proof. apply bi.equiv_entails_1_1, shr_fml_sem. Qed.
  Local Lemma shr_fml_sem_2 κ γc Px :
    bor_sem Px ∨ (llft_dead_def' κ ∗ CCancel γc) ⊢ bor_sem (shr_fml κ γc Px).
  Proof. apply bi.equiv_entails_1_2, shr_fml_sem. Qed.

  (* begin hide *)
  Local Lemma llftl_borrow_shared_maybe_swell κ (Px : FML $oi Σ) :
      bor_sem Px -∗ |=[llft_wsatG]=>
        (llft_alive_def' κ &&{llft_wsatG}&&> bor_sem Px)
        ∗ (llft_dead_def' κ -∗ |=[llft_wsatG]=> bor_sem Px).
  Proof.
    iIntros "P". iMod new_cancel as (γc) "c1".
    rewrite {1}/modw /llft_wsatG. iIntros "[WG [Shr Rest]]".
    iDestruct (sinv_tok_alloc_suspend (sinvGS0:=shrGS)
      (sm := λ _ Qx, bor_sem Qx) (shr_fml κ γc Px) with "Shr") as (I) "Alloc".
    iMod ("Alloc" $! (fresh I) with "[]") as "[#tok Shr]".
    { iPureIntro. apply is_fresh. }
    iDestruct ("Shr" with "[P]") as "Shr".
    { iApply shr_fml_sem_2. by iLeft. }
    iDestruct (sinv_tok_guard (sinvGS0:=shrGS) (sm := λ _ Qx, bor_sem Qx)
      with "tok") as "#Tguard".
    rewrite -/shr_wsat.
    iDestruct (guard_wsat_incl (W:=llft_wsatG) with "Tguard") as "#Tguard'".
    iModIntro. iFrame "WG Shr Rest". iSplit.
    - (* the guard *)
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
    - (* the reclamation *)
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

  (** LeLiLo-Shr-Pers *)
  Lemma llftl_borrow_shared_persistent κ (Px : FML $oi Σ) :
      Persistent (@[ κ ] &&{llft_wsatG}&&> bor_sem Px).
  Proof. typeclasses eauto. Qed.

  (** Indexed borrows and full borrows *)

  Definition Idx: Type := ra.slice_name * gset nat.

  (* begin hide *)
  Local Definition idx_bor_def' (κ: gset lt_atom) (idx: Idx) (Px: FML $oi Σ)
    : iProp Σ :=
      let (sn, κ') := idx in
        (llft_alive_def' κ &&{llft_wsatG}&&> @[κ'])
          ∗ (∃ Px', □ (bor_sem Px' ↔ bor_sem Px) ∗ sinv_tok sn Px').

  Local Definition idx_bor_def (κ: lft) (idx: Idx) (Px: FML $oi Σ) : iProp Σ :=
      let (sn, κ') := idx in
        κ ⊑ κ' ∗ (∃ Px', □ (bor_sem Px' ↔ bor_sem Px) ∗ sinv_tok sn Px').

  Local Definition full_bor_def (κ: lft) (Px: FML $oi Σ) : iProp Σ :=
      ∃ sn κ' ,
        κ ⊑ κ'
          ∗ (∃ Px', □ (bor_sem Px' ↔ bor_sem Px) ∗ sinv_tok sn Px')
          ∗ OwnBorState llft_name sn
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

  Definition idx_bor_tok (idx: Idx) : iProp Σ :=
      let (sn, κ') := idx in
          OwnBorState llft_name sn
            (Borrow (set_map LtAtomSwell κ') {[default_dead]}).

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
      κ' ⊑ κ -∗ &{κ, idx} Px -∗ &{κ', idx} Px.
  Proof.
      unseal_bor. destruct idx as [sn κ2]. iIntros "#g [#g2 #slice]".
      iFrame "slice". iApply (guard_trans with "g g2").
  Qed.

  (* begin hide *)
  Local Lemma make_everything_alive new sa sd blocked :
      LtState llft_name sa sd
        -∗ llft_alive_def' sa
        -∗ outer_inv llft_name o_name d_name sa sd blocked
        -∗ Delayed d_name None
        -∗ |=[box_wsat bor_sem]=> ∃ sa' ,
        ⌜ new ⊆ sa' ∪ sd ⌝
        ∗ LtState llft_name sa' sd
        ∗ llft_alive_def' sa'
        ∗ outer_inv llft_name o_name d_name sa' sd blocked
        ∗ Delayed d_name None.
  Proof.
    induction new as [|x T ? IH] using set_ind_L.
    - iIntros "State Alive OuInv Delayed". iModIntro. iExists sa. iFrame "OuInv".
      iFrame. iPureIntro. set_solver.
    - iIntros "State Alive OuInv Delayed".
      iMod (IH with "State Alive OuInv Delayed") as "X".
      iDestruct "X" as (sa') "[%HTin [State [Alive [OuInv Delayed]]]]".
      destruct (decide (x ∈ sa' ∪ sd)) as [Hin|Hout].
      + iModIntro. iExists sa'. iFrame "OuInv". iFrame. iPureIntro. set_solver.
      + iMod (outer_new_lt llft_name o_name d_name sa' sd blocked x
          with "[OuInv Delayed]") as "[OuInv Delayed]"; first by set_solver.
        { iFrame "OuInv". iFrame. }
        iMod (new_lt llft_name x sa' sd with "State") as "[State [Al1 Al2]]".
        { set_solver. } { set_solver. }
        iModIntro. iExists (sa' ∪ {[x]}). iFrame "OuInv". iFrame.
        iSplitR.
        { iPureIntro. set_solver. }
        rewrite /llft_alive_def' big_sepS_union; last by set_solver.
        iFrame "Alive". rewrite big_sepS_singleton. iFrame "Al1".
  Qed.

  Local Lemma outer_get_dead alive dead blocked
    : Delayed d_name None -∗ outer_inv llft_name o_name d_name alive dead blocked
      -∗ ⌜default_dead ∈ dead⌝.
  Proof.
    iIntros "Delayed1 OuInv". iDestruct "OuInv" as (opt_k) "[Delayed2 OuInv]".
    iDestruct (delayed_agree with "[Delayed1 Delayed2]") as "%Heq".
      { iFrame "Delayed1". iFrame "Delayed2". }
    subst opt_k.
    iDestruct "OuInv" as (mbs mprops Ptotal outlives) "[_ [_ [_ [_ [%W _]]]]]".
    iPureIntro. unfold inv.map_wf in W. intuition.
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

  Local Lemma llft_augment_outlives sa sd blocked outlives κ κ' :
    (κ ⊆ sa) →
    (κ' ⊆ sa) →
    (llft_alive_def' κ &&{llft_wsatG}&&> llft_alive_def' κ')
    -∗ Delayed d_name None
    -∗ llft_outlives outlives
    -∗ outer_inv llft_name o_name d_name sa sd blocked
    -∗ LtState llft_name sa sd
    -∗ |=[box_wsat bor_sem]=> ∃ outlives' ,
    ⌜ ∀ k : lt_atom, k ∈ κ' → (κ, k) ∈ outlives' ⌝
    ∗ Delayed d_name None
    ∗ llft_outlives outlives'
    ∗ outer_inv llft_name o_name d_name sa sd blocked
    ∗ LtState llft_name sa sd.
  Proof.
    intros Hk Hk'. iIntros "#Hincl Delayed [Outlives #Hf] OuInv LtState".
    iDestruct (inv_get_outlives_condition llft_name o_name sa sd blocked outlives
      with "[Outlives OuInv Delayed]") as "#%Howf".
    { rewrite /outer_inv. iDestruct "OuInv" as (opt_k) "[Delayed1 X]".
      iDestruct (delayed_agree with "[Delayed1 Delayed]") as "%Heq".
      { iFrame "Delayed". iFrame "Delayed1". } subst opt_k. iFrame. }
    iDestruct (inv_get_outlives_consistent llft_name o_name sa sd blocked outlives
      with "[Outlives OuInv Delayed]") as "#%Hoc".
    { rewrite /outer_inv. iDestruct "OuInv" as (opt_k) "[Delayed1 X]".
      iDestruct (delayed_agree with "[Delayed1 Delayed]") as "%Heq".
      { iFrame "Delayed". iFrame "Delayed1". } subst opt_k. iFrame. }
    iDestruct (inv_get_alive_dead_disj llft_name o_name sa sd blocked
      with "[Outlives OuInv Delayed]") as "#%Hdisj".
    { rewrite /outer_inv. iDestruct "OuInv" as (opt_k) "[Delayed1 X]".
      iDestruct (delayed_agree with "[Delayed1 Delayed]") as "%Heq".
      { iFrame "Delayed". iFrame "Delayed1". } subst opt_k. iFrame. }
    iMod (outer_augment_outlives llft_name o_name d_name sa sd blocked outlives
        (outlives ∪ (set_map (λ k, (κ, k)) κ'))
        with "[Delayed Outlives OuInv]") as "[D [OuInv X]]".
    { set_solver. }
    { set_solver. }
    { unfold outlives_consistent. unfold outlives_consistent in Hoc. set_solver. }
    { iFrame. }
    iExists (outlives ∪ (set_map (λ k, (κ, k)) κ')).
    iModIntro. iFrame.
    iSplitR. { iPureIntro. set_solver. }
    iIntros (o) "%Hoin". rewrite elem_of_union in Hoin.
    destruct Hoin as [Hoin_outlives|Hoin_setmap].
    - iApply "Hf". iPureIntro. trivial.
    - rewrite elem_of_map in Hoin_setmap.
      destruct Hoin_setmap as [x [Hoeq Hxin]]. subst o. simpl.
      iApply (guard_trans with "Hincl"). iApply guard_intro. iIntros "!> A".
      rewrite /llft_alive_def'.
      iDestruct (big_sepS_elem_of_acc _ κ' x with "A") as "[$ A]"; first done.
      iIntros "Al". by iApply "A".
  Qed.
  (* end hide *)

  (* begin hide *)
  Local Lemma llftl_idx_acc_fwd E κ idx Px :
      llft_ctx -∗ idx_bor_def' κ idx Px -∗
        idx_bor_tok idx -∗ llft_alive_def' κ -∗ |=[llft_wsat]{E}=> bor_sem Px
          ∗ OwnBorState llft_name (idx.1)
              (Unborrow κ (set_map LtAtomSwell idx.2) {[default_dead]}).
  Proof.
      destruct idx as [sn κ']. iIntros "_ [#Incl #Slice] OwnBor k".
      rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives) "[Delayed O]".
      iDestruct "Main" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iDestruct (make_everything_alive
        (κ ∪ (set_map LtAtomSwell κ') ∪ {[default_dead]}) sa sd blocked
        with "State Alive OuInv Delayed") as "X".
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sa') "[%Hsa [State [Alive [OuInv Delayed]]]]".
      iDestruct (outer_get_dead with "Delayed OuInv") as "%Hdd".
      iDestruct (lt_state_alive_set llft_name κ sa' sd with "[State k]")
        as "%Hksa'". { iFrame. }
      destruct (decide (set_map LtAtomSwell κ' ⊆ sa')) as [Hk'sa'|Hk'sa'].
      { iDestruct (alive_alive_disjoint with "Alive k Blo") as "%Hbldisj";
          first done.
        iDestruct (llft_augment_outlives sa' sd blocked outlives κ
          (set_map LtAtomSwell κ') with "[] Delayed O OuInv State") as "X";
          [done|done| |].
        { rewrite /llft_alive_def' big_sepS_set_map. unseal. iFrame "Incl". }
        iMod ("X" with "Box") as "[Box X]".
        iDestruct "X" as (outlives') "[%Ho' [Delayed [O [OuInv State]]]]".
        iDestruct "Slice" as (Px') "[#PEquiv #Slice']".
        iDestruct "O" as "[Ostate Oguards]".
        iDestruct (outer_unborrow_start llft_name o_name d_name sa' sd blocked
          outlives' sn κ (set_map LtAtomSwell κ') {[default_dead]} Px'
          with "[Delayed OuInv OwnBor Ostate]") as "X".
        { done. } { set_solver. } { set_solver. } { done. } { done. }
        { exact Ho'. }
        { iFrame "Delayed OuInv Ostate OwnBor". iFrame "Slice'". }
        iMod ("X" with "Box") as
          "[Box [Delayed [OuInv [Ostate [OwnBor P]]]]]".
        iModIntro. iFrame "WG Shr Box". iSplitR "P OwnBor"; last first.
        { iFrame "OwnBor". by iApply "PEquiv". }
        iSplitR "Delayed Ostate Oguards"; last by iExists outlives'; iFrame.
        iExists sa', sd, (blocked ∪ κ). iFrame "State Alive OuInv".
        rewrite /llft_alive_def' big_sepS_union; last by set_solver. iFrame. }
      assert (∃ x , x ∈ (set_map LtAtomSwell κ') ∩ sd) as Hex_x.
      { apply set_choose_L.
          assert ((set_map LtAtomSwell κ' : gset lt_atom) ⊆ sa' ∪ sd) as X
            by set_solver.
          set_solver. }
      destruct Hex_x as [x Hex].
      iDestruct (LtState_entails_Dead llft_name x sa' sd with "State")
        as "#Deadx". { set_solver. }
      iDestruct (llftl_incl_dead_implies_dead_unswell E κ
        (set_map LtAtomSwell κ') with "[] [] []") as "HdeadkUpd".
      { done. }
      { rewrite /llft_alive_def' big_sepS_set_map. unseal. iFrame "Incl". }
      { rewrite /llft_dead_def'. iExists x. iFrame "Deadx". iPureIntro.
        set_solver. }
      iMod ("HdeadkUpd" with "[WG Shr Box State Alive OuInv Blo]")
        as "[_ #Hdeadk]".
      { rewrite /llft_wsatG. iFrame "WG Shr Box".
        iExists sa', sd, blocked. iFrame. }
      iExFalso. iApply (llftl_not_own_end_unswell κ with "k Hdeadk").
  Qed.
  (* end hide *)

  Local Instance pers_idx_bor_def' κ idx Px : Persistent (idx_bor_def' κ idx Px).
  Proof. destruct idx. rewrite /idx_bor_def'. typeclasses eauto. Qed.

  (* begin hide *)
  Local Lemma llftl_idx_acc_back_vs κ idx Px Qx :
      llft_ctx -∗ idx_bor_def' κ idx Px -∗
        OwnBorState llft_name (idx.1)
          (Unborrow κ (set_map LtAtomSwell idx.2) {[default_dead]}) -∗
        bor_sem Qx -∗
        (bor_sem Qx ∗ llft_dead_def' κ ={↑NllftUsr ∪ ↑NllftUsr2}=∗ bor_sem Px)
        -∗ |=[llft_wsat]=> ∃ sn, idx_bor_def' κ (sn, idx.2) Qx
            ∗ idx_bor_tok (sn, idx.2) ∗ llft_alive_def' κ.
  Proof.
      destruct idx as [sn κ']. iIntros "_ #idxbor OwnBor Q vs".
      iDestruct "idxbor" as "[#incl #slice]".
      rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives) "[Delayed O]".
      iDestruct "Main" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iDestruct "slice" as (Px') "[#PEquiv #slice']".
      iDestruct (outer_unborrow_end llft_name o_name d_name sa sd blocked sn κ
        (set_map LtAtomSwell κ') {[default_dead]} Px' Qx
        with "[Delayed OuInv OwnBor vs Q]") as "X".
      { apply swell_set_set_map. } { apply swell_set_default_dead. }
      { iFrame "Delayed OuInv OwnBor Q". iFrame "slice'".
        iIntros "A". iMod ("vs" with "A") as "P". iModIntro.
        by iApply "PEquiv". }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn2) "[Delayed [OuInv [OwnBor [#slice2 %Hbl]]]]".
      iAssert (llft_alive_def' (blocked ∖ κ) ∗ llft_alive_def' κ)%I
        with "[Blo]" as "[Blo Ret]".
      { rewrite /llft_alive_def' -big_sepS_union; last by set_solver.
        replace (blocked ∖ κ ∪ κ) with blocked; first by iFrame.
        apply set_eq. intro x. destruct (decide (x ∈ κ)); set_solver. }
      iModIntro. iSplitR "OwnBor Ret".
      { iFrame "WG Shr Box". iSplitR "Delayed O".
        - iExists sa, sd, (blocked ∖ κ). iFrame.
        - iExists outlives. iFrame. }
      iExists sn2. iFrame "Ret OwnBor". rewrite /idx_bor_def'. iFrame "incl".
      iExists Qx. iFrame "slice2". iModIntro. iSplit; by iIntros "$".
  Qed.

  Local Lemma llftl_idx_acc_back_at_same_idx κ idx Px :
      llft_ctx -∗ idx_bor_def' κ idx Px -∗
        OwnBorState llft_name (idx.1)
          (Unborrow κ (set_map LtAtomSwell idx.2) {[default_dead]}) -∗
        bor_sem Px
        -∗ |=[llft_wsat]=> idx_bor_tok idx ∗ llft_alive_def' κ.
  Proof.
      destruct idx as [sn κ']. iIntros "_ #idxbor OwnBor Q".
      iDestruct "idxbor" as "[#incl #slice]".
      rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives) "[Delayed O]".
      iDestruct "Main" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iDestruct "slice" as (Px') "[#PEquiv #slice']".
      iDestruct (outer_unborrow_end_at_same_idx llft_name o_name d_name sa sd
        blocked sn κ (set_map LtAtomSwell κ') {[default_dead]} Px'
        with "[Delayed OuInv OwnBor Q]") as "X".
      { apply swell_set_set_map. } { apply swell_set_default_dead. }
      { iFrame "Delayed OuInv OwnBor". iFrame "slice'". by iApply "PEquiv". }
      iMod ("X" with "Box") as "[Box [Delayed [OuInv [OwnBor %Hbl]]]]".
      iAssert (llft_alive_def' (blocked ∖ κ) ∗ llft_alive_def' κ)%I
        with "[Blo]" as "[Blo Ret]".
      { rewrite /llft_alive_def' -big_sepS_union; last by set_solver.
        replace (blocked ∖ κ ∪ κ) with blocked; first by iFrame.
        apply set_eq. intro x. destruct (decide (x ∈ κ)); set_solver. }
      iModIntro. iSplitR "OwnBor Ret".
      { iFrame "WG Shr Box". iSplitR "Delayed O".
        - iExists sa, sd, (blocked ∖ κ). iFrame.
        - iExists outlives. iFrame. }
      iFrame.
  Qed.

  Lemma llftl_bor_acc_maybe_swell' E Px κ' κ :
      llft_ctx -∗ (llft_alive_def' κ' &&{llft_wsatG}&&> @[κ]) -∗ &{κ} Px -∗
        llft_alive_def' κ' -∗ |=[llft_wsat]{E}=> bor_sem Px ∗
          (∀ Qx, (bor_sem Qx ={↑NllftUsr ∪ ↑NllftUsr2}=∗ bor_sem Px) -∗
            bor_sem Qx -∗ |=[llft_wsat]=> (&{κ} Qx) ∗ llft_alive_def' κ').
  Proof.
    iIntros "#ctx #incl1 fb alive". unseal_bor.
    iDestruct "fb" as (sn κ'') "[#incl [#slice OwnBor]]".
    iDestruct (guard_trans with "incl1 incl") as "incl2".
    iMod (llftl_idx_acc_fwd E κ' (sn, κ'') Px with "ctx [] OwnBor alive")
      as "[P OwnBor]".
      { rewrite /idx_bor_def'. iFrame "#". }
    iModIntro. iFrame "P". iIntros (Qx) "vs Q".
    iMod (llftl_idx_acc_back_vs κ' (sn, κ'') Px Qx
      with "ctx [] OwnBor Q [vs]") as (sn2) "[#bor2 [tok2 alive]]".
      { rewrite /idx_bor_def'. iFrame "#". }
      { iIntros "[Q _]". by iApply "vs". }
    iModIntro. iFrame "alive". iExists sn2, κ''. iFrame "incl tok2".
    rewrite /idx_bor_def'. by iDestruct "bor2" as "[_ $]".
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
    iMod (llftl_idx_acc_fwd E (set_map LtAtomSwell κ) (sn, κ') Px
      with "ctx [] OwnBor [alive]") as "[P OwnBor]".
      { rewrite /idx_bor_def' /llft_alive_def' big_sepS_set_map. unseal.
        iFrame "incl". iFrame "slice". }
      { rewrite /llft_alive_def' big_sepS_set_map. unseal. iFrame "alive". }
    iModIntro. iFrame "P". iIntros (Qx) "vs Q".
    iMod (llftl_idx_acc_back_vs (set_map LtAtomSwell κ) (sn, κ') Px Qx
      with "ctx [] OwnBor Q [vs]") as (sn2) "[#bor2 [tok2 alive]]".
      { rewrite /idx_bor_def' /llft_alive_def' big_sepS_set_map. unseal.
        iFrame "incl". iFrame "slice". }
      { rewrite /llft_dead_def' -dead_def_set_map. unseal. iFrame "vs". }
    iModIntro. iSplitR "alive".
    { iExists sn2, κ'. iFrame "incl tok2". rewrite /idx_bor_def'.
      by iDestruct "bor2" as "[_ $]". }
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
      iDestruct "fb" as (sn κ') "[#Incl [#slice OwnBor]]".
      rewrite {1}/llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives) "[Delayed O]".
      iDestruct "Main" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iDestruct (make_everything_alive
        (set_map LtAtomSwell κ ∪ set_map LtAtomSwell κ') sa sd blocked
        with "State Alive OuInv Delayed") as "X".
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sa') "[%Hsa [State [Alive [OuInv Delayed]]]]".
      iDestruct (outer_get_dead with "Delayed OuInv") as "%Hdd".
      destruct (decide (set_map LtAtomSwell κ ⊆ sa')) as [Hksa'|Hksa']; last first.
      { assert (∃ x , x ∈ (set_map LtAtomSwell κ : gset lt_atom) ∩ sd)
          as Hex_x. { apply set_choose_L. set_solver. }
        destruct Hex_x as [x Hex].
        iDestruct (LtState_entails_Dead llft_name x sa' sd with "State")
          as "#Deadx". { set_solver. }
        iModIntro. iRight. iSplitR "".
        { rewrite /llft_wsat /llft_wsatG. iFrame "WG Shr Box".
          iSplitR "Delayed O".
          - iExists sa', sd, blocked. iFrame.
          - iExists outlives. iFrame. }
        unseal. rewrite dead_def_set_map. iExists x. iFrame "Deadx".
        iPureIntro. set_solver. }
      destruct (decide (set_map LtAtomSwell κ' ⊆ sa')) as [Hk'sa'|Hk'sa']; last first.
      { assert (∃ x , x ∈ (set_map LtAtomSwell κ' : gset lt_atom) ∩ sd)
          as Hex_x. { apply set_choose_L. set_solver. }
        destruct Hex_x as [x Hex].
        iDestruct (LtState_entails_Dead llft_name x sa' sd with "State")
          as "#Deadx". { set_solver. }
        iDestruct (llftl_incl_dead_implies_dead E κ κ'
          with "[] Incl [Deadx]") as "Upd".
        { done. }
        { unseal. rewrite dead_def_set_map. iExists x. iFrame "Deadx".
          iPureIntro. set_solver. }
        iMod ("Upd" with "[WG Shr Box State Alive OuInv Blo]")
          as "[WsatG #Hdeadk]".
        { rewrite /llft_wsatG. iFrame "WG Shr Box".
          iExists sa', sd, blocked. iFrame. }
        iModIntro. iRight. iFrame "Hdeadk".
        rewrite /llft_wsat. iFrame "WsatG". iExists outlives. iFrame. }
      iDestruct (llft_augment_outlives sa' sd blocked outlives
        (set_map LtAtomSwell κ) (set_map LtAtomSwell κ')
        with "[] Delayed O OuInv State") as "X"; [done|done| |].
      { rewrite /llft_alive_def'. do 2 rewrite big_sepS_set_map. unseal.
        iFrame "Incl". }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (outlives') "[%Ho' [Delayed [O [OuInv State]]]]".
      iDestruct "O" as "[Ostate Oguards]".
      iDestruct "slice" as (Px') "[#PEquiv #slice']".
      iDestruct (outer_unborrow_atomic llft_name o_name d_name sa' sd blocked
        outlives' sn (set_map LtAtomSwell κ) (set_map LtAtomSwell κ')
        {[default_dead]} Px' with "[Delayed OuInv OwnBor Ostate]") as "X".
      { done. } { set_solver. } { exact Ho'. }
      { iFrame "Delayed OuInv Ostate OwnBor". iFrame "slice'". }
      iMod ("X" with "Box") as "[Box [P X]]".
      iModIntro. iLeft. iSplitL "P". { by iApply "PEquiv". }
      iIntros (Qx) "vs Q". iDestruct ("X" $! Qx) as "X".
      iDestruct ("X" with "[vs Q]") as "X".
      { iFrame "Q". iIntros "A".
        iMod ("vs" with "[A]") as "Y".
        { unseal. rewrite dead_def_set_map. iFrame "A". }
        iModIntro. by iApply "PEquiv". }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn2) "[Delayed [OuInv [Ostate [OwnBor #slice2]]]]".
      iModIntro. iSplitR "OwnBor".
      { rewrite /llft_wsat /llft_wsatG. iFrame "WG Shr Box".
        iSplitR "Delayed Ostate Oguards".
        - iExists sa', sd, blocked. iFrame.
        - iExists outlives'. iFrame. }
      iExists sn2, κ'. iFrame "Incl OwnBor". iExists Qx. iFrame "slice2".
      iModIntro. iSplit; by iIntros "$".
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
    iIntros "ctx".
    iDestruct (llftl_bor_idx_acc_maybe_swell E Px (set_map LtAtomSwell κ) idx
      with "ctx") as "A".
    destruct idx. unseal_bor. rewrite /idx_bor_def' /llft_incl /llft_alive_def'.
    unseal. rewrite big_sepS_set_map. iFrame "A".
  Qed.

  (* begin hide *)
  Local Lemma llftl_borrow_fwd Px (κ: gset nat) :
      llft_ctx -∗ bor_sem Px -∗ |=[llft_wsat]=> ∃ sn1 sn2 ,
          sinv_tok sn1 Px
          ∗ sinv_tok sn2 Px
          ∗ OwnBorState llft_name sn1
              (Borrow (set_map LtAtomSwell κ : gset lt_atom) {[default_dead]})
          ∗ OwnBorState llft_name sn2
              (Borrow ∅ (set_map LtAtomSwell κ : gset lt_atom)).
  Proof.
      iIntros "_ P". rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives) "[Delayed O]".
      iDestruct "Main" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iDestruct (make_everything_alive (set_map LtAtomSwell κ) sa sd blocked
        with "State Alive OuInv Delayed") as "X".
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sa') "[%Hsa' [State [Alive [OuInv Delayed]]]]".
      iDestruct (outer_borrow_create llft_name o_name d_name sa' sd blocked
        (set_map LtAtomSwell κ) Px with "[Delayed OuInv State P]") as "X".
      { apply swell_set_set_map. } { set_solver. } { iFrame. }
      iMod ("X" with "Box") as "[Box [Delayed X]]".
      iDestruct "X" as (sn1 sn2)
        "[OuInv [State [OwnBor1 [OwnBor2 [#slice1 #slice2]]]]]".
      iModIntro. iSplitR "OwnBor1 OwnBor2".
      { iFrame "WG Shr Box". iSplitR "Delayed O".
        - iExists sa', sd, blocked. iFrame.
        - iExists outlives. iFrame. }
      iExists sn1, sn2. iFrame "OwnBor1 OwnBor2". iFrame "slice1 slice2".
  Qed.

  Local Lemma llftl_borrow_rev Px (κ: gset nat) sn :
      llft_ctx -∗ sinv_tok sn Px -∗
        OwnBorState llft_name sn (Borrow ∅ (set_map LtAtomSwell κ)) -∗ [†κ] -∗
        |=[llft_wsat]=> bor_sem Px.
  Proof.
      iIntros "_ #slice OwnBor #Dead". rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives) "[Delayed O]".
      iDestruct "Main" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iDestruct (make_everything_alive (set_map LtAtomSwell κ) sa sd blocked
        with "State Alive OuInv Delayed") as "X".
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sa') "[%Hsa' [State [Alive [OuInv Delayed]]]]".
      unseal. iDestruct "Dead" as (k) "[%Hkdead Deadkin]".
      iAssert (⌜ LtAtomSwell k ∈ sd ⌝)%I as "%Hksd".
      { iApply (lt_state_dead llft_name (LtAtomSwell k) sa' sd).
        iSplitL; iFrame. iFrame "#". }
      iDestruct "O" as "[Ostate #Oguards]".
      iDestruct (outer_unborrow_start llft_name o_name d_name sa' sd blocked
        outlives sn ∅ ∅ (set_map LtAtomSwell κ) Px
        with "[Delayed OuInv OwnBor Ostate]") as "X".
      { set_solver. } { set_solver. } { set_solver. } { set_solver. }
      { set_solver. } { intros k0. set_solver. }
      { iFrame "OuInv". iFrame "Delayed Ostate OwnBor". iFrame "slice". }
      iMod ("X" with "Box") as "[Box [Delayed [OuInv [Ostate [OwnBor P]]]]]".
      iModIntro. iFrame "P". iFrame "WG Shr Box". iSplitR "Delayed Ostate".
      - iExists sa', sd, blocked. replace (blocked ∪ ∅) with blocked
          by set_solver. iFrame.
      - iExists outlives. iFrame. iFrame "Oguards".
  Qed.

  Local Lemma llftl_weaken sn (κ κ' : gset nat) Px :
      llft_ctx -∗
        OwnBorState llft_name sn
          (Borrow (set_map LtAtomSwell κ) {[default_dead]}) -∗
        sinv_tok sn Px -∗ |=[llft_wsat]=>
          ∃ sn' , OwnBorState llft_name sn'
            (Borrow (set_map LtAtomSwell κ ∪ set_map LtAtomSwell κ')
              {[default_dead]}) ∗ sinv_tok sn' Px.
  Proof.
    iIntros "_ OwnBor #slice". rewrite /modw /llft_wsat /llft_wsatG.
    iIntros "[[WG [Shr [Box Main]]] Other]".
    iDestruct "Other" as (outlives) "[Delayed O]".
    iDestruct "Main" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
    iDestruct (make_everything_alive (set_map LtAtomSwell κ') sa sd blocked
      with "State Alive OuInv Delayed") as "X".
    iMod ("X" with "Box") as "[Box X]".
    iDestruct "X" as (sa') "[%Hsa [State [Alive [OuInv Delayed]]]]".
    iDestruct (outer_reborrow llft_name o_name d_name sa' sd blocked Px sn
      (set_map LtAtomSwell κ) (set_map LtAtomSwell κ')
      with "[Delayed OuInv OwnBor slice]") as "X".
    { apply swell_set_set_map. } { set_solver. }
    { iFrame "Delayed OuInv OwnBor". iFrame "slice". }
    iMod ("X" with "Box") as "[Box X]".
    iDestruct "X" as (sn1 sn2)
      "[Delayed [OuInv [OwnBor1 [OwnBor2 [#slice1 #slice2]]]]]".
    iModIntro. iSplitR "OwnBor1".
    { iFrame "WG Shr Box". iSplitR "Delayed O".
      - iExists sa', sd, blocked. iFrame.
      - iExists outlives. iFrame. }
    iExists sn1. iFrame "OwnBor1". iFrame "slice1".
  Qed.
  (* end hide *)

  (** LeLiLo-Borrow *)
  Lemma llftl_borrow κ Px :
      llft_ctx -∗ bor_sem Px -∗ |=[llft_wsat]=>
        &{κ} Px ∗ ([†κ] -∗ |=[llft_wsat]=> bor_sem Px).
  Proof.
    iIntros "#ctx P". unseal_bor.
    iMod (llftl_borrow_fwd Px κ with "ctx P")
      as (sn1 sn2) "[#slice1 [#slice2 [OwnBor1 OwnBor2]]]".
    iModIntro. iSplitL "OwnBor1".
    { iExists sn1, κ. iFrame "OwnBor1". iSplitR. { iApply guard_refl. }
      iExists Px. iFrame "slice1". iModIntro. iSplit; by iIntros "$". }
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
      iDestruct "Other" as (outlives) "[Delayed O]".
      iDestruct "Main" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iDestruct "slice" as (PQ) "[#PQEquiv #slice']".
      iDestruct (outer_iff llft_name o_name d_name sa sd blocked sn
        (set_map LtAtomSwell κ') {[default_dead]} PQ (bor_sep Px Qx)
        with "[Delayed OuInv OwnBor]") as "X".
      { iFrame "Delayed OuInv OwnBor". iFrame "slice'". iFrame "PQEquiv". }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn0) "[Delayed [OuInv [OwnBor #slice0]]]".
      iDestruct (outer_split llft_name o_name d_name sa sd blocked sn0
        (set_map LtAtomSwell κ') {[default_dead]} Px Qx
        with "[Delayed OuInv OwnBor]") as "X".
      { iFrame "Delayed OuInv OwnBor". iFrame "slice0". }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn1 sn2)
        "[Delayed [OuInv [OwnBor1 [OwnBor2 [#slice1 #slice2]]]]]".
      iModIntro. iSplitR "OwnBor1 OwnBor2".
      { iFrame "WG Shr Box". iSplitR "Delayed O".
        - iExists sa, sd, blocked. iFrame.
        - iExists outlives. iFrame. }
      iSplitL "OwnBor1".
      { iExists sn1, κ'. iFrame "OwnBor1 incl". iExists Px. iFrame "slice1".
        iModIntro. iSplit; by iIntros "$". }
      { iExists sn2, κ'. iFrame "OwnBor2 incl". iExists Qx. iFrame "slice2".
        iModIntro. iSplit; by iIntros "$". }
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
      iDestruct "Other" as (outlives) "[Delayed O]".
      iDestruct "Main" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iDestruct (make_everything_alive ({[default_dead]}) sa sd blocked
        with "State Alive OuInv Delayed") as "X".
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sa') "[%Hsa [State [Alive [OuInv Delayed]]]]".
      iDestruct (outer_join llft_name o_name d_name sa' sd blocked sn1' sn2'
        (set_map LtAtomSwell κ1 ∪ set_map LtAtomSwell κ2) {[default_dead]}
        Px' Qx' with "[Delayed OuInv OwnBor1 OwnBor2]") as "X".
      { apply swell_set_default_dead. } { set_solver. }
      { iFrame "Delayed OuInv OwnBor1 OwnBor2". iFrame "slice1' slice2'". }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn) "[Delayed [OuInv [OwnBor #slice]]]".
      iModIntro. iSplitR "OwnBor".
      { iFrame "WG Shr Box". iSplitR "Delayed O".
        - iExists sa', sd, blocked. iFrame.
        - iExists outlives. iFrame. }
      iExists sn, (κ1 ∪ κ2). rewrite set_map_inter. iFrame "OwnBor".
      iSplitR. { iApply llftl_incl_glb; iFrame "#". }
      iExists (bor_sep Px' Qx'). iFrame "slice". iModIntro.
      rewrite !bor_sep_sem. iSplit; iIntros "[P Q]".
      - iSplitL "P". { by iApply "PEquiv". } { by iApply "QEquiv". }
      - iSplitL "P". { by iApply "PEquiv". } { by iApply "QEquiv". }
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
      iDestruct "Other" as (outlives) "[Delayed O]".
      iDestruct "Main" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iDestruct "slice" as (Px') "[#PEquiv #slice']".
      iDestruct "Hs2" as (Pibt) "[#PibtEquiv #slice2]".
      iDestruct (outer_iff llft_name o_name d_name sa sd blocked sn'
        (set_map LtAtomSwell κ2') {[default_dead]} Pibt
        (bor_state_fml sn (Borrow (set_map LtAtomSwell κ2) {[default_dead]}))
        with "[Delayed OuInv OwnBor2]") as "X".
      { iFrame "Delayed OuInv OwnBor2". iFrame "slice2". iFrame "PibtEquiv". }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn0) "[Delayed [OuInv [OwnBor2 #slice0]]]".
      iDestruct (outer_unnest llft_name o_name d_name sa sd blocked sn sn0
        (set_map LtAtomSwell κ2) (set_map LtAtomSwell κ2') Px'
        with "[Delayed OuInv OwnBor2]") as "X".
      { iFrame "Delayed OuInv OwnBor2". iFrame "slice' slice0". }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn2) "[Delayed [OuInv [OwnBor #slice3]]]".
      iModIntro. iSplitR "OwnBor".
      { iFrame "WG Shr Box". iSplitR "Delayed O".
        - iExists sa, sd, blocked. iFrame.
        - iExists outlives. iFrame. }
      iExists sn2, (κ2 ∪ κ2'). rewrite set_map_inter. iFrame "OwnBor".
      iSplitR.
      { iApply llftl_incl_glb.
        - iApply llftl_incl_weaken_lhs_l. iFrame "incl".
        - iApply llftl_incl_weaken_lhs_r. iFrame "incl2". }
      iExists Px'. iFrame "slice3". iFrame "PEquiv".
  Qed.

  (** LeLiLo-Bor-Fake *)
  Lemma llftl_bor_fake E κ Px :
    llft_ctx -∗ [†κ] -∗ |=[llft_wsat]{E}=> &{κ} Px.
  Proof.
      iIntros "_ #dead". unseal_bor. rewrite /modw /llft_wsat /llft_wsatG.
      iIntros "[[WG [Shr [Box Main]]] Other]".
      iDestruct "Other" as (outlives) "[Delayed O]".
      iDestruct "Main" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      unseal. iDestruct "dead" as (k) "[%HkK deadk]".
      iAssert (⌜LtAtomSwell k ∈ sd⌝)%I as "%Hksd".
      { iApply lt_state_dead. iSplit. { iFrame "State". } iFrame "deadk". }
      iDestruct (outer_fake llft_name o_name d_name sa sd blocked
        (set_map LtAtomSwell κ) {[default_dead]} Px with "[Delayed OuInv]")
        as "X". { set_solver. } { iFrame. }
      iMod ("X" with "Box") as "[Box X]".
      iDestruct "X" as (sn) "[Delayed [OuInv [OwnBor #slice]]]".
      iModIntro. iSplitR "OwnBor".
      { iFrame "WG Shr Box". iSplitR "Delayed O".
        - iExists sa, sd, blocked. iFrame.
        - iExists outlives. iFrame. }
      iExists sn, κ. iFrame "OwnBor". iSplitR. { iApply guard_refl. }
      iExists Px. iFrame "slice". iModIntro. iSplit; by iIntros "$".
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

  Local Lemma guard_helper2 sn κ' b sa sd blocked :
      set_map LtAtomSwell κ' ⊆ sa →
      idx_bor_tok (sn, κ')
      ∧ (inner_inv llft_name o_name sa sd blocked ∗ box_own_auth sn (●E b))
      ⊢ ⌜b = true⌝.
  Proof.
    intros Hsub. iIntros "A". rewrite /inner_inv.
    rewrite bi.sep_exist_r.
    setoid_rewrite bi.sep_exist_r. setoid_rewrite bi.sep_exist_r.
    setoid_rewrite bi.sep_exist_r.
    rewrite bi.and_exist_l.
    setoid_rewrite bi.and_exist_l. setoid_rewrite bi.and_exist_l.
    setoid_rewrite bi.and_exist_l.
    iDestruct "A" as (mbs mprops Ptotal outlives) "A".
    iAssert (⌜sa ## sd ∧ default_dead ∈ sd⌝)%I as "[%Hdisj %Hdd]".
    { iDestruct "A" as "[_ [(? & ? & ? & ? & %Hall & ?) _]]".
      unfold inv.map_wf in Hall. iPureIntro. intuition. }
    iDestruct (agree_bor_state_borrow_lts_and llft_name sn mbs sd
      (set_map LtAtomSwell κ') {[default_dead]} with "[A]") as (de') "%Hde'".
    { set_solver. }
    { iSplit.
      - iDestruct "A" as "[A _]". iFrame "A".
      - iDestruct "A" as "[_ ((? & ? & ?) & ?)]". iFrame. }
    destruct Hde' as [Hmbssn Hx].
    iDestruct "A" as "[_ ((_ & _ & Box & _) & BoxOwnAuth)]".
    assert (boxmap sa sd mbs !! sn = Some true) as Htrue.
    { unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. simpl.
      f_equiv. rewrite bool_decide_eq_true. set_solver. }
    iAssert (⌜true = b⌝)%I with "[Box BoxOwnAuth]" as "%Heq";
      last by iPureIntro.
    iApply (box_own_auth_agree_and (γ:=sn)). iSplit.
    - rewrite /box. iDestruct "Box" as (Φ) "[_ A]".
      rewrite (big_sepM_delete _ _ sn); last by apply Htrue.
      iDestruct "A" as "[[A B] _]". iFrame "A".
    - iFrame "BoxOwnAuth".
  Qed.

  Local Lemma guard_helper1 sn κ' b sa sd blocked :
      idx_bor_tok (sn, κ')
        ∧ (outer_inv llft_name o_name d_name sa sd blocked
              ∗ LtState llft_name sa sd
              ∗ ⌜set_map LtAtomSwell κ' ⊆ sa⌝
              ∗ box_own_auth sn (●E b))
      ⊢ ⌜b = true⌝.
  Proof.
    rewrite /outer_inv. iIntros "A".
    iAssert (⌜set_map LtAtomSwell κ' ⊆ sa⌝)%I as "%Hsub".
    { iDestruct "A" as "[_ (? & ? & ? & ?)]". iFrame. }
    rewrite bi.sep_exist_r. rewrite bi.and_exist_l.
    iDestruct "A" as (opt_k) "A". destruct opt_k as [p|].
    - destruct p as [k alive'].
      iApply (guard_helper2 sn κ' b (sa ∪ {[k]}) (sd ∖ {[k]}) blocked).
      { set_solver. }
      iSplit.
        + iDestruct "A" as "[A _]". iFrame.
        + iDestruct "A" as "[_ ((? & ? & ?) & (? & ? & ?))]". iFrame.
    - iApply (guard_helper2 sn κ' b sa sd blocked). { trivial. }
      iSplit.
        + iDestruct "A" as "[A _]". iFrame.
        + iDestruct "A" as "[_ ((? & ?) & ? & ? & ?)]". iFrame.
  Qed.

  (** The state the guard sees: the main invariant together with the slice's
    own cell, packaged as a single existential so that the persistent facts
    can be pinned down by [guard_exist_strengthen]. *)
  Local Definition guard_body (sn : ra.slice_name) (Px' : FML $oi Σ)
    (a : gset lt_atom * gset lt_atom * gset lt_atom * bool) : iProp Σ :=
    (LtState llft_name a.1.1.1 a.1.1.2 ∗ llft_alive_def' a.1.1.1
      ∗ outer_inv llft_name o_name d_name a.1.1.1 a.1.1.2 a.1.2
      ∗ llft_alive_def' a.1.2)
    ∗ (box_own_auth sn (●E a.2) ∗ (if a.2 then bor_sem Px' else True%I)).

  Local Lemma guard_body_eq_1 sn Px' :
    (slice_body bor_sem sn Px' ∗ llft_inv_main) ⊢ ∃ a, guard_body sn Px' a.
  Proof.
    rewrite /llft_inv_main /slice_body /guard_body.
    iIntros "[(%b & H2) (%sa & %sd & %blocked & H)]".
    iExists (sa, sd, blocked, b). iFrame.
  Qed.
  Local Lemma guard_body_eq_2 sn Px' :
    (∃ a, guard_body sn Px' a) ⊢ slice_body bor_sem sn Px' ∗ llft_inv_main.
  Proof.
    rewrite /llft_inv_main /slice_body /guard_body.
    iIntros "(%a & H1 & H2)". destruct a as [[[sa sd] blocked] b]. simpl.
    iSplitL "H2". { iExists b. iFrame. }
    iExists sa, sd, blocked. iFrame.
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
    iIntros "_ [#Incl #Slice] #Galive #Gtok".
    iDestruct "Slice" as (Px') "[#PEquiv #slice]".
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
    { iApply guard_refl. }
    iDestruct (guard_trans with "Galive Incl2") as "#GaliveM".
    iDestruct (guard_exist_strengthen
      (S := λ a, ⌜set_map LtAtomSwell κ ∪ set_map LtAtomSwell κ'
                   ⊆ a.1.1.1⌝%I) with "GaliveM g1") as "#g2".
    { intros a. iIntros "A".
      iAssert (∀ k, ⌜ k ∈ κ ∪ κ' → LtAtomSwell k ∈ a.1.1.1 ⌝)%I
        with "[A]" as "%J".
      { iIntros (k) "%Hk".
        iApply (lt_state_alive llft_name (LtAtomSwell k) a.1.1.1 a.1.1.2).
        iSplit.
        { iDestruct "A" as "[_ [[A _] _]]". iFrame. }
        { iDestruct "A" as "[A _]". unseal.
          iDestruct (big_sepS_elem_of_acc _ (κ' ⊓ κ) k with "A") as "[$ _]".
          unfold meet, llft_intersect. set_solver. } }
      iPureIntro. intro x. rewrite elem_of_union !elem_of_map.
      intros [[x0 [Heq Hin]]|[x0 [Heq Hin]]]; subst x; apply J; set_solver. }
    (* Second fact: the slice is full. *)
    iDestruct (guard_exist_strengthen
      (S := λ a, ⌜a.2 = true⌝%I) with "Gtok g2") as "#g3".
    { intros a. iIntros "A".
      iApply (guard_helper1 sn κ' a.2 a.1.1.1 a.1.1.2 a.1.2). iSplit.
      - iDestruct "A" as "[$ _]".
      - iDestruct "A" as "[_ [[(LtState & _ & Ou & _) [Box _]] %Hfacts]]".
        iFrame "Ou LtState Box". iPureIntro. set_solver. }
    (* Now read the borrowed proposition off. *)
    iApply (guard_trans with "g3"). iApply guard_intro. iIntros "!> X".
    iDestruct "X" as (a) "[[B %Hsub] %Hb]".
    destruct a as [[[sa sd] blocked] b]. simpl in Hsub, Hb. subst b.
    iDestruct "B" as "[(LtState & Alive & Ou & Blo) [BoxAuth P]]".
    rewrite (llft_alive_subset_split (set_map LtAtomSwell κ) sa);
      last by set_solver.
    iDestruct "Alive" as "[Alive1 Alive2]".
    iSplitL "Alive1 P".
    { iSplitL "Alive1". { by iApply llft_alive_set_map_1. }
      by iApply "PEquiv". }
    iIntros "[Alive1 P]".
    iDestruct (llft_alive_set_map_2 with "Alive1") as "Alive1".
    iExists (sa, sd, blocked, true). simpl.
    iSplitR ""; last by iPureIntro.
    iSplitR ""; last by iPureIntro.
    rewrite /guard_body /=. iFrame "LtState Ou Blo BoxAuth".
    iSplitL "Alive1 Alive2".
    { rewrite (llft_alive_subset_split (set_map LtAtomSwell κ) sa);
        last by set_solver. iFrame. }
    by iApply "PEquiv".
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
    □ (bor_sem Px ↔ bor_sem Px') -∗ &{κ,i} Px -∗ &{κ,i} Px'.
  Proof.
    destruct i as [sn κ']. unseal_bor. iIntros "#Eq [#Incl #S]".
    iDestruct "S" as (Px'') "[#Eq' slice]". iFrame "Incl". iExists Px''.
    iFrame "slice". iModIntro. iSplit.
    - iIntros. iApply "Eq". iApply "Eq'". iFrame.
    - iIntros. iApply "Eq'". iApply "Eq". iFrame.
  Qed.

  (** Derived rules about full borrows *)

  Lemma llftl_bor_shorten κ κ' Px :
      κ' ⊑ κ -∗ &{κ} Px -∗ &{κ'} Px.
  Proof.
      rewrite llftl_bor_idx. rewrite llftl_bor_idx.
      iIntros "#incl fb". iDestruct "fb" as (idx) "[idx tok]".
      iDestruct (llftl_idx_shorten κ κ' with "incl idx") as "idx".
      iExists idx. iFrame.
  Qed.

  Lemma llftl_bor_iff κ Px Px' :
    □ (bor_sem Px ↔ bor_sem Px') -∗ &{κ} Px -∗ &{κ} Px'.
  Proof.
    rewrite !llftl_bor_idx. iIntros "#HP Hbor".
    iDestruct "Hbor" as (i) "[Hbor Htok]". iExists i. iFrame "Htok".
    iApply llftl_idx_bor_iff; done.
  Qed.

  Lemma llftl_reborrow E κ κ' Px :
      llft_ctx -∗ κ' ⊑ κ -∗ &{κ} Px -∗ |=[llft_wsat]{E}=>
        &{κ'} Px ∗ ([†κ'] -∗ |=[llft_wsat]=> &{κ} Px).
  Proof.
      iIntros "#ctx #incl fb". rewrite llftl_bor_idx.
      iDestruct "fb" as (idx) "[#idx tok]". destruct idx as [sn κ2].
      iMod (llftl_borrow κ'
        (bor_state_fml sn (Borrow (set_map LtAtomSwell κ2) {[default_dead]}))
        with "ctx [tok]") as "[tokbor back]".
      { by iApply bi.equiv_entails_1_2; [apply bor_state_fml_sem|]. }
      iMod (llftl_idx_bor_unnest E κ κ' (sn, κ2) Px with "ctx idx tokbor")
        as "fullbor".
      iModIntro. iSplitL "fullbor".
      { iApply (llftl_bor_shorten with "[] fullbor").
        iApply llftl_incl_glb. { iFrame "incl". } iApply guard_refl. }
      iIntros "#dead". iMod ("back" with "dead") as "tok". iModIntro.
      iExists (sn, κ2). iFrame "idx".
      by iApply bi.equiv_entails_1_1; [apply bor_state_fml_sem|].
  Qed.

  Lemma llftl_bor_freeze `{!Inhabited T} E κ (Pxs : T → FML $oi Σ) Qx :
      (bor_sem Qx ⊣⊢ ∃ x : T, bor_sem (Pxs x)) →
      llft_ctx -∗ &{κ} Qx -∗ |=[llft_wsat]{E}=> ∃ x : T, &{κ} (Pxs x).
  Proof.
      intros Hsem.
      have Hs1 := bi.equiv_entails_1_1 _ _ Hsem.
      have Hs2 := bi.equiv_entails_1_2 _ _ Hsem.
      iIntros "#ctx fb". rewrite /modw. iIntros "Wsat".
      iMod (llftl_bor_acc_atomic E Qx κ with "ctx fb Wsat")
        as "[[P back]|[Wsat #dead]]".
      - iDestruct (Hs1 with "P") as (x) "P".
        iMod ("back" $! (Pxs x) with "[] P") as "[Wsat fb]".
        { iIntros "[P k]". iModIntro. iApply Hs2. by iExists x. }
        iModIntro. iFrame "Wsat". by iExists x.
      - iDestruct (llftl_bor_fake E κ (Pxs inhabitant) with "ctx dead") as "X".
        iMod ("X" with "Wsat") as "[Wsat fb]".
        iModIntro. iFrame "Wsat". by iExists inhabitant.
  Qed.

  Lemma llftl_bor_pers_from_wand E κ Px (Q : iProp Σ) `{!Persistent Q} :
      llft_ctx -∗ &{κ} Px -∗ (bor_sem Px -∗ Q) -∗ |=[llft_wsat]{E}=>
        &{κ} Px ∗ (Q ∨ [†κ]).
  Proof.
      iIntros "#ctx fb wand". rewrite /modw. iIntros "Wsat".
      iMod (llftl_bor_acc_atomic E Px κ with "ctx fb Wsat")
        as "[[P back]|[Wsat #dead]]".
      - iDestruct ("wand" with "P") as "#Q".
        iMod ("back" $! Px with "[] P") as "[Wsat fb]".
        { iIntros "[P2 dead]". by iFrame. }
        iModIntro. iFrame "Wsat fb". iLeft. iFrame "Q".
      - iDestruct (llftl_bor_fake E κ Px with "ctx dead") as "X".
        iMod ("X" with "Wsat") as "[Wsat fb]".
        iModIntro. iFrame "Wsat fb". iRight. iFrame "dead".
  Qed.

  Lemma llftl_bor_pers_from_wand2 E κ Px (Q R : iProp Σ) `{!Persistent Q} :
      llft_ctx -∗ &{κ} Px -∗ (R -∗ bor_sem Px -∗ Q) -∗ R -∗
        |=[llft_wsat]{E}=> &{κ} Px ∗ (Q ∨ [†κ]) ∗ R.
  Proof.
      iIntros "#ctx fb wand R". rewrite /modw. iIntros "Wsat".
      iMod (llftl_bor_acc_atomic E Px κ with "ctx fb Wsat")
        as "[[P back]|[Wsat #dead]]".
      - iDestruct ("wand" with "R P") as "#Q".
        iMod ("back" $! Px with "[] P") as "[Wsat fb]".
        { iIntros "[P2 dead]". by iFrame. }
        iModIntro. iFrame "Wsat fb R". iLeft. iFrame "Q".
      - iDestruct (llftl_bor_fake E κ Px with "ctx dead") as "X".
        iMod ("X" with "Wsat") as "[Wsat fb]".
        iModIntro. iFrame "Wsat fb R". iRight. iFrame "dead".
  Qed.

  Lemma llftl_bor_pers E κ Px `{!Persistent (bor_sem Px)} :
      llft_ctx -∗ &{κ} Px -∗ |=[llft_wsat]{E}=>
        &{κ} Px ∗ (bor_sem Px ∨ [†κ]).
  Proof.
      iIntros "#ctx fb".
      iApply (llftl_bor_pers_from_wand E κ Px (bor_sem Px) with "ctx fb []").
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
      (∀ idx, bor_sem (Sx idx) ⊣⊢ &{κ, idx} Px) →
      (bor_sem Qx ⊣⊢ ∃ idx : Idx, bor_sem (bor_sep (Sx idx)
          (bor_state_fml idx.1
            (Borrow (set_map LtAtomSwell idx.2) {[default_dead]})))) →
      llft_ctx -∗ &{κ'} Qx -∗ |=[llft_wsat]{E}=> &{κ ⊓ κ'} Px.
  Proof.
      intros HS HQ.
      assert (∀ i0, Persistent (bor_sem (Sx i0))) as Hpers.
      { intros i0. rewrite (HS i0). apply _. }
      iIntros "#ctx fb".
      iMod (llftl_bor_freeze E κ' (λ idx, bor_sep (Sx idx)
        (bor_state_fml idx.1
          (Borrow (set_map LtAtomSwell idx.2) {[default_dead]}))) Qx HQ
        with "ctx fb") as (idx) "fb".
      iMod (llftl_sep_split E (Sx idx) (bor_state_fml idx.1
        (Borrow (set_map LtAtomSwell idx.2) {[default_dead]})) κ'
        with "ctx fb") as "[fb1 fb2]".
      iMod (llftl_bor_pers E κ' (Sx idx) with "ctx fb1")
        as "[fb1 [#idxbor|#dead]]".
      - iDestruct (bi.equiv_entails_1_1 _ _ (HS idx) with "idxbor")
          as "#idxbor'".
        destruct idx as [sn κ2].
        iApply (llftl_idx_bor_unnest E κ κ' (sn, κ2) Px with "ctx idxbor' fb2").
      - iApply (llftl_bor_fake E (κ ⊓ κ') Px with "ctx []").
        rewrite llftl_end_inter. by iRight.
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
      iDestruct "bor" as "[B1 $]". iApply (guard_trans with "Incl B1"). }
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
    iMod (llftl_bor_acc_maybe_swell' E Px κ' κ with "ctx Incl bor Alive")
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

Lemma llft_wsat_alloc {Σ : gFunctors} {FML : oFunctor} {hlc}
  `{!llft_logicGpreS Σ, !sinvGpreS FML Σ, !invGS_gen hlc Σ, !BorSem FML Σ}
  (WG : iProp Σ) :
  WG ⊢ |==> ∃ (_ : llft_logicGS Σ) (_ : sinvGS FML Σ) (shr_name : gname),
    llft_wsat (LlftWG0 := LlftWGS Σ shr_name WG).
Proof.
  iIntros "WG".
  iMod lt_alloc as (γ) "[J [Ab Modulo]]".
  iMod (outlives_alloc ∅) as (γo) "[O1 O2]".
  iMod (delayed_alloc None) as (γd) "[D1 D2]".
  iMod (new_lt γ default_dead ∅ ∅ with "J") as "J"; [set_solver|set_solver|].
  iMod (kill_lt γ default_dead with "J") as "[J dd]".
  iMod (modulo_dead_new γ default_dead ∅ with "[dd Modulo]") as "Modulo".
  { iFrame. }
  iMod sinv_wsat_alloc as (Hbox) "Wbox".
  iMod sinv_wsat_alloc_name as (shr_name) "Wshr".
  iDestruct ("Wbox" $! (λ γ' Px, slice_body bor_sem γ' Px) with "[]") as "Wbox".
  { iIntros (?). iApply ne_internal_ne. solve_proper. }
  iDestruct ("Wshr" $! (λ _ Px, bor_sem Px) with "[]") as "Wshr".
  { iIntros (?). iApply ne_internal_ne. solve_proper. }
  iModIntro. iExists (LlftLogicG _ _ γ γo γd), Hbox, shr_name.
  rewrite /llft_wsat /llft_wsatG /shr_wsat /llft_inv_other /llft_outlives
    /llft_inv_main /box_wsat /llft_shr_name /llft_WG /=.
  iFrame "WG Wshr Wbox".
  iSplitR "D2 O2"; last first.
  { iExists ∅. iFrame "D2 O2". iIntros (o) "%Ho". set_solver. }
  iExists ∅, {[default_dead]}, ∅.
  replace ((∅ ∪ {[default_dead]}) ∖ {[default_dead]}) with (∅ : gset lt_atom);
    last by set_solver.
  replace (∅ ∪ {[default_dead]}) with ({[default_dead]} : gset lt_atom);
    last by set_solver.
  iFrame "J". rewrite /llft_alive_def' !big_sepS_empty.
  iSplitR; first by done. iSplitL; last by done.
  iExists None. iFrame "D1". iExists ∅, ∅, emp%I, ∅.
  iFrame "Ab O1 Modulo".
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
  defines them (see [nola.alerus.typing.ctx]). *)
