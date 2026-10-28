(** * Lifetime utilities

  Ported from VerusBelt ([typing/lifetime.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  Only [lft_eternalize] really changes.  The original allocates an Iris
  invariant with Leaf's [guards_alloc] and then removes the resulting later
  with [guards_remove_later_rhs]; here the lifetime token is handed to the
  [eternal_wsat] component of [verus_halt_WG] and [eternal_tok_guard] yields the
  guard with no later at all. *)

From nola.verus_halt.typing Require Export base ctx.
From nola.bi Require Import guard modw.
From iris.proofmode Require Import proofmode.
Import GuardNotation ModwNotation.

(** [static], [lft_intersect_list] and [lftO] are in
  [nola.verus_halt.typing.ctx], since the world satisfaction defined there has to
  mention [llctx_interp]. *)

Global Instance lft_intersect_left_id : LeftId eq static meet.
Proof. intros κ; unfold llft_intersect; set_solver. Qed.

Global Instance lft_intersect_right_id : RightId eq static meet.
Proof. intros κ; unfold llft_intersect; set_solver. Qed.

(** Lifetime equivalence, as a pair of *stored* inclusions: it ends up inside
  a type's ghost assertion through [type_incl], which is a formula.  See
  [AltSem] in [typing/ctx.v]. *)
Definition lft_equiv `{!verus_haltGS FML Σ, !VerusHaltSem FML Σ, !GsrcSem FML Σ, !TypeFml FML Σ,
  StBor0 : !StBor FML Σ, StBorSem0 : !StBorSem, !AltSem FML Σ} (κ κ': lft) : iProp Σ := (dincl κ κ' ∗ dincl κ' κ)%I.

Infix "≡ₗ" := lft_equiv (at level 70) : bi_scope.

Section lifetimes.
  Context `{!verus_haltGS FML Σ, !VerusHaltSem FML Σ, !GsrcSem FML Σ, !TypeFml FML Σ, StBor0 : !StBor FML Σ, StBorSem0 : !StBorSem, !AltSem FML Σ}.
  Implicit Type (κ: lft).

  Global Instance lft_intersect_comm : Comm (A:=lft) eq (⊓).
  Proof. unfold meet, llft_intersect. intros ??; set_solver. Qed.
  Global Instance lft_intersect_assoc : Assoc (A:=lft) eq (⊓).
  Proof. unfold meet, llft_intersect. intros ??; set_solver. Qed.

  Lemma lft_incl_static κ : ⊢ κ ⊑ static.
  Proof.
    replace κ with (κ ⊓ static) by (unfold llft_intersect; set_solver).
    by iApply llftl_intersect_incl_r.
  Qed.

  Lemma static_alive_true : @[static] ⊣⊢ True.
  Proof.
    iSplit; iIntros "_"; [done|]. iApply llftl_tok_unit.
  Qed.

  Lemma lft_intersect_list_elem_of_incl κs κ :
    κ ∈ κs → ⊢ lft_intersect_list κs ⊑ κ.
  Proof.
    induction κs as [ | κ' κs' IH ] in κ |- *; first set_solver.
    intros [ -> | Hin ]%elem_of_cons => /=.
    - iApply llftl_incl_weaken_lhs_l. iApply fguard_refl.
    - iApply llftl_incl_weaken_lhs_r. by iApply IH.
  Qed.

  Lemma lft_intersect_list_elem_of_sub κs κ :
    κ ∈ κs → κ ⊆ lft_intersect_list κs.
  Proof.
    induction κs as [ | κ' κs' IH ] in κ |- *; first set_solver.
    move=> /elem_of_cons[->|Hin] /=; unfold meet, llft_intersect;
      [set_solver|]. have := IH _ Hin. set_solver.
  Qed.
  Lemma lft_intersect_list_sub l1 l2 :
    (∀ κ, κ ∈ l1 → κ ∈ l2) → lft_intersect_list l1 ⊆ lft_intersect_list l2.
  Proof.
    induction l1 as [ | κ l1' IH ]=>/= Hsub; [set_solver|].
    unfold meet, llft_intersect. apply union_least.
    - apply lft_intersect_list_elem_of_sub, Hsub, elem_of_cons. by left.
    - apply IH=> ??. apply Hsub, elem_of_cons. by right.
  Qed.

  Lemma lft_intersect_list_app l1 l2 :
    lft_intersect_list (l1 ++ l2) =
      lft_intersect_list l1 ⊓ lft_intersect_list l2.
  Proof.
    induction l1 as [ | κ l1' IH ] in l2 |- * => /=;
      by [rewrite left_id_L| rewrite IH assoc_L].
  Qed.

  Lemma lft_incl_refl κ : ⊢ κ ⊑ κ.
  Proof. iApply fguard_refl. Qed.

  Lemma lft_equiv_refl κ : ⊢ lft_equiv κ κ.
  Proof. by iSplit; iApply dincl_refl. Qed.
  Lemma dincl_static κ : ⊢ dincl κ static.
  Proof. apply dincl_of_sub. unfold static, llft_empty. set_solver. Qed.
  Lemma dincl_intersect_list_elem_of κs κ :
    κ ∈ κs → ⊢ dincl (lft_intersect_list κs) κ.
  Proof. move=> ?. by apply dincl_of_sub, lft_intersect_list_elem_of_sub. Qed.

  Lemma lft_intersect_equiv_idemp κ : ⊢ κ ⊓ κ ≡ₗ κ.
  Proof.
    iSplit; unfold meet, llft_intersect;
      replace (κ ∪ κ) with κ by set_solver; iApply dincl_refl.
  Qed.

  Lemma lft_intersect_mono : ∀ κ1 κ1' κ2 κ2',
    κ1 ⊑ κ1' -∗ κ2 ⊑ κ2' -∗ κ1 ⊓ κ2 ⊑ κ1' ⊓ κ2'.
  Proof.
    iIntros (κ1 κ1' κ2 κ2') "#H1 #H2".
    iApply (llftl_incl_glb with "[H1] [H2]").
    - by iApply llftl_incl_weaken_lhs_l.
    - by iApply llftl_incl_weaken_lhs_r.
  Qed.

  Lemma lft_equiv_sym κ κ' : κ ≡ₗ κ' -∗ κ' ≡ₗ κ.
  Proof. iIntros "[??]". by iSplit. Qed.

  Lemma lft_equiv_trans κ κ' κ'' : ⊢ κ ≡ₗ κ' -∗ κ' ≡ₗ κ'' -∗ κ ≡ₗ κ''.
  Proof.
    iIntros "[H1 H2][H3 H4]". iSplit.
    - iApply (dincl_trans with "H1 H3").
    - iApply (dincl_trans with "H4 H2").
  Qed.

  Lemma lft_intersect_equiv_proper κ1 κ2 κ3 κ4 :
    κ1 ≡ₗ κ3 -∗ κ2 ≡ₗ κ4 -∗ κ1 ⊓ κ2 ≡ₗ κ3 ⊓ κ4.
  Proof.
    iIntros "[#H1 #H2] [#H3 #H4]". iSplit; by iApply dincl_intersect_mono.
  Qed.
  Lemma dincl_equiv_proper κ1 κ2 κ3 κ4 :
    (⊢ κ1 ≡ₗ κ3) → (⊢ κ2 ≡ₗ κ4) → dincl κ1 κ2 ⊣⊢ dincl κ3 κ4.
  Proof.
    move=> H1 H2. iDestruct H1 as "[#A1 #A2]". iDestruct H2 as "[#B1 #B2]".
    iSplit; iIntros "#H".
    - iApply (dincl_trans with "A2"). iApply (dincl_trans with "H B1").
    - iApply (dincl_trans with "A1"). iApply (dincl_trans with "H B2").
  Qed.
  Lemma dincl_equiv_proper_l κ1 κ2 κ3 :
    (⊢ κ1 ≡ₗ κ3) → dincl κ1 κ2 ⊣⊢ dincl κ3 κ2.
  Proof.
    move=> ?. apply dincl_equiv_proper; [done|]. iApply lft_equiv_refl.
  Qed.
  Lemma dincl_equiv_proper_r κ1 κ2 κ3 :
    (⊢ κ2 ≡ₗ κ3) → dincl κ1 κ2 ⊣⊢ dincl κ1 κ3.
  Proof.
    move=> ?. apply dincl_equiv_proper; [|done]. iApply lft_equiv_refl.
  Qed.

  Lemma lft_incl_equiv_proper κ1 κ2 κ3 κ4 :
    (⊢ κ1 ≡ₗ κ3) → (⊢ κ2 ≡ₗ κ4) → κ1 ⊑ κ2 ⊣⊢ κ3 ⊑ κ4.
  Proof.
    intros H1 H2.
    iDestruct H1 as "[A1 A2]". iDestruct (dincl_incl with "A1") as "#A1'".
    iDestruct (dincl_incl with "A2") as "#A2'".
    iDestruct H2 as "[B1 B2]". iDestruct (dincl_incl with "B1") as "#B1'".
    iDestruct (dincl_incl with "B2") as "#B2'".
    iSplit; iIntros "#H".
    - iApply (llftl_incl_trans with "A2' []").
      iApply (llftl_incl_trans with "H B1'").
    - iApply (llftl_incl_trans with "A1' []").
      iApply (llftl_incl_trans with "H B2'").
  Qed.

  Lemma lft_incl_equiv_proper_l κ1 κ2 κ3 :
    (⊢ κ1 ≡ₗ κ3) → κ1 ⊑ κ2 ⊣⊢ κ3 ⊑ κ2.
  Proof.
    intros. apply lft_incl_equiv_proper; [done|]. iApply lft_equiv_refl.
  Qed.

  Lemma lft_incl_equiv_proper_r κ1 κ2 κ3 :
    (⊢ κ2 ≡ₗ κ3) → κ1 ⊑ κ2 ⊣⊢ κ1 ⊑ κ3.
  Proof.
    intros. apply lft_incl_equiv_proper; [|done]. iApply lft_equiv_refl.
  Qed.

  Lemma lft_intersect_list_submseteq_incl κs κs' :
    κs' ⊆+ κs → ⊢ lft_intersect_list κs ⊑ lft_intersect_list κs'.
  Proof.
    elim.
    - exact: lft_incl_refl.
    - move=>/= *. iApply lft_intersect_mono=>//. iApply lft_incl_refl.
    - move=>/= κ κ' ?. rewrite !lft_intersect_assoc (lft_intersect_comm κ κ').
      exact: lft_incl_refl.
    - move=>/= *. by rewrite -llftl_incl_weaken_lhs_r.
    - move=>/= *. by iApply llftl_incl_trans.
  Qed.

  Lemma llftl_tok_unit_equiv : True ⊣⊢ @[ llft_empty ].
  Proof. iSplit; iIntros "_"; [iApply llftl_tok_unit|done]. Qed.

  (** Eternalize a lifetime token.

    The original is [@[κ] ={E}=∗ static ⊑ κ] with [↑NllftG ⊆ E], proved with
    [guards_alloc] and [guards_remove_later_rhs]. *)
  Lemma lft_eternalize κ : @[κ] =[verus_halt_wsat]=∗ static ⊑ κ.
  Proof.
    iIntros "K W".
    rewrite (wsat_incl verus_halt_wsat
      (eternal_wsat verus_halt_eternal_name llft_alive) _).
    iDestruct "W" as "[We Wr]".
    iMod (eternal_tok_alloc with "K We") as "[#tok We]". iModIntro.
    iSplitL "We Wr"; [by iFrame|]. rewrite /llft_incl /static.
    iApply fguard_of_here.
    iApply (guard_wsat_incl (W:=llft_wsatG)
      (W':=eternal_wsat verus_halt_eternal_name llft_alive)).
    iApply (eternal_tok_guard with "tok").
  Qed.

  Lemma lft_bor_idx1 κ P idx :
    idx_bor_tok idx ∗ &{κ, idx} P  ⊢ &{κ} P.
  Proof.
    iIntros "[A B]". iApply llftl_bor_idx. iExists idx. iFrame.
  Qed.
End lifetimes.
