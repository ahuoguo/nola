(** * Program logic, later-free and total

  Ported from VerusBelt ([lang/lifting.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer).

  This is where the later-free rewrite pays off most visibly.  The original
  sets

    num_laters_per_step n := sum_advance_credits (n + 1)

  i.e. it has the machine hand out a *superlinearly growing* budget of later
  credits at every step, and carries a whole time-receipt library
  ([lang/time.v], [⧗ n], [⧖ n], [wp_cumulative_time_receipt*], the [sqr_bound]
  lemmas) whose only job is to produce the credits that strip the laters a
  guard introduces when opened.  With the later-free guard there is nothing to
  strip: [num_laters_per_step' _ := 0], the time-receipt section disappears
  entirely, and the rules are stated for the *total* weakest precondition
  [twpw] of [nola.bi.wpw]. *)

From iris.proofmode Require Import proofmode.
From nola.bi Require Export wpw.
From nola.bi Require Import modw.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From nola.alerus.lang Require Export lang heap.
From nola.alerus.lang Require Import tactics.
From nola.alerus.util Require Import non_atomic_cell_map atomic_lock_counter.
From nola.alerus Require Import na_inv_fork.
From nola.bi Require Import guard.
From iris.prelude Require Import options.
Import uPred ModwNotation WpwNotation GuardNotation.

Open Scope Z_scope.

Class lrustGS_gen hlc FML Σ : Type := LRustGS {
  lrustGS_invGS : invGS_gen hlc Σ;
  #[global] lrustGS_na_invGS :: na_invG Σ;
  #[global] lrustGS_alcGS :: alc_logicG Σ;
  #[global] lrustGS_heapGS :: heapGS FML Σ;
  #[global] lrustGS_naSem :: NaSem FML Σ;
  #[global] lrustGS_heapSem :: HeapSem FML Σ;
}.

(** As in [nola.lrust.lifting], we go through [iris'GS_gen] so that the weakest
  precondition can carry a custom world satisfaction.  Note
  [num_laters_per_step' _ := 0]: the original needed
  [sum_advance_credits (n + 1)]. *)
Global Instance lrustGS_iris'GS `{!lrustGS_gen hlc FML Σ}
  : iris'GS_gen hlc lrust_lang Σ := {
  iris'_invGS := lrustGS_invGS;
  state_interp' σ _ κs _ := heap_ctx σ;
  fork_post' _ := True%I;
  num_laters_per_step' _ := 0%nat;
  state_interp'_mono _ _ _ _ := fupd_intro _ _
}.

Ltac inv_lit :=
  repeat match goal with
  | H : lit_eq _ ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  | H : lit_neq ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  end.

Ltac inv_bin_op_eval :=
  repeat match goal with
  | H : bin_op_eval _ ?c _ _ _ |- _ => is_constructor c; inversion H; clear H;
    simplify_eq/=
  end.

Local Hint Extern 0 (atomic _) => solve_atomic : core.
Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (base_reducible_no_obs _ _) => eexists _, _, _; simpl
  : core.

Local Hint Constructors head_step bin_op_eval lit_neq lit_eq : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Class AsRec (e : expr) (f : binder) (xl : list binder) (erec : expr) : Prop :=
  as_rec : e = Rec f xl erec.
Global Instance AsRec_rec f xl e : AsRec (Rec f xl e) f xl e := eq_refl.
Global Instance AsRec_rec_locked_val v f xl e :
  AsRec (of_val v) f xl e → AsRec (of_val (locked v)) f xl e.
Proof. by unlock. Qed.

Class DoSubst (x : binder) (es : expr) (e er : expr) : Prop :=
  do_subst : subst' x es e = er.
Global Hint Extern 0 (DoSubst _ _ _ _) =>
  rewrite /DoSubst; simpl_subst; reflexivity : typeclass_instances.

Class DoSubstL (xl : list binder) (esl : list expr) (e er : expr) : Prop :=
  do_subst_l : subst_l xl esl e = Some er.
Global Instance do_subst_l_nil e : DoSubstL [] [] e e.
Proof. done. Qed.
Global Instance do_subst_l_cons x xl es esl e er er' :
  DoSubstL xl esl e er' → DoSubst x es er' er →
  DoSubstL (x :: xl) (es :: esl) e er.
Proof. rewrite /DoSubstL /DoSubst /= => -> <- //. Qed.
Global Instance do_subst_vec xl (vsl : vec val (length xl)) e :
  DoSubstL xl (of_val <$> vec_to_list vsl) e (subst_v xl vsl e).
Proof. by rewrite /DoSubstL subst_v_eq. Qed.

Section lifting.
Context `{!lrustGS_gen hlc FML Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types e : expr.
Implicit Types ef : option expr.

(** Split and rejoin the weakest precondition's world satisfaction *)
Local Lemma wsat_split {W W' Wr : iProp Σ} `{!WsatIncl W W' Wr} :
  W ⊢ W' ∗ Wr.
Proof. by rewrite (wsat_incl W W' Wr). Qed.
Local Lemma wsat_join {W W' Wr : iProp Σ} `{!WsatIncl W W' Wr} :
  W' ∗ Wr ⊢ W.
Proof. by rewrite (wsat_incl W W' Wr). Qed.

(** ** Stateless reductions *)
Lemma twp_fork W s E e :
  [[{ WP[W] e @ s; ⊤ [{ _, True }] }]][W] Fork e @ s; E
  [[{ RET LitV LitPoison; True }]].
Proof.
  iIntros (?) "?HΦ". iApply twp_lift_atomic_base_step; [done|].
  iIntros (σ1 ns κs nt) "[$ Hσ] !>". iSplit; first by eauto.
  iIntros (?????) "!>". inv_head_step. iSplit; [done|]. iFrame.
  by iApply "HΦ".
Qed.
Lemma wp_fork W s E e :
  {{{ ▷ WP[W] e @ s; ⊤ {{ _, True }} }}}[W] Fork e @ s; E
  {{{ RET LitV LitPoison; True }}}.
Proof.
  iIntros (?) "?HΦ". iApply wp_lift_atomic_base_step; [done|].
  iIntros (σ1 κ ? κs n) "Hσ !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep) "_"; inv_head_step. iFrame.
  iModIntro. by iApply "HΦ".
Qed.

(** ** Non-determinism *)
Lemma twp_nd_int W s E :
  [[{ True }]][W] NdInt @ s; E [[{ (z : Z), RET (LitV (LitInt z)); True }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (????) "[W ?] !>". iSplit.
  { iPureIntro. eexists _, _, _. apply (NdIntS 0). }
  iIntros (?????). inv_head_step. iModIntro. do 2 (iSplit=>//). iFrame.
  by iApply "HΦ".
Qed.
Lemma wp_nd_int W s E :
  {{{ True }}}[W] NdInt @ s; E {{{ (z : Z), RET (LitV (LitInt z)); True }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_nd_int; [done|]. iIntros (z) "_ HΦ". by iApply "HΦ".
Qed.

(** ** Pure reductions *)
Local Ltac solve_exec_safe :=
  intros; destruct_and?; subst; do 3 eexists; econstructor; simpl; eauto
    with lia.
Local Ltac solve_exec_puredet :=
  simpl; intros; destruct_and?; inv_head_step; inv_bin_op_eval; inv_lit; done.
Local Ltac solve_pure_exec :=
  intros ?; apply nsteps_once, pure_base_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

Global Instance pure_rec e f xl erec erec' el :
  AsRec e f xl erec →
  TCForall AsVal el →
  Closed (f :b: xl +b+ []) erec →
  DoSubstL (f :: xl) (e :: el) erec erec' →
  PureExec True 1 (App e el) erec'.
Proof.
  rewrite /AsRec /DoSubstL=> -> /TCForall_Forall Hel ??. solve_pure_exec.
  eapply Forall_impl; [exact Hel|]. intros e' [v <-]. rewrite to_of_val; eauto.
Qed.

Close Scope nat_scope.

Global Instance pure_le n1 n2 :
  PureExec True 1 (BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)))
                  (Lit (bool_decide (n1 ≤ n2))).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_int n1 n2 :
  PureExec True 1 (BinOp EqOp (Lit (LitInt n1)) (Lit (LitInt n2)))
                  (Lit (bool_decide (n1 = n2))).
Proof. case_bool_decide; solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_r l :
  PureExec True 1 (BinOp EqOp (Lit (LitLoc l)) (Lit (LitInt 0))) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_l l :
  PureExec True 1 (BinOp EqOp (Lit (LitInt 0)) (Lit (LitLoc l))) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance pure_plus z1 z2 :
  PureExec True 1 (BinOp PlusOp (Lit $ LitInt z1) (Lit $ LitInt z2))
                  (Lit $ LitInt $ z1 + z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_minus z1 z2 :
  PureExec True 1 (BinOp MinusOp (Lit $ LitInt z1) (Lit $ LitInt z2))
                  (Lit $ LitInt $ z1 - z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_mult z1 z2 :
  PureExec True 1 (BinOp MultOp (Lit $ LitInt z1) (Lit $ LitInt z2))
                  (Lit $ LitInt $ z1 * z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_offset l z :
  PureExec True 1 (BinOp OffsetOp (Lit $ LitLoc l) (Lit $ LitInt z))
                  (Lit $ LitLoc $ l +ₗ z).
Proof. solve_pure_exec. Qed.

Global Instance pure_case i e el :
  PureExec (0 ≤ i ∧ el !! (Z.to_nat i) = Some e) 1 (Case (Lit $ LitInt i) el) e
  | 10.
Proof. solve_pure_exec. Qed.

Global Instance pure_if b e1 e2 :
  PureExec True 1 (If (Lit (lit_of_bool b)) e1 e2) (if b then e1 else e2) | 1.
Proof. destruct b; solve_pure_exec. Qed.

(** ** Heap *)

Lemma twp_alloc W s E (n : Z) :
  0 < n →
  [[{ True }]][W] Alloc (Lit $ LitInt n) @ s; E
  [[{ l (sz: nat), RET LitV $ LitLoc l;
      ⌜n = sz⌝ ∗ †l…sz ∗ l ↦∗ repeat (LitV LitPoison) sz }]].
Proof.
  iIntros (? Φ) "_ HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (????) "[$ Hσ] !>". iSplit; first by auto.
  iIntros (?????). inv_head_step.
  iMod (heap_alloc with "Hσ") as "[$ Hl]"; [done..|].
  iModIntro. do 2 (iSplit=>//).
  iApply ("HΦ" $! _ (Z.to_nat n)). auto with lia iFrame.
Qed.
Lemma wp_alloc W s E (n : Z) :
  0 < n →
  {{{ True }}}[W] Alloc (Lit $ LitInt n) @ s; E
  {{{ l (sz: nat), RET LitV $ LitLoc l;
      ⌜n = sz⌝ ∗ †l…sz ∗ l ↦∗ repeat (LitV LitPoison) sz }}}.
Proof.
  iIntros (??) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_alloc with "H"); [done|]. iIntros "%%? →Φ !>". by iApply "→Φ".
Qed.

Lemma twp_free `{!WsatIncl W na_wsat Wr} s E (n:Z) l vl :
  n = length vl →
  [[{ l ↦∗ vl ∗ †l…(length vl) }]][W]
    Free (Lit $ LitInt n) (Lit $ LitLoc l) @ s; E
  [[{ RET LitV LitPoison; True }]].
Proof.
  iIntros (? Φ) "[Hmt Hf] HΦ". iApply twp_lift_atomic_base_step_no_fork;
    first done.
  iIntros (????) "[W Hσ]". iDestruct (wsat_split (W':=na_wsat) with "W") as "[Wna Wr]".
  iMod (heap_free _ _ _ n with "Hσ Hmt Hf Wna") as "(% & % & Hσ & Wna)"=>//.
  iModIntro. iSplit; first by auto.
  iIntros (?????) "!>". inv_head_step. do 2 (iSplit=>//).
  iSplitR "HΦ"; last by iApply "HΦ".
  iSplitL "Wna Wr"; last by iFrame "Hσ".
  iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr)). iFrame.
Qed.
Lemma wp_free `{!WsatIncl W na_wsat Wr} s E (n:Z) l vl :
  n = length vl →
  {{{ ▷ l ↦∗ vl ∗ ▷ †l…(length vl) }}}[W]
    Free (Lit $ LitInt n) (Lit $ LitLoc l) @ s; E
  {{{ RET LitV LitPoison; True }}}.
Proof.
  iIntros (??) "[>H >H'] →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_free with "[$H $H']"); [done|]. iIntros "? →Φ !>".
  by iApply "→Φ".
Qed.

(** ** Reads

  The original takes a later-credit budget [£ d] on every guarded rule and
  spends it on [lc_fupd_elim_laterN] inside the Points-To Cell Logic.  Here the
  guard is over the world satisfaction [na_wsat], which the weakest
  precondition's own world satisfaction [W] contains, and no credits appear. *)
Lemma twp_read_sc_guarded_cells `{!WsatIncl W na_wsat Wr} s E l c v
    (G : iProp Σ) :
  [[{ (G &&{na_wsat}&&> l ↦[^ c] v) ∗ G }]][W]
    Read ScOrd (Lit $ LitLoc l) @ s; E [[{ RET v; G }]].
Proof.
  iIntros (Φ) "[#Gv G] HΦ". iApply twp_lift_atomic_base_step_no_fork;
    first done.
  iIntros (????) "[W Hσ]". iDestruct (wsat_split (W':=na_wsat) with "W") as "[Wna Wr]".
  iDestruct "Hσ" as (hF) "(Hna & HhF & %REL & ato)".
  iDestruct (atomic_read with "[] G Hna Wna") as (n0) "[%Heq [G [Hna Wna]]]".
  { rewrite /heap_mapsto_cells_fancy /fv2sum. iApply "Gv". }
  iModIntro. iSplit; first by eauto.
  iIntros (?????). inv_head_step. iModIntro. do 2 (iSplit=>//).
  iSplitR "G HΦ"; last by iApply "HΦ".
  iSplitL "Wna Wr".
  { iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr)). iFrame. }
  iExists hF. iFrame. done.
Qed.

Lemma twp_read_sc `{!WsatIncl W na_wsat Wr} s E l v :
  [[{ l ↦ v }]][W] Read ScOrd (Lit $ LitLoc l) @ s; E [[{ RET v; l ↦ v }]].
Proof.
  iIntros (Φ) "pt HΦ".
  iApply (twp_read_sc_guarded_cells s E l [] v (l ↦ v)%I with "[$pt]").
  { rewrite /heap_mapsto_cells_fancy /heap_mapsto /fv2sum /=.
    iApply guard_refl. }
  done.
Qed.
Lemma wp_read_sc `{!WsatIncl W na_wsat Wr} s E l v :
  {{{ ▷ l ↦ v }}}[W] Read ScOrd (Lit $ LitLoc l) @ s; E {{{ RET v; l ↦ v }}}.
Proof.
  iIntros (?) ">H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_read_sc with "H"). iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma twp_read_na_guarded_cells `{!WsatIncl W na_wsat Wr} s E l c v Gx :
  [[{ (na_sem Gx &&{na_wsat}&&> (l ↦[^ c] v)) ∗ na_sem Gx }]][W]
    Read Na1Ord (Lit $ LitLoc l) @ s; E [[{ RET v; na_sem Gx }]].
Proof.
  iIntros (Φ) "[#Gv G] HΦ". iApply twp_lift_base_step; first done.
  iIntros (????) "[W Hσ]".
  iDestruct (wsat_split (W':=na_wsat) with "W") as "[Wna Wr]".
  iDestruct "Hσ" as (hF) "(Hna & HhF & %REL & ato)".
  iMod (na_read_begin with "Gv G Hna Wna") as (n0) "[%Heq [rim [Hna Wna]]]".
  replace (n0 + 1)%nat with (S n0) by lia.
  iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
  iModIntro. iSplit.
  { iPureIntro. eexists _, _, _. by apply ReadNa1S. }
  iIntros (?????). inv_head_step. iMod "Hclose" as "_". iModIntro.
  iSplitR; [done|]. iSplitL "Wna Wr Hna HhF ato".
  { iSplitL "Wna Wr".
    { iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr)). iFrame. }
    iExists hF. iFrame. iPureIntro. eauto using heap_freeable_rel_stable. }
  iSplitL; [|done].
  iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (????) "[W Hσ]".
  iDestruct (wsat_split (W':=na_wsat) with "W") as "[Wna Wr]".
  iDestruct "Hσ" as (hF') "(Hna & HhF & %REL' & ato)".
  iMod (na_read_end with "rim Hna Wna") as (n) "([%H1 %H2] & G & Hna & Wna)".
  destruct n as [|n]; first by lia. replace (S n - 1)%nat with n by lia.
  iModIntro. iSplit.
  { iPureIntro. eexists _, _, _. by apply ReadNa2S. }
  iIntros (?????) "!>". inv_head_step. do 2 (iSplit=>//).
  iSplitR "G HΦ"; last by iApply "HΦ".
  iSplitL "Wna Wr".
  { iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr)). iFrame. }
  iExists hF'. iFrame. iPureIntro. eauto using heap_freeable_rel_stable.
Qed.

Lemma twp_read_na `{!WsatIncl W na_wsat Wr} s E l v :
  [[{ l ↦ v }]][W] Read Na1Ord (Lit $ LitLoc l) @ s; E [[{ RET v; l ↦ v }]].
Proof.
  iIntros (Φ) "pt HΦ".
  iApply (twp_read_na_guarded_cells s E l [] v
    (heap_fml (inl l) [] (inr v)) with "[pt]").
  - rewrite heap_fml_sem. iFrame "pt".
    rewrite /heap_mapsto_cells_fancy /fv2sum /=. iApply guard_refl.
  - rewrite heap_fml_sem. rewrite /heap_mapsto /=. iIntros "pt".
    by iApply "HΦ".
Qed.
Lemma wp_read_na `{!WsatIncl W na_wsat Wr} s E l v :
  {{{ ▷ l ↦ v }}}[W] Read Na1Ord (Lit $ LitLoc l) @ s; E {{{ RET v; l ↦ v }}}.
Proof.
  iIntros (?) ">H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_read_na with "H"). iIntros "? →Φ !>". by iApply "→Φ".
Qed.

End lifting.
