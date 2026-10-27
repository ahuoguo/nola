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
From nola.verus_halt.lang Require Export lang heap.
From nola.verus_halt.lang Require Import tactics.
From nola.verus_halt.util Require Import non_atomic_cell_map atomic_lock_counter.
From nola.verus_halt Require Import na_inv_fork.
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

(** ** Writes

  The original's [wp_write_sc] is stated with a [£1] in its precondition,
  flagged in the source as "the extra £1 is the problem".  Later-free there is
  no credit at all. *)
Lemma twp_write_sc_guarded `{!WsatIncl W na_wsat Wr} s E l c e v v' Gx :
  IntoVal e v →
  [[{ (na_sem Gx &&{na_wsat}&&> ((l,c) #↦_)) ∗ na_sem Gx ∗ (l,c) #↦ v' }]][W]
    Write ScOrd (Lit $ LitLoc l) e @ s; E
  [[{ RET LitV LitPoison; (l,c) #↦ v ∗ na_sem Gx }]].
Proof.
  iIntros (<- Φ) "[#guards [G Hv]] HΦ".
  iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (????) "[W Hσ]".
  iDestruct (wsat_split (W':=na_wsat) with "W") as "[Wna Wr]".
  iMod (heap_write _ (l,c) v' v with "Hσ guards G Hv Wna")
    as "(%Hσl & Hσ & G & Hv' & Wna)".
  iModIntro. iSplit.
  { iPureIntro. eexists _, _, _. eapply WriteScS; [|apply Hσl].
    by rewrite to_of_val. }
  iIntros (?????) "!>". inv_head_step. do 2 (iSplit=>//).
  iSplitR "G Hv' HΦ"; last by iApply "HΦ"; iFrame.
  iSplitL "Wna Wr".
  { iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr)). iFrame. }
  iFrame "Hσ".
Qed.

Lemma twp_write_sc `{!WsatIncl W na_wsat Wr} s E l e v v' :
  IntoVal e v →
  [[{ l ↦ v' }]][W] Write ScOrd (Lit $ LitLoc l) e @ s; E
  [[{ RET LitV LitPoison; l ↦ v }]].
Proof.
  iIntros (? Φ) "pt HΦ".
  iApply (twp_write_sc_guarded s E l [] e v v' na_emptyx with "[pt]").
  - rewrite na_emptyx_sem heap_cloc1_mapsto_val. iFrame "pt".
    rewrite /heap_complete_mapsto /=. iApply guard_true.
  - rewrite na_emptyx_sem heap_cloc1_mapsto_val. iIntros "[pt _]".
    by iApply "HΦ".
Qed.
Lemma wp_write_sc `{!WsatIncl W na_wsat Wr} s E l e v v' :
  IntoVal e v →
  {{{ ▷ l ↦ v' }}}[W] Write ScOrd (Lit $ LitLoc l) e @ s; E
  {{{ RET LitV LitPoison; l ↦ v }}}.
Proof.
  iIntros (??) ">H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_write_sc with "H"). iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma twp_write_na_guarded `{!WsatIncl W na_wsat Wr} s E l c e v v' Gx :
  IntoVal e v →
  [[{ (na_sem Gx &&{na_wsat}&&> ((l,c) #↦_)) ∗ na_sem Gx ∗ (l,c) #↦ v' }]][W]
    Write Na1Ord (Lit $ LitLoc l) e @ s; E
  [[{ RET LitV LitPoison; (l,c) #↦ v ∗ na_sem Gx }]].
Proof.
  iIntros (<- Φ) "[#guards [G Hv]] HΦ".
  iApply twp_lift_base_step; first done.
  iIntros (????) "[W Hσ]".
  iDestruct (wsat_split (W':=na_wsat) with "W") as "[Wna Wr]".
  iMod (heap_write_na _ (l,c) v' v with "Hσ guards G Hv Wna")
    as "(%Hσl & Hσ & Wna & Hσclose)".
  iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
  iModIntro. iSplit.
  { iPureIntro. eexists _, _, _. eapply WriteNa1S; [|apply Hσl].
    by rewrite to_of_val. }
  iIntros (?????). inv_head_step. iMod "Hclose" as "_". iModIntro.
  iSplitR; [done|]. iSplitL "Wna Wr Hσ".
  { iSplitL "Wna Wr".
    { iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr)). iFrame. }
    iFrame "Hσ". }
  iSplitL; [|done].
  iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (????) "[W Hσ]".
  iDestruct (wsat_split (W':=na_wsat) with "W") as "[Wna Wr]".
  iMod ("Hσclose" with "Hσ Wna") as "(%Hw & Hσ & G & Hv & Wna)".
  destruct Hw as [v0 Hw].
  iModIntro. iSplit.
  { iPureIntro. eexists _, _, _. eapply WriteNa2S; [|apply Hw].
    by rewrite to_of_val. }
  iIntros (?????) "!>". inv_head_step. do 2 (iSplit=>//).
  iSplitR "G Hv HΦ"; last by iApply "HΦ"; iFrame.
  iSplitL "Wna Wr".
  { iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr)). iFrame. }
  iFrame "Hσ".
Qed.

Lemma twp_write_na `{!WsatIncl W na_wsat Wr} s E l e v v' :
  IntoVal e v →
  [[{ l ↦ v' }]][W] Write Na1Ord (Lit $ LitLoc l) e @ s; E
  [[{ RET LitV LitPoison; l ↦ v }]].
Proof.
  iIntros (? Φ) "pt HΦ".
  iApply (twp_write_na_guarded s E l [] e v v' na_emptyx with "[pt]").
  - rewrite na_emptyx_sem heap_cloc1_mapsto_val. iFrame "pt".
    rewrite /heap_complete_mapsto /=. iApply guard_true.
  - rewrite na_emptyx_sem heap_cloc1_mapsto_val. iIntros "[pt _]".
    by iApply "HΦ".
Qed.
Lemma wp_write_na `{!WsatIncl W na_wsat Wr} s E l e v v' :
  IntoVal e v →
  {{{ ▷ l ↦ v' }}}[W] Write Na1Ord (Lit $ LitLoc l) e @ s; E
  {{{ RET LitV LitPoison; l ↦ v }}}.
Proof.
  iIntros (??) ">H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_write_na with "H"). iIntros "? →Φ !>". by iApply "→Φ".
Qed.

(** Derived forms of the guarded read rules *)
Lemma twp_read_na_guarded_cells_singleton `{!WsatIncl W na_wsat Wr} s E l c v
    Gx :
  [[{ (na_sem Gx &&{na_wsat}&&> (l ↦[^ c]∗ [v])) ∗ na_sem Gx }]][W]
    Read Na1Ord (Lit $ LitLoc l) @ s; E [[{ RET v; na_sem Gx }]].
Proof.
  case: c=> >; last first.
  { setoid_rewrite guard_rhs_sep_l. exact: twp_read_na_guarded_cells. }
  iIntros "[#gd G] HΦ".
  iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (????) "[W Hσ]".
  iDestruct (wsat_split (W':=na_wsat) with "W") as "[Wna Wr]".
  by iDestruct (guard_acc with "gd G Wna") as "[[] _]".
Qed.

Lemma twp_read_na_guarded `{!WsatIncl W na_wsat Wr} s E l v Gx :
  [[{ (na_sem Gx &&{na_wsat}&&> (l ↦ v)) ∗ na_sem Gx }]][W]
    Read Na1Ord (Lit $ LitLoc l) @ s; E [[{ RET v; na_sem Gx }]].
Proof.
  exact: (twp_read_na_guarded_cells s E l [] v Gx).
Qed.

Lemma twp_write_na_guarded_0 `{!WsatIncl W na_wsat Wr} s E l cells e v v' Gx :
  IntoVal e v →
  [[{ (na_sem Gx &&{na_wsat}&&> ((l,cells) #↦_)) ∗ na_sem Gx
      ∗ (l,cells) #↦ v' }]][W] Write Na1Ord (Lit $ LitLoc l) e @ s; E
  [[{ RET LitV LitPoison; (l,cells) #↦ v ∗ na_sem Gx }]].
Proof. exact: twp_write_na_guarded. Qed.

(** ** Moving a cell between locations *)
Lemma twp_cell_move_na `{!WsatIncl W na_wsat Wr} s E l l' cell v' :
  [[{ l ↦! (FCell cell) ∗ l' ↦ v' }]][W]
    Write Na1Ord (Lit $ LitLoc l') (Read Na1Ord (Lit $ LitLoc l)) @ s; E
  [[{ RET LitV LitPoison; ∃ v, l ↦ v ∗ l' ↦! (FCell cell) }]].
Proof.
  iIntros (Φ) "[pt pt'] post". iApply twp_fupd.
  (* untether the cell from the location, get a concrete value [v] *)
  iMod (mapsto_vec_untether1 (l, []) (FCell cell) with "pt")
    as (v) "[pt [retether ?]]".
  change (Write Na1Ord (Lit (LitLoc l')) (Read Na1Ord (Lit (LitLoc l)))) with
    (fill_item (WriteRCtx Na1Ord (LitV (LitLoc l')))
      (Read Na1Ord (Lit (LitLoc l)))).
  iApply twp_bind. iApply (twp_read_na with "pt"). iIntros "pt".
  iApply (twp_write_na _ _ _ _ v with "pt'"); [done|]. iIntros "pt'".
  iMod ("retether" $! (l', []) with "[pt']") as "[? pt']".
  { iSplitR; [done|].
    rewrite /heap_complete_mapsto_fancy /split_at_last /rev /=.
    rewrite /heap_mapsto. iFrame "pt'". }
  iModIntro. iApply "post". iFrame.
Qed.

(** ** Compare-and-swap

  Every one of these takes [£(3*d+1)] (guarded) or [£1] (plain) in the
  original. *)
Lemma twp_cas_int_fail_guarded `{!WsatIncl W na_wsat Wr} s E l c z1 e2 lit2 zl
    Gx :
  IntoVal e2 (LitV lit2) → z1 ≠ zl →
  [[{ (na_sem Gx &&{na_wsat}&&> ((l,c) #↦_)) ∗ na_sem Gx
      ∗ (l,c) #↦ LitV (LitInt zl) }]][W]
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ s; E
  [[{ RET LitV $ LitInt 0; na_sem Gx ∗ (l,c) #↦ LitV (LitInt zl) }]].
Proof.
  iIntros (<- ? Φ) "[#guards [G Hv]] HΦ".
  iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros ([σh σb] ???) "[W Hσ]".
  iDestruct (wsat_split (W':=na_wsat) with "W") as "[Wna Wr]".
  iMod (heap_write _ (l,c) (LitV $ LitInt zl) (LitV $ LitInt zl)
    with "Hσ guards G Hv Wna") as "(%Hσl & Hσ & G & Hv' & Wna)".
  simpl in Hσl. rewrite /= (insert_id _ _ _ Hσl).
  iModIntro. iSplit; first by eauto.
  iIntros (?????) "!>". inv_head_step.
  - do 2 (iSplit=>//).
    iSplitR "G Hv' HΦ"; last by iApply "HΦ"; iFrame.
    iSplitL "Wna Wr".
    { iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr)). iFrame. }
    iFrame "Hσ".
  - rename select (lit_eq _ _ _) into Hfalse; inversion Hfalse; subst => //.
Qed.

Lemma twp_cas_int_fail `{!WsatIncl W na_wsat Wr} s E l z1 e2 lit2 zl :
  IntoVal e2 (LitV lit2) → z1 ≠ zl →
  [[{ l ↦ LitV (LitInt zl) }]][W]
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ s; E
  [[{ RET LitV $ LitInt 0; l ↦ LitV (LitInt zl) }]].
Proof.
  iIntros (?? Φ) "pt HΦ".
  iApply (twp_cas_int_fail_guarded s E l [] z1 e2 lit2 zl na_emptyx
    with "[pt]"); [done..| |].
  - rewrite na_emptyx_sem heap_cloc1_mapsto_val. iFrame "pt".
    rewrite /heap_complete_mapsto /=. iApply guard_true.
  - rewrite na_emptyx_sem heap_cloc1_mapsto_val. iIntros "[_ pt]".
    by iApply "HΦ".
Qed.

Lemma twp_cas_suc_guarded `{!WsatIncl W na_wsat Wr} s E l c lit1 e2 lit2 Gx :
  IntoVal e2 (LitV lit2) → lit1 ≠ LitPoison →
  [[{ (na_sem Gx &&{na_wsat}&&> ((l,c) #↦_)) ∗ na_sem Gx
      ∗ (l,c) #↦ LitV lit1 }]][W]
    CAS (Lit $ LitLoc l) (Lit lit1) e2 @ s; E
  [[{ RET LitV $ LitInt 1; na_sem Gx ∗ (l,c) #↦ LitV lit2 }]].
Proof.
  iIntros (<- Hne Φ) "[#guards [G Hv]] HΦ".
  iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (????) "[W Hσ]".
  iDestruct (wsat_split (W':=na_wsat) with "W") as "[Wna Wr]".
  iMod (heap_write _ (l,c) (LitV lit1) (LitV lit2)
    with "Hσ guards G Hv Wna") as "(%Hσl & Hσ & G & Hv' & Wna)".
  iModIntro. iSplit.
  { iPureIntro. eexists _, _, _. eapply CasSucS;
      [done|by rewrite to_of_val|apply Hσl|]. destruct lit1 => //. }
  iIntros (?????) "!>". inv_head_step.
  - rename select (lit_neq _ _) into Hfalse; inversion Hfalse; subst => //.
  - do 2 (iSplit=>//). iSplitR "G Hv' HΦ"; last by iApply "HΦ"; iFrame.
    iSplitL "Wna Wr".
    { iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr)). iFrame. }
    iFrame "Hσ".
Qed.

Lemma twp_cas_int_suc_guarded `{!WsatIncl W na_wsat Wr} s E l c z1 e2 lit2
    Gx :
  IntoVal e2 (LitV lit2) →
  [[{ (na_sem Gx &&{na_wsat}&&> ((l,c) #↦_)) ∗ na_sem Gx
      ∗ (l,c) #↦ LitV (LitInt z1) }]][W]
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ s; E
  [[{ RET LitV $ LitInt 1; na_sem Gx ∗ (l,c) #↦ LitV lit2 }]].
Proof.
  iIntros (<- Φ) "[#guards [G Hv]] HΦ".
  iApply (twp_cas_suc_guarded with "[$guards $G $Hv]") => //.
Qed.

Lemma twp_cas_suc `{!WsatIncl W na_wsat Wr} s E l lit1 e2 lit2 :
  IntoVal e2 (LitV lit2) → lit1 ≠ LitPoison →
  [[{ l ↦ LitV lit1 }]][W] CAS (Lit $ LitLoc l) (Lit lit1) e2 @ s; E
  [[{ RET LitV (LitInt 1); l ↦ LitV lit2 }]].
Proof.
  iIntros (?? Φ) "Hv HΦ".
  iApply (twp_cas_suc_guarded s E l [] lit1 _ lit2 na_emptyx with "[Hv]");
    [done..| |].
  - rewrite na_emptyx_sem heap_cloc1_mapsto_val. iFrame "Hv".
    rewrite /heap_complete_mapsto /=. iApply guard_true.
  - rewrite na_emptyx_sem heap_cloc1_mapsto_val. iIntros "[_ pt]".
    by iApply "HΦ".
Qed.

Lemma twp_cas_int_suc `{!WsatIncl W na_wsat Wr} s E l z1 e2 lit2 :
  IntoVal e2 (LitV lit2) →
  [[{ l ↦ LitV (LitInt z1) }]][W]
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ s; E
  [[{ RET LitV (LitInt 1); l ↦ LitV lit2 }]].
Proof. iIntros (? Φ) "pt HΦ". iApply (twp_cas_suc with "pt") => //. Qed.

Lemma twp_cas_loc_suc `{!WsatIncl W na_wsat Wr} s E l l1 e2 lit2 :
  IntoVal e2 (LitV lit2) →
  [[{ l ↦ LitV (LitLoc l1) }]][W]
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ s; E
  [[{ RET LitV (LitInt 1); l ↦ LitV lit2 }]].
Proof. iIntros (? Φ) "pt HΦ". iApply (twp_cas_suc with "pt") => //. Qed.

(** ** Pointer equality *)
Lemma twp_eq_loc `{!WsatIncl W na_wsat Wr} s E (l1 l2 : loc) v1 v2 P Φ :
  (P ⊢ l1 ↦ v1) → (P ⊢ l2 ↦ v2) →
  (P ⊢ Φ (LitV (bool_decide (l1 = l2)))) →
  P ⊢ WP[W] BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2)) @ s; E [{ Φ }].
Proof.
  iIntros (Hl1 Hl2 Hpost) "P".
  destruct (bool_decide_reflect (l1 = l2)) as [->|].
  - iApply (twp_lift_pure_det_base_step_no_fork (Λ:=lrust_ectx_lang));
      [done|solve_exec_safe|solve_exec_puredet|].
    rewrite Hpost. by iApply twp_value.
  - iApply twp_lift_atomic_base_step_no_fork; subst=>//.
    iIntros (????) "[W Hσ1]".
    iDestruct (wsat_split (W':=na_wsat) with "W") as "[Wna Wr]".
    inv_head_step. iModIntro. iSplit.
    { iPureIntro. repeat eexists. econstructor. eapply BinOpEqFalse. by auto. }
    iAssert (l1 ↦ v1 ∧ l2 ↦ v2 ∧ Φ (LitV false))%I with "[P]" as "P".
    { iSplit; last iSplit; by [iApply Hl1|iApply Hl2|iApply Hpost]. }
    clear Hl1 Hl2. iIntros (?????) "!>". inv_head_step.
    iSplitR=>//. iSplitR=>//. inv_bin_op_eval; inv_lit.
    + iExFalso. iDestruct "P" as "[Hl1 _]".
      iDestruct (heap_read with "Hσ1 Hl1 Wna") as "(_ & _ & _ & %X)".
      destruct X as [? X]. by simplify_eq.
    + iExFalso. iDestruct "P" as "[_ [Hl2 _]]".
      iDestruct (heap_read with "Hσ1 Hl2 Wna") as "(_ & _ & _ & %X)".
      destruct X as [? X]. by simplify_eq.
    + iSplitR "P"; last by iDestruct "P" as "[_ [_ $]]".
      iSplitL "Wna Wr".
      { iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr)). iFrame. }
      iFrame "Hσ1".
Qed.

(** ** Proof rules for the n-ary argument list *)
Lemma twp_app_ind W s E f (el : list expr)
    (Ql : vec (val → iProp Σ) (length el)) vs Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP[W] eQ.1 @ s; E [{ eQ.2 }]) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP[W] App f (of_val <$> vs ++ vl) @ s; E [{ Φ }]) -∗
    WP[W] App f ((of_val <$> vs) ++ el) @ s; E [{ Φ }].
Proof.
  intros [vf <-]. revert vs Ql.
  induction el as [|e el IH]=>/= vs Ql; inv_vec Ql; simpl.
  - iIntros "_ H". iSpecialize ("H" $! [#]). rewrite !app_nil_r /=.
    by iApply "H".
  - iIntros (Q Ql) "[He Hl] HΦ".
    change (App (of_val vf) ((of_val <$> vs) ++ e :: el)) with
      (fill_item (AppRCtx vf vs el) e).
    iApply twp_bind. iApply (twp_wand with "He"). iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]).
    iApply (IH _ _ with "Hl"). iIntros "%vl Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). iFrame.
Qed.

Lemma twp_app_vec W s E f el (Ql : vec (val → iProp Σ) (length el)) Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP[W] eQ.1 @ s; E [{ eQ.2 }]) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP[W] App f (of_val <$> (vl : list val)) @ s; E [{ Φ }]) -∗
    WP[W] App f el @ s; E [{ Φ }].
Proof. iIntros (Hf). by iApply (twp_app_ind _ _ _ _ _ _ []). Qed.

Lemma twp_app (Ql : list (val → iProp Σ)) W s E f el Φ :
  length Ql = length el → AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP[W] eQ.1 @ s; E [{ eQ.2 }]) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ -∗
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP[W] App f (of_val <$> (vl : list val)) @ s; E [{ Φ }]) -∗
    WP[W] App f el @ s; E [{ Φ }].
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_to_vec Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (twp_app_vec with "Hel"). iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite length_vec_to_list.
Qed.

(** ** Partial-weakest-precondition forms of the guarded rules

  Each is the total rule composed with [twp_wp_step]. *)
Lemma wp_read_sc_guarded_cells `{!WsatIncl W na_wsat Wr} s E l c v
    (G : iProp Σ) :
  {{{ (G &&{na_wsat}&&> l ↦[^ c] v) ∗ G }}}[W]
    Read ScOrd (Lit $ LitLoc l) @ s; E {{{ RET v; G }}}.
Proof.
  iIntros (?) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_read_sc_guarded_cells with "H"). iIntros "? →Φ !>".
  by iApply "→Φ".
Qed.

Lemma wp_read_na_guarded_cells `{!WsatIncl W na_wsat Wr} s E l c v Gx :
  {{{ (na_sem Gx &&{na_wsat}&&> (l ↦[^ c] v)) ∗ na_sem Gx }}}[W]
    Read Na1Ord (Lit $ LitLoc l) @ s; E {{{ RET v; na_sem Gx }}}.
Proof.
  iIntros (?) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_read_na_guarded_cells with "H"). iIntros "? →Φ !>".
  by iApply "→Φ".
Qed.

Lemma wp_write_sc_guarded `{!WsatIncl W na_wsat Wr} s E l c e v v' Gx :
  IntoVal e v →
  {{{ (na_sem Gx &&{na_wsat}&&> ((l,c) #↦_)) ∗ na_sem Gx ∗ (l,c) #↦ v' }}}[W]
    Write ScOrd (Lit $ LitLoc l) e @ s; E
  {{{ RET LitV LitPoison; (l,c) #↦ v ∗ na_sem Gx }}}.
Proof.
  iIntros (??) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_write_sc_guarded with "H"). iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma wp_write_na_guarded `{!WsatIncl W na_wsat Wr} s E l c e v v' Gx :
  IntoVal e v →
  {{{ (na_sem Gx &&{na_wsat}&&> ((l,c) #↦_)) ∗ na_sem Gx ∗ (l,c) #↦ v' }}}[W]
    Write Na1Ord (Lit $ LitLoc l) e @ s; E
  {{{ RET LitV LitPoison; (l,c) #↦ v ∗ na_sem Gx }}}.
Proof.
  iIntros (??) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_write_na_guarded with "H"). iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma wp_cas_int_fail_guarded `{!WsatIncl W na_wsat Wr} s E l c z1 e2 lit2 zl
    Gx :
  IntoVal e2 (LitV lit2) → z1 ≠ zl →
  {{{ (na_sem Gx &&{na_wsat}&&> ((l,c) #↦_)) ∗ na_sem Gx
      ∗ (l,c) #↦ LitV (LitInt zl) }}}[W]
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ s; E
  {{{ RET LitV $ LitInt 0; na_sem Gx ∗ (l,c) #↦ LitV (LitInt zl) }}}.
Proof.
  iIntros (???) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_cas_int_fail_guarded with "H"); [done..|].
  iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma wp_cas_suc_guarded `{!WsatIncl W na_wsat Wr} s E l c lit1 e2 lit2 Gx :
  IntoVal e2 (LitV lit2) → lit1 ≠ LitPoison →
  {{{ (na_sem Gx &&{na_wsat}&&> ((l,c) #↦_)) ∗ na_sem Gx
      ∗ (l,c) #↦ LitV lit1 }}}[W]
    CAS (Lit $ LitLoc l) (Lit lit1) e2 @ s; E
  {{{ RET LitV $ LitInt 1; na_sem Gx ∗ (l,c) #↦ LitV lit2 }}}.
Proof.
  iIntros (???) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_cas_suc_guarded with "H"); [done..|].
  iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma wp_cell_move_na `{!WsatIncl W na_wsat Wr} s E l l' cell v' :
  {{{ l ↦! (FCell cell) ∗ l' ↦ v' }}}[W]
    Write Na1Ord (Lit $ LitLoc l') (Read Na1Ord (Lit $ LitLoc l)) @ s; E
  {{{ RET LitV LitPoison; ∃ v, l ↦ v ∗ l' ↦! (FCell cell) }}}.
Proof.
  iIntros (?) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_cell_move_na with "H"). iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma wp_read_na_guarded_cells_0 `{!WsatIncl W na_wsat Wr} s E l c v Gx :
  {{{ (na_sem Gx &&{na_wsat}&&> (l ↦[^ c] v)) ∗ na_sem Gx }}}[W]
    Read Na1Ord (Lit $ LitLoc l) @ s; E {{{ RET v; na_sem Gx }}}.
Proof. exact: wp_read_na_guarded_cells. Qed.

Lemma wp_read_na_guarded_cells_singleton `{!WsatIncl W na_wsat Wr} s E l c v
    Gx :
  {{{ (na_sem Gx &&{na_wsat}&&> (l ↦[^ c]∗ [v])) ∗ na_sem Gx }}}[W]
    Read Na1Ord (Lit $ LitLoc l) @ s; E {{{ RET v; na_sem Gx }}}.
Proof.
  iIntros (?) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_read_na_guarded_cells_singleton with "H"). iIntros "? →Φ !>".
  by iApply "→Φ".
Qed.

Lemma wp_read_na_guarded `{!WsatIncl W na_wsat Wr} s E l v Gx :
  {{{ (na_sem Gx &&{na_wsat}&&> (l ↦ v)) ∗ na_sem Gx }}}[W]
    Read Na1Ord (Lit $ LitLoc l) @ s; E {{{ RET v; na_sem Gx }}}.
Proof. exact: (wp_read_na_guarded_cells s E l [] v Gx). Qed.

Lemma wp_write_na_guarded_0 `{!WsatIncl W na_wsat Wr} s E l cells e v v' Gx :
  IntoVal e v →
  {{{ (na_sem Gx &&{na_wsat}&&> ((l,cells) #↦_)) ∗ na_sem Gx
      ∗ (l,cells) #↦ v' }}}[W] Write Na1Ord (Lit $ LitLoc l) e @ s; E
  {{{ RET LitV LitPoison; (l,cells) #↦ v ∗ na_sem Gx }}}.
Proof. exact: wp_write_na_guarded. Qed.

Lemma wp_cas_int_fail `{!WsatIncl W na_wsat Wr} s E l z1 e2 lit2 zl :
  IntoVal e2 (LitV lit2) → z1 ≠ zl →
  {{{ ▷ l ↦ LitV (LitInt zl) }}}[W]
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ s; E
  {{{ RET LitV $ LitInt 0; l ↦ LitV (LitInt zl) }}}.
Proof.
  iIntros (???) ">H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_cas_int_fail with "H"); [done..|]. iIntros "? →Φ !>".
  by iApply "→Φ".
Qed.

Lemma wp_cas_int_suc_guarded `{!WsatIncl W na_wsat Wr} s E l c z1 e2 lit2 Gx :
  IntoVal e2 (LitV lit2) →
  {{{ (na_sem Gx &&{na_wsat}&&> ((l,c) #↦_)) ∗ na_sem Gx
      ∗ (l,c) #↦ LitV (LitInt z1) }}}[W]
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ s; E
  {{{ RET LitV $ LitInt 1; na_sem Gx ∗ (l,c) #↦ LitV lit2 }}}.
Proof.
  iIntros (??) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_cas_int_suc_guarded with "H"). iIntros "? →Φ !>".
  by iApply "→Φ".
Qed.

Lemma wp_cas_suc `{!WsatIncl W na_wsat Wr} s E l lit1 e2 lit2 :
  IntoVal e2 (LitV lit2) → lit1 ≠ LitPoison →
  {{{ ▷ l ↦ LitV lit1 }}}[W] CAS (Lit $ LitLoc l) (Lit lit1) e2 @ s; E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof.
  iIntros (???) ">H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_cas_suc with "H"); [done..|]. iIntros "? →Φ !>".
  by iApply "→Φ".
Qed.

Lemma wp_cas_int_suc `{!WsatIncl W na_wsat Wr} s E l z1 e2 lit2 :
  IntoVal e2 (LitV lit2) →
  {{{ ▷ l ↦ LitV (LitInt z1) }}}[W]
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ s; E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof. iIntros (??) "pt HΦ". iApply (wp_cas_suc with "pt") => //. Qed.

Lemma wp_cas_loc_suc `{!WsatIncl W na_wsat Wr} s E l l1 e2 lit2 :
  IntoVal e2 (LitV lit2) →
  {{{ ▷ l ↦ LitV (LitLoc l1) }}}[W]
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ s; E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof. iIntros (??) "pt HΦ". iApply (wp_cas_suc with "pt") => //. Qed.

Lemma wp_eq_loc `{!WsatIncl W na_wsat Wr} s E (l1 l2 : loc) v1 v2 P Φ :
  (P ⊢ ▷ l1 ↦ v1) → (P ⊢ ▷ l2 ↦ v2) →
  (P ⊢ ▷ Φ (LitV (bool_decide (l1 = l2)))) →
  P ⊢ WP[W] BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2)) @ s; E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hpost) "P".
  destruct (bool_decide_reflect (l1 = l2)) as [->|].
  - iApply (wp_lift_pure_det_base_step_no_fork (Λ:=lrust_ectx_lang));
      [done|solve_exec_safe|solve_exec_puredet|].
    rewrite Hpost. iIntros "!>!>!> _". by iApply wp_value.
  - iApply wp_lift_atomic_base_step_no_fork; subst=>//.
    iIntros (?????) "[W Hσ1]".
    iDestruct (wsat_split (W':=na_wsat) with "W") as "[Wna Wr]".
    inv_head_step. iModIntro. iSplit.
    { iPureIntro. repeat eexists. econstructor. eapply BinOpEqFalse. by auto. }
    iAssert (▷ (l1 ↦ v1 ∧ l2 ↦ v2 ∧ Φ (LitV false)))%I with "[P]" as "P".
    { iSplit; last iSplit; by [iApply Hl1|iApply Hl2|iApply Hpost]. }
    clear Hl1 Hl2. iIntros (????) "!> _". inv_head_step.
    iSplitR=>//. inv_bin_op_eval; inv_lit.
    + iExFalso. iDestruct "P" as "[Hl1 _]".
      iDestruct (heap_read with "Hσ1 Hl1 Wna") as "(_ & _ & _ & %X)".
      destruct X as [? X]. by simplify_eq.
    + iExFalso. iDestruct "P" as "[_ [Hl2 _]]".
      iDestruct (heap_read with "Hσ1 Hl2 Wna") as "(_ & _ & _ & %X)".
      destruct X as [? X]. by simplify_eq.
    + iSplitR "P"; last by iDestruct "P" as "[_ [_ $]]".
      iSplitL "Wna Wr".
      { iModIntro. iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr)). iFrame. }
      iModIntro. iFrame "Hσ1".
Qed.

Lemma wp_app_ind W s E f (el : list expr)
    (Ql : vec (val → iProp Σ) (length el)) vs Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP[W] eQ.1 @ s; E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP[W] App f (of_val <$> vs ++ vl) @ s; E {{ Φ }}) -∗
    WP[W] App f ((of_val <$> vs) ++ el) @ s; E {{ Φ }}.
Proof.
  intros [vf <-]. revert vs Ql.
  induction el as [|e el IH]=>/= vs Ql; inv_vec Ql; simpl.
  - iIntros "_ H". iSpecialize ("H" $! [#]). rewrite !app_nil_r /=.
    by iApply "H".
  - iIntros (Q Ql) "[He Hl] HΦ".
    change (App (of_val vf) ((of_val <$> vs) ++ e :: el)) with
      (fill_item (AppRCtx vf vs el) e).
    iApply wp_bind. iApply (wp_wand with "He"). iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]).
    iApply (IH _ _ with "Hl"). iIntros "%vl Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). iFrame.
Qed.

Lemma wp_app_vec W s E f el (Ql : vec (val → iProp Σ) (length el)) Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP[W] eQ.1 @ s; E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP[W] App f (of_val <$> (vl : list val)) @ s; E {{ Φ }}) -∗
    WP[W] App f el @ s; E {{ Φ }}.
Proof. iIntros (Hf). by iApply (wp_app_ind _ _ _ _ _ _ []). Qed.

Lemma wp_app (Ql : list (val → iProp Σ)) W s E f el Φ :
  length Ql = length el → AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP[W] eQ.1 @ s; E {{ eQ.2 }}) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ -∗
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP[W] App f (of_val <$> (vl : list val)) @ s; E {{ Φ }}) -∗
    WP[W] App f el @ s; E {{ Φ }}.
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_to_vec Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (wp_app_vec with "Hel"). iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite length_vec_to_list.
Qed.

Close Scope nat_scope.

End lifting.
