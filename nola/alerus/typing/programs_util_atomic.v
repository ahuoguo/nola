(** * Skip-rule helpers for the global atomic lock

  Ported from VerusBelt ([typing/programs_util_atomic.v], MIT, Hance,
  Elbeheiry, Matsushita, Dreyer).

  Like the other skip rules these are "ghost steps": a [Skip;;Skip] that
  rearranges the ghost state.  In the original the two [Skip]s are there to
  mint [⧖] and [£]; later-free there is nothing to mint, so the hypotheses
  lose [⧖], [⧗] and [£] and the fancy update becomes an update over the world
  satisfaction.  Each of these is then just [typed_inv_instr_of_skip] with
  the invariant context taken apart.

  *** Not ported: [wp_global_atomic_lock].

  [GlobalAtomicLock] is the spin loop

    rec: "f" [] := if: GlobalLock then "f" [] else #☠

  and the original proves it by [iLöb].  The weakest precondition here is the
  *total* one, so the loop has no proof: a spin lock need not terminate.  The
  single-step [twp_global_try_atomic_lock] and [twp_global_atomic_unlock]
  below are both fine; what is lost is the rule that *acquires* the global
  atomic lock, and with it [typed_atomic_lock] in [typing/atomic_inv.v]. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From nola.alerus.lang Require Import lang proofmode tactics lifting.
From nola.alerus.typing Require Export type ctx.
From nola.alerus.typing Require Import type_context programs programs_util own
  inv_context.
From nola.alerus.util Require Import atomic_lock_counter.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation WpwNotation.

Definition GlobalAtomicLock: expr :=
  (rec: "global_atomic_lock" [] :=
     if: GlobalLock then "global_atomic_lock" [] else #☠)%V [].
Notation GlobalAtomicUnlock := (GlobalUnlock) (only parsing).

Section programs_util_atomic.
  Context `{!typeG FML Σ}.

  Lemma twp_global_try_atomic_lock W s E :
    [[{ True }]][W] GlobalLock @ s; E
    [[{ (b: Z), RET LitV (LitInt b);
      match b with 0%Z => heap_ato_ctx | 1%Z => True | _ => False end }]].
  Proof.
    iIntros (Φ) "_ HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
    iIntros (????) "[$ Hσ]".
    iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato)".
    iModIntro. iSplit.
    { iPureIntro. eexists _, _, _. apply GlobalLockS. }
    iIntros (?????). inv_head_step. iModIntro. do 2 (iSplit=>//).
    iSplitR "HΦ ato".
    { iExists hF. by iFrame "Hσ HhF". }
    iApply "HΦ". by destruct σ1 as [? [|]].
  Qed.

  Lemma twp_global_atomic_unlock W s E :
    [[{ heap_ato_ctx }]][W] GlobalAtomicUnlock @ s; E
    [[{ RET LitV LitPoison; True }]].
  Proof.
    iIntros (Φ) "ato HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
    iIntros (????) "[$ Hσ]".
    iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato2)".
    destruct σ1 as [σ1 [|]]; last first.
    { iDestruct "ato" as "[pool1 _]". iDestruct "ato2" as "[pool2 _]".
      iDestruct (na_own_disjoint with "pool1 pool2") as %disj.
      iExFalso. iPureIntro.
      have Htop : (xH ∈ (⊤:coPset)) by set_solver.
      exact (disj xH Htop Htop). }
    iModIntro. iSplit.
    { iPureIntro. eexists _, _, _. by apply GlobalUnlockS. }
    iIntros (?????). inv_head_step. iModIntro. do 2 (iSplit=>//).
    iSplitR "HΦ"; [|by iApply "HΦ"].
    iExists hF. by iFrame "Hσ HhF ato".
  Qed.

  Lemma typed_atomic_instr {𝔄 𝔅l} (E: elctx) (L: llctx) Il ϝ n n'
      (p : path) (ty : type 𝔄) (T': tctx 𝔅l) (tr: predl_trans [𝔄] 𝔅l) :
    (∀ x v d tid post mask na_mask at_mask iκs,
      na_mask ∪ at_mask = ⊤ → na_mask ∩ at_mask = mask →
      ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ atomic_ctx at_mask (AtomicOpen n) -∗
      cna_lifetimes tid (invctx_to_multiset Il ⊎ list_to_set_disj iκs) -∗
      ϝ ⊑ lft_intersect_list iκs -∗
      ⌜eval_path p = Some v⌝ -∗ ty_own ty x d d tid [FVal v] -∗
      ⟨π, tr post -[x] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ xl' mask' at_mask',
      ⌜na_mask ∪ at_mask' = ⊤ ∧ na_mask ∩ at_mask' = mask'⌝ ∗
      llctx_interp L ∗ atomic_ctx at_mask' (AtomicOpen n') ∗
      cna_lifetimes tid (invctx_to_multiset Il ⊎ list_to_set_disj iκs) ∗
      tctx_interp tid T' xl' ∗ ⟨π, post xl' mask' π⟩)%I)
    → typed_inv_instr E L (InvCtx Il ϝ (AtomicOpen n)) +[p ◁ ty]
        (Seq Skip Skip) (InvCtx Il ϝ (AtomicOpen n')) (const T') tr.
  Proof.
    move=> Hvs. apply typed_inv_instr_of_skip.
    move=> x v d tid post mask iκs.
    iIntros "#LFT #PROPH #UNIQ #E L I %Hp own Obs W".
    iDestruct "I" as (na_mask at_mask) "[%Hmask [[I1 #I1'] [I2 Iat]]]".
    iMod (Hvs x v d tid post mask na_mask at_mask iκs
      with "LFT PROPH UNIQ E L Iat I1 I1' [//] own Obs W")
      as "[W (%xl' & %mask' & %at_mask' & %Hmasks' & L & Iat & I1 & T & Obs)]";
      [apply Hmask|apply Hmask|].
    iModIntro. iFrame "W". iExists xl', mask'. iFrame "L T Obs".
    iExists na_mask, at_mask'. by iFrame "I1 I1' I2 Iat".
  Qed.

  Lemma typed2_atomic_instr {𝔄1 𝔄2 𝔅l} (E: elctx) (L: llctx) Il ϝ n n'
      (p1 : path) (ty1 : type 𝔄1) (p2 : path) (ty2 : type 𝔄2)
      (T': tctx 𝔅l) (tr: predl_trans [𝔄1; 𝔄2] 𝔅l) :
    (∀ x1 x2 v1 v2 d tid post mask na_mask at_mask iκs,
      na_mask ∪ at_mask = ⊤ → na_mask ∩ at_mask = mask →
      ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ atomic_ctx at_mask (AtomicOpen n) -∗
      cna_lifetimes tid (invctx_to_multiset Il ⊎ list_to_set_disj iκs) -∗
      ϝ ⊑ lft_intersect_list iκs -∗
      ⌜eval_path p1 = Some v1⌝ -∗ ty_own ty1 x1 d d tid [FVal v1] -∗
      ⌜eval_path p2 = Some v2⌝ -∗ ty_own ty2 x2 d d tid [FVal v2] -∗
      ⟨π, tr post -[x1; x2] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ xl' mask' at_mask',
      ⌜na_mask ∪ at_mask' = ⊤ ∧ na_mask ∩ at_mask' = mask'⌝ ∗
      llctx_interp L ∗ atomic_ctx at_mask' (AtomicOpen n') ∗
      cna_lifetimes tid (invctx_to_multiset Il ⊎ list_to_set_disj iκs) ∗
      tctx_interp tid T' xl' ∗ ⟨π, post xl' mask' π⟩)%I)
    → typed_inv_instr E L (InvCtx Il ϝ (AtomicOpen n))
        +[p1 ◁ ty1; p2 ◁ ty2] (Seq Skip Skip)
        (InvCtx Il ϝ (AtomicOpen n')) (const T') tr.
  Proof.
    move=> Hvs. apply typed2_inv_instr_of_skip.
    move=> x1 x2 v1 v2 d tid post mask iκs.
    iIntros "#LFT #PROPH #UNIQ #E L I %Hp1 own1 %Hp2 own2 Obs W".
    iDestruct "I" as (na_mask at_mask) "[%Hmask [[I1 #I1'] [I2 Iat]]]".
    iMod (Hvs x1 x2 v1 v2 d tid post mask na_mask at_mask iκs
      with "LFT PROPH UNIQ E L Iat I1 I1' [//] own1 [//] own2 Obs W")
      as "[W (%xl' & %mask' & %at_mask' & %Hmasks' & L & Iat & I1 & T & Obs)]";
      [apply Hmask|apply Hmask|].
    iModIntro. iFrame "W". iExists xl', mask'. iFrame "L T Obs".
    iExists na_mask, at_mask'. by iFrame "I1 I1' I2 Iat".
  Qed.

  Local Lemma zero_size_phys {𝔅} (ty : type 𝔅) x tid :
    ty_size ty = 0 → ty_phys ty x tid = [].
  Proof.
    move=> Hsz. have Hl := ty_size_eq ty x tid.
    destruct (ty_phys ty x tid); [done|]. simpl in Hl. lia.
  Qed.

  Lemma typed_atomic_instr_own_own_t {𝔄1 𝔅} (E: elctx) (L: llctx) Il ϝ n n'
      (p1 : path) (ty1 : type 𝔄1) (tyret: type 𝔅)
      (tr: predl_trans [at_locₛ 𝔄1] [at_locₛ 𝔅]) :
    ty_size ty1 = 0 → ty_size tyret = 0 →
    (∀ l1 x1 d tid post mask na_mask at_mask iκs,
      na_mask ∪ at_mask = ⊤ → na_mask ∩ at_mask = mask →
      ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ atomic_ctx at_mask (AtomicOpen n) -∗
      cna_lifetimes tid (invctx_to_multiset Il ⊎ list_to_set_disj iκs) -∗
      ϝ ⊑ lft_intersect_list iκs -∗
      ty_gho ty1 x1 d (S d) tid -∗
      ⟨π, tr post -[(l1, x1)] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ d' xret mask' at_mask',
      ⌜na_mask ∪ at_mask' = ⊤ ∧ na_mask ∩ at_mask' = mask'⌝ ∗
      llctx_interp L ∗ atomic_ctx at_mask' (AtomicOpen n') ∗
      cna_lifetimes tid (invctx_to_multiset Il ⊎ list_to_set_disj iκs) ∗
      ty_gho tyret xret d' (S d') tid ∗
      ⟨π, post -[(l1, xret)] mask' π⟩)%I)
    → typed_inv_instr E L (InvCtx Il ϝ (AtomicOpen n))
        +[p1 ◁ own_ptr 0 ty1] (Seq Skip Skip)
        (InvCtx Il ϝ (AtomicOpen n')) (const +[p1 ◁ own_ptr 0 tyret]) tr.
  Proof.
    move=> Hsize0 Hsize0' Ha. apply typed_atomic_instr.
    move=> [l1 x1] v1 d tid post mask na_mask at_mask iκs Hm1 Hm2.
    iIntros "#LFT #PROPH #UNIQ #E L Iat I1 #I1' %He1 Own1 Obs W".
    iDestruct "Own1" as "[Gho1 %Phys1]".
    destruct d as [|d];
      first by iDestruct (false_fml_sem_1 with "Gho1") as "[]".
    rewrite own_ptr_gho /=. iDestruct "Gho1" as "(Pt1 & Free1 & Gho1)".
    iMod (Ha l1 x1 d tid post mask na_mask at_mask iκs Hm1 Hm2
      with "LFT PROPH UNIQ E L Iat I1 I1' Gho1 Obs W")
      as "[W (%d' & %xret & %mask' & %at_mask' & %Hmasks' & L & Iat & I1 &
        GhoRet & Obs)]".
    iModIntro. iFrame "W". iExists -[(l1, xret)], mask', at_mask'.
    iFrame "L Iat I1 Obs". iSplit; [done|]. iSplit; [|done].
    iExists v1, (S d'). inversion Phys1.
    iSplit; [iPureIntro; subst; done|].
    rewrite /ty_own own_ptr_gho /= Hsize0'
      (zero_size_phys tyret xret tid Hsize0') heap_mapsto_fancy_vec_nil.
    by iFrame "GhoRet".
  Qed.

  Lemma typed_atomic_instr_own2_emp {𝔄1 𝔄2} (E: elctx) (L: llctx) Il ϝ n n'
      (p1 : path) (ty1 : type 𝔄1) (p2 : path) (ty2 : type 𝔄2)
      (tr: predl_trans (at_locₛ 𝔄1 :: [at_locₛ 𝔄2]) []) :
    (∀ l1 l2 x1 x2 d tid post mask na_mask at_mask iκs,
      na_mask ∪ at_mask = ⊤ → na_mask ∩ at_mask = mask →
      ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ atomic_ctx at_mask (AtomicOpen n) -∗
      cna_lifetimes tid (invctx_to_multiset Il ⊎ list_to_set_disj iκs) -∗
      ϝ ⊑ lft_intersect_list iκs -∗
      ty_gho ty1 x1 d (S d) tid -∗ ty_gho ty2 x2 d (S d) tid -∗
      ⟨π, tr post -[(l1, x1); (l2, x2)] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ mask' at_mask',
      ⌜na_mask ∪ at_mask' = ⊤ ∧ na_mask ∩ at_mask' = mask'⌝ ∗
      llctx_interp L ∗ atomic_ctx at_mask' (AtomicOpen n') ∗
      cna_lifetimes tid (invctx_to_multiset Il ⊎ list_to_set_disj iκs) ∗
      ⟨π, post -[] mask' π⟩)%I)
    → typed_inv_instr E L (InvCtx Il ϝ (AtomicOpen n))
        +[p1 ◁ own_ptr 0 ty1; p2 ◁ own_ptr 0 ty2] (Seq Skip Skip)
        (InvCtx Il ϝ (AtomicOpen n')) (const +[]) tr.
  Proof.
    move=> Ha. apply typed2_atomic_instr.
    move=> [l1 x1] [l2 x2] v1 v2 d tid post mask na_mask at_mask iκs Hm1 Hm2.
    iIntros "#LFT #PROPH #UNIQ #E L Iat I1 #I1' %He1 Own1 %He2 Own2 Obs W".
    iDestruct "Own1" as "[Gho1 %Phys1]".
    iDestruct "Own2" as "[Gho2 %Phys2]".
    destruct d as [|d];
      first by iDestruct (false_fml_sem_1 with "Gho1") as "[]".
    rewrite !own_ptr_gho /=.
    iDestruct "Gho1" as "(Pt1 & Free1 & Gho1)".
    iDestruct "Gho2" as "(Pt2 & Free2 & Gho2)".
    iMod (Ha l1 l2 x1 x2 d tid post mask na_mask at_mask iκs Hm1 Hm2
      with "LFT PROPH UNIQ E L Iat I1 I1' Gho1 Gho2 Obs W")
      as "[W (%mask' & %at_mask' & %Hmasks' & L & Iat & I1 & Obs)]".
    iModIntro. iFrame "W". iExists -[], mask', at_mask'.
    by iFrame "L Iat I1 Obs".
  Qed.
End programs_util_atomic.
