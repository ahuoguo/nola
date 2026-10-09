(** * Skip-rule helpers for zero-sized owning pointers

  Ported from VerusBelt ([typing/programs_util_own.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  These are the "ghost step" rules: a [Skip;;Skip] that does nothing
  physically but rearranges the ghost state behind zero-sized [own_ptr]s.  In
  the original each one is a time-receipt factory - the two [Skip]s are there
  to mint [⧖] and [£], which the client then spends stripping the [▷] that
  [own_ptr] puts in front of its inner ghost state.  Later-free there is no
  [▷] and nothing to mint, so the hypotheses lose [⧖], [⧗] and [£] and the
  fancy update becomes an update over the world satisfaction. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.typing Require Import type_context programs programs_util own.
From nola.alerus.typing Require Export type ctx.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation WpwNotation.

Section programs_util_own.
  Context `{!typeG FML Σ}.

  Local Lemma zero_size_phys {𝔅} (ty : type 𝔅) x tid :
    ty_size ty = 0 → ty_phys ty x tid = [].
  Proof.
    move=> Hsz. have Hl := ty_size_eq ty x tid.
    destruct (ty_phys ty x tid); [done|]. simpl in Hl. lia.
  Qed.

  Lemma typed_instr_of_skip_own2_own
    {𝔄1 𝔄2 𝔅} (E: elctx) (L: llctx) (I: invctx)
    (p1 : path) (ty1 : type 𝔄1)
    (p2 : path) (ty2 : type 𝔄2)
    (tyret: type 𝔅)
    (tr: predl_trans (at_locₛ 𝔄1 :: [at_locₛ 𝔄2]) [at_locₛ 𝔅]) :
    (ty_size ty1 = 0) →
    (ty_size tyret = 0) →
    (∀ l1 l2 x1 x2 d tid post mask iκs, ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ty_gho ty1 x1 d (S d) tid -∗
      ty_gho ty2 x2 d (S d) tid -∗
      ⟨π, tr post -[(l1, x1); (l2, x2)] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ xret, llctx_interp L ∗ invctx_interp tid mask iκs I ∗
        ty_gho tyret xret (S d) (S (S d)) tid ∗
        ⟨π, post -[(l2, xret)] mask π⟩)%I)
    → typed_inv_instr E L I
        +[p1 ◁ own_ptr 0 ty1; p2 ◁ own_ptr 0 ty2]
       (Seq Skip Skip) I
       (const +[p2 ◁ own_ptr 0 tyret])
       tr.
  Proof.
    intros Hsize0 Hsize0' Ha. apply typed2_inv_instr_of_skip.
    iIntros ([l1 x1] [l2 x2] v1 v2 d tid post mask iκs)
      "#LFT #PROPH #UNIQ #E L I %He1 Own1 %He2 Own2 Obs".
    iDestruct "Own1" as "[Gho1 %Phys1]".
    iDestruct "Own2" as "[Gho2 %Phys2]".
    destruct d as [|d]; first by iIntros.
    iDestruct "Gho1" as "[Pt1 [Free1 Gho1]]".
    iDestruct "Gho2" as "[Pt2 [Free2 Gho2]]".
    iIntros "W".
    iMod (Ha l1 l2 x1 x2 d tid post mask iκs
      with "LFT PROPH UNIQ E L I Gho1 Gho2 Obs W") as "[W X]".
    iDestruct "X" as (xret) "[L [I [GhoRet Obs]]]".
    iModIntro. iFrame "W". iExists -[(l2, xret)], mask. iFrame "L I Obs".
    iSplitL "GhoRet"; [|done]. iExists v2, (S (S d)).
    inversion Phys2. iSplit; [iPureIntro; subst; done|]. iSplitL "GhoRet"; [|done].
    rewrite /= Hsize0' (zero_size_phys tyret xret tid Hsize0')
      heap_mapsto_fancy_vec_nil. by iFrame "GhoRet".
  Qed.

  Lemma typed_instr_of_skip_own_own_t
    {𝔄1 𝔅} (E: elctx) (L: llctx) (I: invctx)
    (p1 : path) (ty1 : type 𝔄1)
    (tyret: type 𝔅)
    (tr: predl_trans ([at_locₛ 𝔄1]) [at_locₛ 𝔅]) :
    (ty_size ty1 = 0) →
    (ty_size tyret = 0) →
    (∀ l1 x1 d tid iκs post mask, ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ty_gho ty1 x1 d (S d) tid -∗
      ⟨π, tr post -[(l1, x1)] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ d' xret, llctx_interp L ∗ invctx_interp tid mask iκs I ∗
        ty_gho tyret xret d' (S d') tid ∗
        ⟨π, post -[(l1, xret)] mask π⟩)%I)
    → typed_instr E L I
        +[p1 ◁ own_ptr 0 ty1]
       (Seq Skip Skip)
       (const +[p1 ◁ own_ptr 0 tyret])
       tr.
  Proof.
    intros Hsize0 Hsize0' Ha. apply typed_instr_of_skip.
    iIntros ([l1 x1] v1 d tid post mask iκs)
      "#LFT #PROPH #UNIQ #E L I %He1 Own1 Obs".
    iDestruct "Own1" as "[Gho1 %Phys1]".
    destruct d as [|d]; first by iIntros.
    iDestruct "Gho1" as "[Pt1 [Free1 Gho1]]". iIntros "W".
    iMod (Ha l1 x1 d tid iκs post mask
      with "LFT PROPH UNIQ E L I Gho1 Obs W") as "[W X]".
    iDestruct "X" as (d' xret) "[L [I [GhoRet Obs]]]".
    iModIntro. iFrame "W". iExists -[(l1, xret)]. iFrame "L I Obs".
    iSplitL "GhoRet"; [|done]. iExists v1, (S d').
    inversion Phys1. iSplit; [iPureIntro; subst; done|]. iSplitL "GhoRet"; [|done].
    rewrite /= Hsize0' (zero_size_phys tyret xret tid Hsize0')
      heap_mapsto_fancy_vec_nil. by iFrame "GhoRet".
  Qed.

  Lemma typed_inv_instr_of_skip_own_own_t
    {𝔄1 𝔅} (E: elctx) (L: llctx) (I: invctx) (I': invctx)
    (p1 : path) (ty1 : type 𝔄1)
    (tyret: type 𝔅)
    (tr: predl_trans ([at_locₛ 𝔄1]) [at_locₛ 𝔅]) :
    (ty_size ty1 = 0) →
    (ty_size tyret = 0) →
    (∀ l1 x1 d tid iκs post mask, ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ty_gho ty1 x1 d (S d) tid -∗
      ⟨π, tr post -[(l1, x1)] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ d' xret mask', llctx_interp L ∗ invctx_interp tid mask' iκs I' ∗
        ty_gho tyret xret d' (S d') tid ∗
        ⟨π, post -[(l1, xret)] mask' π⟩)%I)
    → typed_inv_instr E L I
        +[p1 ◁ own_ptr 0 ty1]
       (Seq Skip Skip)
       I' (const +[p1 ◁ own_ptr 0 tyret])
       tr.
  Proof.
    intros Hsize0 Hsize0' Ha. apply typed_inv_instr_of_skip.
    iIntros ([l1 x1] v1 d tid post mask iκs)
      "#LFT #PROPH #UNIQ #E L I %He1 Own1 Obs".
    iDestruct "Own1" as "[Gho1 %Phys1]".
    destruct d as [|d]; first by iIntros.
    iDestruct "Gho1" as "[Pt1 [Free1 Gho1]]". iIntros "W".
    iMod (Ha l1 x1 d tid iκs post mask
      with "LFT PROPH UNIQ E L I Gho1 Obs W") as "[W X]".
    iDestruct "X" as (d' xret mask') "[L [I [GhoRet Obs]]]".
    iModIntro. iFrame "W". iExists -[(l1, xret)], mask'. iFrame "L I Obs".
    iSplitL "GhoRet"; [|done]. iExists v1, (S d').
    inversion Phys1. iSplit; [iPureIntro; subst; done|]. iSplitL "GhoRet"; [|done].
    rewrite /= Hsize0' (zero_size_phys tyret xret tid Hsize0')
      heap_mapsto_fancy_vec_nil. by iFrame "GhoRet".
  Qed.

  Lemma typed_inv_instr_of_skip_own2_emp
    {𝔄1 𝔄2} (E: elctx) (L: llctx) (I I': invctx)
    (p1 : path) (ty1 : type 𝔄1)
    (p2 : path) (ty2 : type 𝔄2)
    (tr: predl_trans (at_locₛ 𝔄1 :: [at_locₛ 𝔄2]) []) :
    (∀ l1 l2 x1 x2 d tid iκs post mask, ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ty_gho ty1 x1 d (S d) tid -∗
      ty_gho ty2 x2 d (S d) tid -∗
      ⟨π, tr post -[(l1, x1); (l2, x2)] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ mask', llctx_interp L ∗ invctx_interp tid mask' iκs I' ∗
        ⟨π, post -[] mask' π⟩)%I)
    → typed_inv_instr E L I
        +[p1 ◁ own_ptr 0 ty1; p2 ◁ own_ptr 0 ty2]
       (Seq Skip Skip) I'
       (const +[])
       tr.
  Proof.
    intros Ha. apply typed2_inv_instr_of_skip.
    iIntros ([l1 x1] [l2 x2] v1 v2 d tid post mask iκs)
      "#LFT #PROPH #UNIQ #E L I %He1 Own1 %He2 Own2 Obs".
    iDestruct "Own1" as "[Gho1 %Phys1]".
    iDestruct "Own2" as "[Gho2 %Phys2]".
    destruct d as [|d]; first by iIntros.
    iDestruct "Gho1" as "[Pt1 [Free1 Gho1]]".
    iDestruct "Gho2" as "[Pt2 [Free2 Gho2]]". iIntros "W".
    iMod (Ha l1 l2 x1 x2 d tid iκs post mask
      with "LFT PROPH UNIQ E L I Gho1 Gho2 Obs W") as "[W X]".
    iDestruct "X" as (mask') "[L [I' Obs]]".
    iModIntro. iFrame "W". iExists -[], mask'. by iFrame.
  Qed.
End programs_util_own.
