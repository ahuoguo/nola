(** * Utility for building typing rules

  Ported from VerusBelt ([typing/programs_util.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  Every lemma in this file exists to *manufacture time receipts and later
  credits*.  [typed_instr_of_skip] runs [Skip;; Skip] purely so that
  [wp_persistent_time_receipt] and [wp_cumulative_time_receipt2] can hand the
  caller [⧖(S d)], [⧗1], [⧗1] and [£(advance_credits d)]; the
  [typed_instr_of_memload] pair does the same before a guarded read, and sizes
  its budget with [unfold advance_credits; lia].

  Later-free there is nothing to manufacture.  The [Skip;; Skip] is still
  executed - it is part of the program - but the hypotheses take no receipts
  and no credits, and the guards carry no index. *)

From iris.proofmode Require Import environments proofmode.
From nola.alerus.lang Require Import proofmode.
From nola.alerus.typing Require Export type ctx lft_contexts type_context
  cont_context programs.
From nola.bi Require Import guard modw.
From nola.iris Require Import iprop.
Import GuardNotation ModwNotation WpwNotation iPropAppNotation.

Section programs_util.
  Context `{!typeG FML Σ}.

  Lemma typed_instr_of_skip
    {𝔄 𝔅l} (E: elctx) (L: llctx) (I: invctx)
    (p : path) (ty : type 𝔄)
    (T': tctx 𝔅l) (tr: predl_trans [𝔄] 𝔅l) :
    (∀ x v d tid post mask iκs, ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ⌜eval_path p = Some v⌝ -∗ ty_own ty x d d tid [FVal v] -∗
      ⟨π, tr post -[x] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ xl', llctx_interp L ∗ invctx_interp tid mask iκs I ∗
        tctx_interp tid T' xl' ∗ ⟨π, post xl' mask π⟩)%I)
    → typed_instr E L I +[p ◁ ty] (Seq Skip Skip) (const T') tr.
  Proof.
    intros Hvs tid post mask iκs xl. destruct xl as [x []].
    iIntros "#CTX #PROPH #UNIQ #E L I [T _] Obs".
    iDestruct "T" as (v d) "(p & own)".
    iApply twpw_fupdw_nonval; [done|]. do 3 wp_seq. iIntros "W".
    iMod (Hvs x v d tid post with "CTX PROPH UNIQ E L I p own Obs W")
      as "[$ ?]". by iModIntro.
  Qed.

  Lemma typed_inv_instr_of_skip
    {𝔄 𝔅l} (E: elctx) (L: llctx) (I: invctx) (I': invctx)
    (p : path) (ty : type 𝔄)
    (T': tctx 𝔅l) (tr: predl_trans [𝔄] 𝔅l) :
    (∀ x v d tid post mask iκs, ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ⌜eval_path p = Some v⌝ -∗ ty_own ty x d d tid [FVal v] -∗
      ⟨π, tr post -[x] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ xl' mask', llctx_interp L ∗ invctx_interp tid mask' iκs I' ∗
        tctx_interp tid T' xl' ∗ ⟨π, post xl' mask' π⟩)%I)
    → typed_inv_instr E L I +[p ◁ ty] (Seq Skip Skip) I' (const T') tr.
  Proof.
    intros Hvs tid post mask iκs xl. destruct xl as [x []].
    iIntros "#CTX #PROPH #UNIQ #E L I [T _] Obs".
    iDestruct "T" as (v d) "(p & own)".
    iApply twpw_fupdw_nonval; [done|]. do 3 wp_seq. iIntros "W".
    iMod (Hvs x v d tid post with "CTX PROPH UNIQ E L I p own Obs W")
      as "[$ ?]". by iModIntro.
  Qed.

  Lemma typed2_instr_of_skip
    {𝔄1 𝔄2 𝔅l} (E: elctx) (L: llctx) (I: invctx)
    (p1 : path) (ty1 : type 𝔄1)
    (p2 : path) (ty2 : type 𝔄2)
    (T': tctx 𝔅l) (tr: predl_trans (𝔄1 :: [𝔄2]) 𝔅l) :
    (∀ x1 x2 v1 v2 d tid post mask, ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗ llctx_interp L -∗
      ⌜eval_path p1 = Some v1⌝ -∗ ty_own ty1 x1 d d tid [FVal v1] -∗
      ⌜eval_path p2 = Some v2⌝ -∗ ty_own ty2 x2 d d tid [FVal v2] -∗
      ⟨π, tr post -[x1; x2] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ xl', llctx_interp L ∗ tctx_interp tid T' xl' ∗
        ⟨π, post xl' mask π⟩)%I)
    → typed_instr E L I +[p1 ◁ ty1; p2 ◁ ty2] (Seq Skip Skip) (const T') tr.
  Proof.
    intros Hvs tid post mask iκs xl. destruct xl as [x1 [x2 []]].
    iIntros "#CTX #PROPH #UNIQ #E L I [T1 [T2 _]] Obs".
    iDestruct "T1" as (v1 d1) "(p1 & own1)".
    iDestruct "T2" as (v2 d2) "(p2 & own2)".
    iApply twpw_fupdw_nonval; [done|]. do 3 wp_seq. iIntros "W".
    iMod (Hvs x1 x2 v1 v2 (d1 `max` d2) tid post
      with "CTX PROPH UNIQ E L p1 [own1] p2 [own2] Obs W") as "[$ J]".
    { iDestruct "own1" as "[gho phys]". iFrame.
      iDestruct (ty_gho_depth_mono with "gho") as "gho";
        last by iFrame "gho". { lia. } { lia. } }
    { iDestruct "own2" as "[gho phys]". iFrame.
      iDestruct (ty_gho_depth_mono with "gho") as "gho";
        last by iFrame "gho". { lia. } { lia. } }
    iDestruct "J" as (xl') "(? & ? & ?)". iModIntro. iExists xl'. iFrame.
  Qed.

  Lemma typed2_inv_instr_of_skip
    {𝔄1 𝔄2 𝔅l} (E: elctx) (L: llctx) (I I': invctx)
    (p1 : path) (ty1 : type 𝔄1)
    (p2 : path) (ty2 : type 𝔄2)
    (T': tctx 𝔅l) (tr: predl_trans (𝔄1 :: [𝔄2]) 𝔅l) :
    (∀ x1 x2 v1 v2 d tid post mask iκs, ⊢ (llft_ctx -∗ proph_ctx -∗
      uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ⌜eval_path p1 = Some v1⌝ -∗ ty_own ty1 x1 d d tid [FVal v1] -∗
      ⌜eval_path p2 = Some v2⌝ -∗ ty_own ty2 x2 d d tid [FVal v2] -∗
      ⟨π, tr post -[x1; x2] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ xl' mask', llctx_interp L ∗ invctx_interp tid mask' iκs I' ∗
        tctx_interp tid T' xl' ∗ ⟨π, post xl' mask' π⟩)%I)
    → typed_inv_instr E L I +[p1 ◁ ty1; p2 ◁ ty2] (Seq Skip Skip) I'
        (const T') tr.
  Proof.
    intros Hvs tid post mask iκs xl. destruct xl as [x1 [x2 []]].
    iIntros "#CTX #PROPH #UNIQ #E L I [T1 [T2 _]] Obs".
    iDestruct "T1" as (v1 d1) "(p1 & own1)".
    iDestruct "T2" as (v2 d2) "(p2 & own2)".
    iApply twpw_fupdw_nonval; [done|]. do 3 wp_seq. iIntros "W".
    iMod (Hvs x1 x2 v1 v2 (d1 `max` d2) tid post
      with "CTX PROPH UNIQ E L I p1 [own1] p2 [own2] Obs W") as "[$ J]".
    { iDestruct "own1" as "[gho phys]". iFrame.
      iDestruct (ty_gho_depth_mono with "gho") as "gho";
        last by iFrame "gho". { lia. } { lia. } }
    { iDestruct "own2" as "[gho phys]". iFrame.
      iDestruct (ty_gho_depth_mono with "gho") as "gho";
        last by iFrame "gho". { lia. } { lia. } }
    iDestruct "J" as (xl' mask') "(? & ? & ? & ?)". iModIntro.
    iExists xl', mask'. iFrame.
  Qed.

  (** A guarded load.  The original has two versions, differing only in the
    receipts they hand over; later-free they differ only in the depth of the
    result. *)
  Lemma typed_instr_of_memload_with_cumutime1
    {𝔄 𝔅} (E: elctx) (L: llctx) (I: invctx)
    (p : path) (ty : type 𝔄) (ty' : type 𝔅) (tr: predl_trans' [𝔄] 𝔅) :
    (∀ x v d tid post mask, ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗ llctx_interp L -∗
      ⌜eval_path p = Some v⌝ -∗ ty_own ty x d d tid [FVal v] -∗
      ⟨π, tr post -[x] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ (l: cloc) (l': loc) (Hx: FML $oi Σ), ⌜v = #l.1⌝ ∗ bor_sem Hx ∗
        (bor_sem Hx &&{Wguard}&&> (l.1 ↦[^ l.2]∗ [ #l' ])) ∗
        (bor_sem Hx =[alerus_wsat]{⊤}=∗ ∃ x', llctx_interp L ∗
          ty_own ty' x' d d tid [FVal #l' ] ∗ ⟨π, post x' mask π⟩))%I)
    → typed_instr_ty E L I +[p ◁ ty] (!p) (ty') tr.
  Proof.
    intros Rd tid post mask iκs xl. destruct xl as [x []].
    iIntros "#LFT #PROPH #UNIQ #E L I [T _] Obs".
    iApply twpw_fupdw_nonval; [done|].
    wp_bind p. iApply (twp_hasty with "T"). iIntros (v d) "%Hp ty".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Rd x v d tid with "LFT PROPH UNIQ E L [] ty Obs W")
      as "(W & %l & %l' & %Hx & -> & H & #Hpt & VsBack)"; [done|].
    iModIntro. iFrame "W".
    iApply (twp_read_na_guarded_cells_singleton _ _ _ _ _ Hx with "[H]").
    { iFrame "Hpt H". }
    iIntros "H W". iMod ("VsBack" with "H W") as "(W & %x' & L & Ty' & #Obs)".
    iModIntro. iFrame "W". iExists -[x']. iFrame "L I".
    rewrite right_id tctx_hasty_val. iSplit; [|done]. iExists d. iFrame.
  Qed.

  Lemma typed_instr_of_memload
    {𝔄 𝔅} (E: elctx) (L: llctx) (I: invctx)
    (p : path) (ty : type 𝔄) (ty' : type 𝔅) (tr: predl_trans' [𝔄] 𝔅) :
    (∀ x v d tid post mask, ⊢ (llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗ llctx_interp L -∗
      ⌜eval_path p = Some v⌝ -∗ ty_own ty x d d tid [FVal v] -∗
      ⟨π, tr post -[x] mask π⟩ =[alerus_wsat]{⊤}=∗
      ∃ (l: cloc) (l': loc) (Hx: FML $oi Σ), ⌜v = #l.1⌝ ∗ bor_sem Hx ∗
        (bor_sem Hx &&{Wguard}&&> (l.1 ↦[^ l.2]∗ [ #l' ])) ∗
        (bor_sem Hx =[alerus_wsat]{⊤}=∗ ∃ x', llctx_interp L ∗
          ty_own ty' x' (S d) (S d) tid [FVal #l' ] ∗ ⟨π, post x' mask π⟩))%I)
    → typed_instr_ty E L I +[p ◁ ty] (!p) (ty') tr.
  Proof.
    intros Rd tid post mask iκs xl. destruct xl as [x []].
    iIntros "#LFT #PROPH #UNIQ #E L I [T _] Obs".
    iApply twpw_fupdw_nonval; [done|].
    wp_bind p. iApply (twp_hasty with "T"). iIntros (v d) "%Hp ty".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (Rd x v d tid with "LFT PROPH UNIQ E L [] ty Obs W")
      as "(W & %l & %l' & %Hx & -> & H & #Hpt & VsBack)"; [done|].
    iModIntro. iFrame "W".
    iApply (twp_read_na_guarded_cells_singleton _ _ _ _ _ Hx with "[H]").
    { iFrame "Hpt H". }
    iIntros "H W". iMod ("VsBack" with "H W") as "(W & %x' & L & Ty' & #Obs)".
    iModIntro. iFrame "W". iExists -[x']. iFrame "L I".
    rewrite right_id tctx_hasty_val. iSplit; [|done]. iExists (S d). iFrame.
  Qed.
End programs_util.
