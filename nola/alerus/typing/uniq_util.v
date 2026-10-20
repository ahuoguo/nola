(** * The body of a unique borrow

  Ported from VerusBelt ([typing/uniq_util.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.

  This is the file the syntactic type interpretation was built for.  The
  borrow a unique reference holds is

    &{κ,idx} (∃x' d' g', ⧖(S d' `max` g') ∗ .PC[ξ] x' (vπ x') (d', g') ∗
                         ty_gho ty x' d' g' tid ∗ l #↦!∗ ty_phys ty x' tid)

  and later-free a borrow stores a *formula*, not a proposition - see the
  note on [TypeFml] in [typing/ctx.v].  [uniq_body_fml] is that body as a
  formula; [uniq_body_fml_sem] is the only thing the proofs below need to
  know about it.

  Two things go with the time receipts.  [⧖(S d' `max` g')] is VerusBelt's
  evidence that the depth indices have been reached, and [⧗1] is the credit
  [uniq_body] carries so that its clients can strip the [▷] in front of the
  borrowed contents; neither has anything to strip here, so both go.  That
  is what makes [resolve_uniq_body] - the heart of the file - shorter than
  the original: the whole credit arithmetic
  ([cumulative_persistent_time_receipt_get_credits], [lc_weaken],
  [lc_fupd_elim_laterN]) disappears, and the three [▷]s it was buying away
  are not there.

  The arbitrary [Timeless G] with [G &&{↑NllftG}&&> llctx_interp L] that the
  original halves with [frac_split_guard_in_half] is an [Ltok γ L q], as
  everywhere else in this port: halving a fraction is all the proof does
  with it. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.typing Require Import lft_contexts.
From nola.alerus.typing Require Export type ctx uniq_cmra.
From nola.alerus.lifetime Require Import lifetime_full.
From nola.alerus.lifetime Require Import ra.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Implicit Type 𝔄 𝔅: syn_type.

Section uniq_util.
  Context `{!typeG FML Σ}.

  (** The borrowed contents of a unique reference at a *fixed* refinement
    and depth, as a formula.  [resolve_uniq_body] freezes the existentials
    away and hands this one to [bor_to_guard]. *)
  Definition uniq_body_at_fml {𝔄} (ty: type 𝔄) (x: ~~𝔄) (ξi: positive)
    (x': ~~𝔄) (d' g': nat) (tid: thread_id) (l: cloc) : FML $oi Σ :=
    let ξ := PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi in
    (.PCx[ξ] x' (vπ x') (d', g') ∗
     ty.(ty_ghox) x' d' g' tid ∗ l #↦!∗ ty.(ty_phys) x' tid)%FML.

  Lemma uniq_body_at_fml_sem {𝔄} (ty: type 𝔄) x ξi x' d' g' tid l :
    bor_sem (uniq_body_at_fml ty x ξi x' d' g' tid l) ⊣⊢
      .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x' (vπ x') (d', g') ∗
      ty_gho ty x' d' g' tid ∗ l #↦!∗ ty_phys ty x' tid.
  Proof.
    rewrite /uniq_body_at_fml !bor_sep_sem pc_fml_sem ccells_fml_sem //.
  Qed.

  (** The borrowed contents of a unique reference, as a formula *)
  Definition uniq_body_fml {𝔄} (ty: type 𝔄) (x: ~~𝔄) (ξi: positive)
    (tid: thread_id) (l: cloc) : FML $oi Σ :=
    ex_fml (λ x' : ~~𝔄, ex_fml (λ d' : nat, ex_fml (λ g' : nat,
      uniq_body_at_fml ty x ξi x' d' g' tid l))).

  Lemma uniq_body_fml_sem {𝔄} (ty: type 𝔄) x ξi tid l :
    bor_sem (uniq_body_fml ty x ξi tid l) ⊣⊢
      ∃ (x': ~~𝔄) (d' g': nat),
        .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x' (vπ x') (d', g') ∗
        ty_gho ty x' d' g' tid ∗ l #↦!∗ ty_phys ty x' tid.
  Proof.
    rewrite /uniq_body_fml ex_fml_sem. apply bi.exist_proper=> x'.
    rewrite ex_fml_sem. apply bi.exist_proper=> d'.
    rewrite ex_fml_sem. apply bi.exist_proper=> g'.
    apply uniq_body_at_fml_sem.
  Qed.
  Lemma uniq_body_fml_sem_1 {𝔄} (ty: type 𝔄) x ξi tid l :
    bor_sem (uniq_body_fml ty x ξi tid l) ⊢
      ∃ (x': ~~𝔄) (d' g': nat),
        .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x' (vπ x') (d', g') ∗
        ty_gho ty x' d' g' tid ∗ l #↦!∗ ty_phys ty x' tid.
  Proof. by rewrite uniq_body_fml_sem. Qed.
  Lemma uniq_body_fml_sem_2 {𝔄} (ty: type 𝔄) x ξi tid l x' d' g' :
    .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x' (vπ x') (d', g') -∗
    ty_gho ty x' d' g' tid -∗ l #↦!∗ ty_phys ty x' tid -∗
    bor_sem (uniq_body_fml ty x ξi tid l).
  Proof.
    rewrite uniq_body_fml_sem. iIntros "? ? ?". iExists x', d', g'. iFrame.
  Qed.

  Definition uniq_body_pers_component {𝔄} (ty: type 𝔄) (x: ~~𝔄)
    (ξi: positive) (d g: nat) (idx: Idx) (κ: lft) (tid: thread_id) (l: cloc)
    : iProp Σ := bor_sem (idxbor_fml κ idx (uniq_body_fml ty x ξi tid l)).

  (** The original also carries [⧗1], the credit its clients spend on the
    [▷] in front of the borrowed contents.  There is none here. *)
  Definition uniq_body {𝔄} (ty: type 𝔄) (x: ~~𝔄) (ξi: positive)
    (d g: nat) (idx: Idx) (κ: lft) (tid: thread_id) (l: cloc) : iProp Σ :=
    .VO[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x (d, g) ∗
    idx_bor_tok idx ∗
    uniq_body_pers_component ty x ξi d g idx κ tid l.

  Lemma uniq_body_pers_component_impl {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l :
    uniq_body ty x ξi d g idx κ tid l -∗
      uniq_body_pers_component ty x ξi d g idx κ tid l.
  Proof. by iIntros "(_ & _ & $)". Qed.

  #[export] Instance uniq_body_pers_component_persistent
    {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l :
    Persistent (uniq_body_pers_component ty x ξi d g idx κ tid l).
  Proof. exact _. Qed.

  (** Allocating a unique borrow.

    The original takes a [⧗1] to seed [uniq_body]'s credit and a
    [⧖(S d `max` g)] to put inside the borrow; both are gone. *)
  Lemma alloc_uniq_body {𝔄} (ty: type 𝔄) (x: ~~𝔄) (d g: nat)
      (κ: lft) (tid: thread_id) (l: cloc) E :
    ↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
    ty_gho ty x d g tid -∗ l #↦!∗ ty_phys ty x tid =[alerus_wsat]{E}=∗
      ∃ ξi ζi idx,
        uniq_body ty x ξi d g idx κ tid l ∗
        ⟨π, π (PrVar (at_locₛ 𝔄 ↾ prval_to_inh (@vπ (at_locₛ 𝔄) (l.1, x))) ζi)
              = (l.1, π (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi))⟩ ∗
        ([†κ] =[alerus_wsat]=∗ bor_sem (uniq_body_fml ty x ξi tid l)).
  Proof.
    move=> ?. iIntros "#LFT #PROPH #UNIQ gho pt W".
    iMod (uniq_intro x (vπ x) (d, g) with "PROPH UNIQ") as (ξi) "[ξVo ξPc]";
      [set_solver|].
    iMod (uniq_intro (𝔄:=at_locₛ 𝔄) (l.1, x) (@vπ (at_locₛ 𝔄) (l.1, x)) (d, g)
      with "PROPH UNIQ") as (ζi) "[ζVo ζPc]"; [set_solver|].
    iDestruct (uniq_proph_tok with "ξVo ξPc") as "(ξVo & ξtok & ξPc)".
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζtok & ζPc)".
    set ζ := PrVar (at_locₛ 𝔄 ↾ prval_to_inh (@vπ (at_locₛ 𝔄) (l.1, x))) ζi.
    set ξ := PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi.
    iMod (proph_resolve_toks _ ζ (λ π, (l.1, π ξ)) [ξ] with "PROPH ζtok [ξtok]")
      as "[ζObs ξtok]".
    { set_solver. }
    { move=> ?? asn. rewrite asn; [done|]. apply list_elem_of_here. }
    { rewrite big_sepL_singleton. iFrame "ξtok". }
    rewrite big_sepL_singleton. iSpecialize ("ξPc" with "ξtok").
    iDestruct (llftl_borrow κ (uniq_body_fml ty x ξi tid l)
      with "LFT [gho pt ξPc]") as "B".
    { by iApply (uniq_body_fml_sem_2 with "ξPc gho pt"). }
    iDestruct (bupdw_incl (W:=alerus_wsat) with "B") as "B'".
    iMod ("B'" with "W") as "[$ [Bor Back]]".
    rewrite idxbor_fml_of_bor. iDestruct "Bor" as (idx) "[Bor Tok]".
    iModIntro. iExists ξi, ζi, idx. iFrame "ζObs Bor Tok ξVo".
    iIntros "†". by iApply (bupdw_incl (W:=alerus_wsat) with "(Back †)").
  Qed.

  (** [idx_bor_tok] is ghost ownership of a borrow state, so the formula
    language can express it: [BorStateFml] is exactly that. *)
  Definition idx_bor_tok_fml (idx : Idx) : FML $oi Σ :=
    bor_state_fml idx.1 (Borrow (set_map LtAtomSwell idx.2) {[default_dead]}).
  Lemma idx_bor_tok_fml_sem idx :
    bor_sem (idx_bor_tok_fml idx) ⊣⊢ idx_bor_tok idx.
  Proof. case idx=> ??. apply bor_state_fml_sem. Qed.
  Lemma idx_bor_tok_fml_sem_at {sem} (H : alt_sem sem) idx :
    sem (idx_bor_tok_fml idx) ⊣⊢ idx_bor_tok idx.
  Proof.
    rewrite /idx_bor_tok_fml (bor_state_sem_at H).
    by rewrite -/(idx_bor_tok_fml idx) idx_bor_tok_fml_sem.
  Qed.

  (** [&{κ}] gives a guard from [@[κ]].

    The original's version is stated at guard index 1 and spends a
    [guards_later_absorb_1]; there are no indices and no laters here. *)
  Lemma bor_to_guard {Px} κ :
    llft_ctx -∗ &{κ} Px =[alerus_wsat]=∗ (@[κ] &&{Wguard}&&> bor_sem Px).
  Proof.
    iIntros "#LFT Bor W".
    rewrite idxbor_fml_of_bor. iDestruct "Bor" as (idx) "[#Borx Tok]".
    iDestruct (idxbor_fml_sem_1 with "Borx") as "#Bor".
    iDestruct (llftl_borrow_shared κ (idx_bor_tok_fml idx) with "[Tok]")
      as "Sh"; [by rewrite idx_bor_tok_fml_sem|].
    iDestruct (bupdw_incl (W:=alerus_wsat) with "Sh") as "Sh'".
    iMod ("Sh'" with "W") as "[$ [#Gtok _]]". iModIntro.
    iAssert (@[κ] &&{Wguard}&&> idx_bor_tok idx)%I as "#Gtok'".
    { iApply (guard_rhs_iff (idx_bor_tok_fml_sem idx)). iApply "Gtok". }
    iDestruct (llftl_idx_bor_guard' κ idx _ (@[κ])%I with "LFT Bor [] Gtok'")
      as "#G"; [iApply guard_refl|].
    by iApply (guard_rhs_sep_r with "G").
  Qed.

  Lemma shr_bor_from_finalized_uniq_bor {𝔄} (ty: type 𝔄) x ξi d g κ tid l :
    llft_ctx -∗ &{κ} (uniq_body_at_fml ty x ξi x d g tid l)
      =[alerus_wsat]=∗
      dguard (alive_fml κ)
        (ty.(ty_ghox) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid)%FML.
  Proof.
    iIntros "#LFT Bor W". iMod (dguard_of_bor with "LFT Bor W") as "[$ #G]".
    iModIntro. by iApply (dguard_rhs_sep_r with "G").
  Qed.

  (** Pin down a guarded existential whose witness another guard determines.

    Leaf's [guards_exist_eq], minus the later indices. *)
  Lemma guard_exist_eq {A B C} (a' : A) (b' : B) (c' : C) {W}
    (P Q : iProp Σ) (X : A → B → C → iProp Σ) :
    (∀ a b c, (Q ∧ X a b c) ⊢ ⌜a = a' ∧ b = b' ∧ c = c'⌝) →
    (P &&{W}&&> Q) -∗ (P &&{W}&&> ∃ a b c, X a b c) -∗
      P &&{W}&&> X a' b' c'.
  Proof.
    move=> Hent. rewrite /guard. iIntros "#gQ #gX !>" (T) "PT".
    iAssert (Q ∧ ((∃ a b c, X a b c) ∗
      ((∃ a b c, X a b c) -∗ W ∗ T)))%I with "[PT]" as "H".
    { iSplit; [iDestruct ("gQ" with "PT") as "[$ _]"|by iApply "gX"]. }
    rewrite bi.sep_exist_r bi.and_exist_l. iDestruct "H" as (a) "H".
    rewrite bi.sep_exist_r bi.and_exist_l. iDestruct "H" as (b) "H".
    rewrite bi.sep_exist_r bi.and_exist_l. iDestruct "H" as (c) "H".
    iAssert (⌜a = a' ∧ b = b' ∧ c = c'⌝ ∧
      (X a b c ∗ ((∃ a b c, X a b c) -∗ W ∗ T)))%I with "[H]" as "H".
    { iSplit.
      - iApply Hent. iSplit; [by iDestruct "H" as "[$ _]"|].
        by iDestruct "H" as "[_ [$ _]]".
      - by iDestruct "H" as "[_ $]". }
    iDestruct "H" as "[%Heq H]". destruct Heq as [->[->->]].
    iDestruct "H" as "[$ back]". iIntros "X". iApply "back".
    iExists a', b', c'. iFrame.
  Qed.

  (** Similar to [†κ], but the inclusion rule applies immediately instead of
    through an update. *)
  (** A [dincl], matching [basically_dead_fml], which holds an [incl_fml]. *)
  Definition basically_dead (κ: lft) : iProp Σ :=
    ∃ κ', dincl κ κ' ∗ [†κ'].

  #[export] Instance basically_dead_persistent κ : Persistent (basically_dead κ).
  Proof. exact _. Qed.

  (** Weakening by a storable inclusion *)
  Lemma basically_dead_incl κ κ' :
    dincl κ' κ -∗ basically_dead κ -∗ basically_dead κ'.
  Proof.
    iIntros "#Incl (%κ'' & #Incl2 & #Dead)". iExists κ''. iFrame "Dead".
    iApply (dincl_trans with "Incl Incl2").
  Qed.

  (** Bumping the depth indices of a unique borrow.

    The original's [⧖(S d' `max` g')] and its credit disappear with the time
    receipts, and the arbitrary [Timeless G] guarding [@[κ]] becomes the
    fractional share inside an [Ltok], as everywhere else in this port. *)
  Lemma uniq_body_mono_upd {𝔄} (ty: type 𝔄) x ξi d g d' g' idx κ tid l
      γ L q E :
    ↑Nllft ∪ ↑uniqN ⊆ E → d ≤ d' → g ≤ g' →
    llft_ctx -∗ uniq_ctx -∗ (frac_tok γ q &&{Wguard}&&> @[κ]) -∗
    Ltok γ L q -∗ uniq_body ty x ξi d g idx κ tid l =[alerus_wsat]{E}=∗
      Ltok γ L q ∗ uniq_body ty x ξi d' g' idx κ tid l.
  Proof.
    move=> HE ??. iIntros "#LFT #UNIQ #Gκ [#key tok] (ξVo & ξTok & #ξBor) W".
    iAssert (bor_sem (gsrc_fml (GFrac γ q)) &&{Wguard}&&> @[κ])%I as "#Gκ'".
    { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γ q))). iApply "Gκ". }
    iDestruct (idxbor_fml_sem_1 with "ξBor") as "#ξBor1".
    iDestruct (llftl_bor_idx_acc_guarded E (gsrc_fml (GFrac γ q)) κ idx
      with "LFT ξBor1 ξTok Gκ' [tok]") as "A".
    { by iApply (gsrc_fml_sem_2 (s := GFrac γ q)). }
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=E) with "A") as "A'";
      [done|].
    iMod ("A'" with "W") as "[W [Inner Back]]".
    rewrite uniq_body_fml_sem.
    iDestruct "Inner" as (x'' d'' g'') "(ξPc & Gho & Phys)".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<- Heq]. inversion Heq.
    subst d'' g''.
    iMod (uniq_update (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi) x (vπ x) (d', g')
      with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; [solve_ndisj|].
    iDestruct (ty_gho_depth_mono ty d g d' g' x tid with "Gho")
      as "[Gho _]"; [done|done|].
    iDestruct ("Back" with "[ξPc Gho Phys]") as "B".
    { iExists x, d', g'. iFrame. }
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=E) with "B") as "B'";
      [etrans; [|exact HE]; solve_ndisj|].
    iMod ("B'" with "W") as "[$ [ξTok tok]]".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ q) with "tok") as "tok".
    iModIntro. iFrame "key tok ξVo ξTok ξBor".
  Qed.

  (** Resolving the prophecy of a unique borrow.

    The original's proof is mostly credit arithmetic: it buys
    [d*(g+1) + d*(g+1) + 2] later credits out of the time receipt
    [⧖(S d `max` g)] and spends them stripping the [▷]s in front of the
    borrowed contents, of the [∀ζ] guard and of the resolution itself.  None
    of those [▷]s exist here, so all of it goes; what is left is the
    skeleton - halve the share, lend one half to a fresh lifetime [κ'],
    reborrow the contents to [κ'], resolve under it, then let [κ'] die. *)
  Lemma resolve_uniq_body {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E L γ q F :
    lctx_lft_alive E L κ → NalerusE ⊆ F →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ κ ⊑ ty_lft ty -∗ elctx_interp E -∗
    Ltok γ L q -∗ uniq_body ty x ξi d g idx κ tid l =[alerus_wsat]{F}=∗
      ⟨π, π (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi) = vπ x π⟩ ∗ Ltok γ L q ∗
      dguard (alive_fml κ)
        (ty.(ty_ghox) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid)%FML.
  Proof.
    move=> Alv HF.
    have ? : Inhabited (~~𝔄) := populate x.
    iIntros "#LFT #PROPH #UNIQ #In #E [#key f] (ξVo & ξTok & #ξBor) W".
    (* The share guards [@[κ]]. *)
    iDestruct (Ltok_acc (W:=alerus_wsat) with "[$key $f] W") as "[L →W]".
    iDestruct (Alv with "L E") as "#Lkg".
    iDestruct ("→W" with "L") as "[W [_ f]]".
    iAssert (frac_tok γ (q/2) &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "[] Lkg").
      iApply (Ltok_guard_frac with "key"). }
    (* Halve the share; one half goes to a fresh lifetime [κ']. *)
    iDestruct (Ltok_split_1 with "[$key $f]") as "[[_ fa] [_ fb]]".
    iDestruct (llftl_begin' with "LFT") as "B".
    iDestruct (bupdw_incl (W:=alerus_wsat) with "B") as "B'".
    iMod ("B'" with "W") as "[W (%κ' & κ'tok & %κ'ne)]".
    iDestruct (llftl_borrow_shared κ' (gsrc_fml (GFrac γ (q/2))) with "[fa]")
      as "Sh"; [by iApply (gsrc_fml_sem_2 (s := GFrac γ (q/2)))|].
    iDestruct (bupdw_incl (W:=alerus_wsat) with "Sh") as "Sh'".
    iMod ("Sh'" with "W") as "[W [#Sh0 ToF1]]".
    iAssert (κ' ⊑ κ)%I as "#Incl".
    { iApply (guard_trans with "[] Gκ").
      iApply (guard_rhs_iff (gsrc_fml_sem (GFrac γ (q/2)))). iApply "Sh0". }
    (* Freeze the three existentials away. *)
    iDestruct (idxbor_fml_to_full with "ξBor ξTok") as "Bor".
    iDestruct (llftl_bor_freeze F κ
      (λ y, ex_fml (λ e, ex_fml (λ h, uniq_body_at_fml ty x ξi y e h tid l)))
      (uniq_body_fml ty x ξi tid l) (ex_fml_sem _) with "LFT Bor") as "Fr".
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=F) with "Fr") as "Fr'";
      [done|].
    iMod ("Fr'" with "W") as "[W (%x1 & Bor)]".
    iDestruct (llftl_bor_freeze F κ
      (λ e, ex_fml (λ h, uniq_body_at_fml ty x ξi x1 e h tid l)) _
      (ex_fml_sem _) with "LFT Bor") as "Fr".
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=F) with "Fr") as "Fr'";
      [done|].
    iMod ("Fr'" with "W") as "[W (%d1 & Bor)]".
    iDestruct (llftl_bor_freeze F κ
      (λ h, uniq_body_at_fml ty x ξi x1 d1 h tid l) _
      (ex_fml_sem _) with "LFT Bor") as "Fr".
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=F) with "Fr") as "Fr'";
      [done|].
    iMod ("Fr'" with "W") as "[W (%g1 & Bor)]".
    (* Reborrow to [κ'] and open. *)
    iDestruct (llftl_reborrow_meet F κ κ' _ with "LFT Bor") as "Rb".
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=F) with "Rb") as "Rb'";
      [done|].
    iMod ("Rb'" with "W") as "[W [Bor' Back]]".
    iDestruct (llftl_bor_acc' F _ κ' (κ ⊓ κ') with "LFT [] Bor' κ'tok")
      as "Acc";
      [iApply llftl_incl_glb; [iFrame "Incl"|iApply guard_refl]|].
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=F) with "Acc") as "Acc'";
      [done|].
    iMod ("Acc'" with "W") as "[W [Inner ForallQ]]".
    iEval (rewrite uniq_body_at_fml_sem) in "Inner".
    iDestruct "Inner" as "(ξPc & Gho & Phys)".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<- Heq]. inversion Heq.
    subst d1 g1.
    (* Resolve. *)
    iDestruct (ty_gho_pers_impl with "Gho") as "#GhoPers".
    iAssert (∀ ζ, ⌜ζ ∈ ξl x⌝ -∗
      ((frac_tok γ (q/2) ∗ ty_gho ty x d g tid) &&{Wguard}&&> 1:[ζ]))%I
      as "#Hallζ".
    { iIntros (ζ) "%Hin".
      iApply (ty_guard_proph _ ty κ x d g tid ζ
        (frac_tok γ (q/2) ∗ ty_gho ty x d g tid) Hin with "LFT In GhoPers").
      - iApply (guard_trans with "[] Gκ"). iApply guard_sep_l.
      - iApply guard_sep_r. }
    iMod (uniq_resolve_guarded (W:=alerus_wsat)
      (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi) (ξl x) x (d, g) x (vπ x) (d, g)
      with "Hallζ UNIQ PROPH ξVo ξPc [$fb $Gho] W")
      as "[W (#Obs & ξPc & [fb Gho])]";
      [etrans; [|exact HF]; rewrite /NalerusE; set_solver|apply syn_indep|].
    (* Close the borrow and let [κ'] die. *)
    iDestruct ("ForallQ" $! (uniq_body_at_fml ty x ξi x d g tid l)
      with "[] [ξPc Gho Phys]") as "Cl".
    { by iIntros "$". }
    { rewrite uniq_body_at_fml_sem. iFrame. }
    iDestruct (bupdw_incl (W:=alerus_wsat) with "Cl") as "Cl'".
    iMod ("Cl'" with "W") as "[W [_ κ'tok]]".
    iDestruct (llftl_end' κ' κ'ne with "LFT κ'tok") as "End".
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=F) with "End") as "End'";
      [etrans; [|exact HF]; rewrite /NalerusE; set_solver|].
    iMod ("End'" with "W") as "[W #†κ']".
    iDestruct ("Back" with "†κ'") as "Bk".
    iDestruct (bupdw_incl (W:=alerus_wsat) with "Bk") as "Bk'".
    iMod ("Bk'" with "W") as "[W Bor]".
    iDestruct ("ToF1" with "†κ'") as "ToF1'".
    iDestruct (bupdw_incl (W:=alerus_wsat) with "ToF1'") as "ToF1''".
    iMod ("ToF1''" with "W") as "[W fa]".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ (q/2)) with "fa") as "fa".
    iMod (shr_bor_from_finalized_uniq_bor with "LFT Bor W") as "[W #G]".
    iModIntro. iFrame "W Obs".
    iDestruct (Ltok_split_2 with "[$key $fa] [$key $fb]") as "$".
    iApply "G".
  Qed.

  (** The value observer pins down the witnesses of the borrowed body. *)
  Lemma uniq_body_at_agree {𝔄} (ty: type 𝔄) x ξi d g tid l y e h :
    (.VO[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x (d, g) ∧
      (.PC[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] y (vπ y) (e, h) ∗
        ty_gho ty y e h tid ∗ l #↦!∗ ty_phys ty y tid))
    ⊢ ⌜y = x ∧ e = d ∧ h = g⌝.
  Proof.
    iIntros "And".
    iDestruct (uniq_and_agree (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi)
      with "[And]") as %[Heq1 Heq2].
    { iSplit; [by iDestruct "And" as "[$ _]"|].
      by iDestruct "And" as "[_ [$ _]]". }
    iPureIntro. inversion Heq2. by subst y e h.
  Qed.

  (** Reading the physical contents off a guard to the body *)
  Lemma uniq_guards_get_guards_pt {𝔄} (ty: type 𝔄) (P Q R : iProp Σ)
      x d g ξi tid l :
    ((P ∗ .VO[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x (d, g) ∗ R)
      &&{Wguard}&&> (Q ∗ bor_sem (uniq_body_fml ty x ξi tid l))) ⊢
    ((P ∗ .VO[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x (d, g) ∗ R)
      &&{Wguard}&&> l #↦!∗ ty_phys ty x tid).
  Proof.
    iIntros "#G".
    iDestruct (guard_rhs_sep_r with "G") as "#G2".
    iDestruct (guard_rhs_iff (uniq_body_fml_sem ty x ξi tid l) with "G2")
      as "#G3".
    iDestruct (guard_exist_eq x d g _ _ _ (uniq_body_at_agree ty x ξi d g tid l)
      with "[] G3") as "#G4".
    { iApply guard_intro. iIntros "!> (A & B & C)". iFrame "B".
      iIntros "B". iFrame. }
    iDestruct (guard_rhs_sep_r with "G4") as "#G5".
    iApply (guard_rhs_sep_r with "G5").
  Qed.

  (** [uniq_body_at_agree] at a candidate interpretation *)
  Lemma uniq_body_at_agree_at {sem} (H : alt_sem sem) {𝔄} (ty: type 𝔄)
      x ξi d g tid l y e h :
    (.VO[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x (d, g) ∧
      (.PC[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] y (vπ y) (e, h) ∗
        sem (ty.(ty_ghox) y e h tid) ∗ l #↦!∗ ty_phys ty y tid))
    ⊢ ⌜y = x ∧ e = d ∧ h = g⌝.
  Proof.
    iIntros "And".
    iDestruct (uniq_and_agree (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi)
      with "[And]") as %[Heq1 Heq2].
    { iSplit; [by iDestruct "And" as "[$ _]"|].
      by iDestruct "And" as "[_ [$ _]]". }
    iPureIntro. inversion Heq2. by subst y e h.
  Qed.

  (** [uniq_body_fml_sem] at a candidate interpretation *)
  Lemma uniq_body_fml_sem_at {sem} (H : alt_sem sem) {𝔄} (ty: type 𝔄)
      x ξi tid l :
    sem (uniq_body_fml ty x ξi tid l) ⊣⊢
      ∃ (y: ~~𝔄) (e h: nat),
        .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] y (vπ y) (e, h) ∗
        sem (ty.(ty_ghox) y e h tid) ∗ l #↦!∗ ty_phys ty y tid.
  Proof.
    rewrite /uniq_body_fml (ex_sem_at H). apply bi.exist_proper=> y.
    rewrite (ex_sem_at H). apply bi.exist_proper=> e.
    rewrite (ex_sem_at H). apply bi.exist_proper=> h.
    rewrite /uniq_body_at_fml !(sep_sem_at H) (pc_sem_at H)
      (ccells_sem_at H) //.
  Qed.

  (** A guard to the whole [uniq_body] gives one to its contents *)
  Lemma guard_inner_from_guard_uniq_body {𝔄} (ty: type 𝔄) x ξi d g ξidx κ
      tid l G :
    llft_ctx -∗
    uniq_body_pers_component ty x ξi d g ξidx κ tid l -∗
    (G &&{Wguard}&&> uniq_body ty x ξi d g ξidx κ tid l) -∗
    (G &&{Wguard}&&> @[κ]) -∗
    (G &&{Wguard}&&> (ty_gho ty x d g tid ∗ l #↦!∗ ty_phys ty x tid)).
  Proof.
    iIntros "#LFT #Bor #Guniq #Gk".
    iDestruct (guard_rhs_sep_l with "Guniq") as "#Gvo".
    iDestruct (guard_rhs_sep_r with "Guniq") as "#Guniq2".
    iDestruct (guard_rhs_sep_l with "Guniq2") as "#Gtok".
    iDestruct (idxbor_fml_sem_1 with "Bor") as "#Bor1".
    iDestruct (llftl_idx_bor_guard' with "LFT Bor1 Gk Gtok") as "#Ginner".
    iDestruct (guard_rhs_sep_r with "Ginner") as "#Ginner2".
    iDestruct (guard_rhs_iff (uniq_body_fml_sem ty x ξi tid l) with "Ginner2")
      as "#Ginner3".
    iDestruct (guard_exist_eq x d g _ _ _ (uniq_body_at_agree ty x ξi d g tid l)
      with "Gvo Ginner3") as "#G'".
    iApply (guard_rhs_sep_r with "G'").
  Qed.

  (** Moving a unique borrow to another type, along a prophecy-level
    injection.  The original's [▷]s in front of the ghost assertions and its
    [⧖] witnesses go with the time receipts; the arbitrary [Timeless G]
    guarding [@[κ]] is the fraction inside an [Ltok]. *)
  Lemma uniq_body_transform {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) x x' d g ξi ξidx
      κ tid l l' E γ L q (f: 𝔅 →ₛ 𝔄) :
    Inj eq eq ((!ₛ) f) → ↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
    (ty_gho ty x d g tid ∗ l #↦!∗ ty_phys ty x tid
      ={E}=∗ ty_gho ty' x' d g tid ∗ l' #↦!∗ ty_phys ty' x' tid ∗
      (∀ y e h, ty_gho ty' y e h tid ∗ l' #↦!∗ ty_phys ty' y tid
        ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ∃ e2 h2,
          ty_gho ty (f ~~$ₛ y) e2 h2 tid ∗
          l #↦!∗ ty_phys ty (f ~~$ₛ y) tid)) -∗
    (frac_tok γ q &&{Wguard}&&> @[κ]) -∗ Ltok γ L q -∗
    uniq_body ty x ξi d g ξidx κ tid l =[alerus_wsat]{E}=∗
      ∃ ζi ζidx,
        ⟨π, π (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi) =
            (!ₛ) f (π (PrVar (𝔅 ↾ prval_to_inh (vπ x')) ζi))⟩ ∗
        uniq_body ty' x' ζi d g ζidx κ tid l' ∗ Ltok γ L q.
  Proof.
    move=> ? HE.
    iIntros "#LFT #PROPH #UNIQ wand #Gκ [#key f] (ξVo & ξTok & #ξBor) W".
    iDestruct (idxbor_fml_to_full with "ξBor ξTok") as "Bor".
    iAssert (bor_sem (gsrc_fml (GFrac γ q)) &&{Wguard}&&> @[κ])%I as "#Gκ'".
    { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γ q))). iApply "Gκ". }
    iDestruct (llftl_bor_acc_guarded E (gsrc_fml (GFrac γ q)) κ
      with "LFT Bor Gκ' [f]") as "A";
      [by iApply (gsrc_fml_sem_2 (s := GFrac γ q))|].
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=E) with "A") as "A'";
      [done|].
    iMod ("A'" with "W") as "[W [P ToBor]]".
    iEval (rewrite uniq_body_fml_sem) in "P".
    iDestruct "P" as (x1 d1 g1) "(ξPc & Gho & Pt)".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<- Heq]. inversion Heq.
    subst d1 g1.
    iMod (uniq_intro x' (vπ x') (d, g) with "PROPH UNIQ") as (ζi) "[ζVo ζPc]";
      [set_solver|].
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ToζPc)".
    rewrite proph_tok_singleton.
    set ξ := PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi.
    set ζ := PrVar (𝔅 ↾ prval_to_inh (@vπ 𝔅 x')) ζi.
    iMod (uniq_preresolve ξ _ (λ π, f $ₛ (π ζ)) with "UNIQ PROPH ξVo ξPc ζ")
      as "(#EqObs & ζ & ToξPc)";
      [set_solver|apply proph_dep_constr, (proph_dep_one ζ)|].
    iDestruct ("ToζPc" with "ζ") as "ζPc".
    iCombine "Gho Pt" as "GhoPt". iMod ("wand" with "GhoPt") as "(Gho & Pt & R)".
    iDestruct ("ToBor" $! (uniq_body_fml ty' x' ζi tid l')
      with "[ToξPc R] [ζPc Gho Pt]") as "A".
    { iIntros "H". iEval (rewrite uniq_body_fml_sem) in "H".
      iDestruct "H" as (y e h) "(ζPc & Gho2 & Pt2)".
      iCombine "Gho2 Pt2" as "GhoPt2".
      iMod ("R" with "GhoPt2") as (e2 h2) "[Gho1 Pt1]". iModIntro.
      iApply (uniq_body_fml_sem_2 with "[ζPc ToξPc] Gho1 Pt1").
      iApply "ToξPc".
      iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "Eqz".
      iDestruct (proph_eqz_constr ((!ₛ) f) with "Eqz") as "Eqz".
      iApply (proph_eqz_eq with "Eqz"); [done|].
      fun_ext=> ?. by rewrite /= syn_type_morphism_commutes. }
    { by iApply (uniq_body_fml_sem_2 with "ζPc Gho Pt"). }
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=E) with "A") as "A'";
      [etrans; [|exact HE]; solve_ndisj|].
    iMod ("A'" with "W") as "[W [Bor2 f]]".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ q) with "f") as "f".
    iModIntro. iFrame "W".
    rewrite idxbor_fml_of_bor. iDestruct "Bor2" as (ζidx) "[ζBor ζTok]".
    iExists ζi, ζidx. iFrame "EqObs key f ζVo ζTok ζBor".
  Qed.

  (** [uniq_body] as a formula: [&uniq{κ} ty]'s own ghost assertion holds
    one, and that assertion is a formula now. *)
  Definition uniq_body_fmlx {𝔄} (ty: type 𝔄) (x: ~~𝔄) (ξi: positive)
    (d g: nat) (idx: Idx) (κ: lft) (tid: thread_id) (l: cloc) : FML $oi Σ :=
    (.VOx[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x (d, g) ∗
     idx_bor_tok_fml idx ∗ &x{κ, idx} (uniq_body_fml ty x ξi tid l))%FML.

  Lemma uniq_body_fmlx_sem {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l :
    bor_sem (uniq_body_fmlx ty x ξi d g idx κ tid l) ⊣⊢
      uniq_body ty x ξi d g idx κ tid l.
  Proof.
    rewrite /uniq_body_fmlx /uniq_body /uniq_body_pers_component !bor_sep_sem
      vo_fml_sem idx_bor_tok_fml_sem //.
  Qed.

  (** [guard_inner_from_guard_uniq_body] for *stored* guards: the inner
    guard a shared reference's ghost assertion has to hold is itself a
    formula, so the construction has to run at every candidate. *)
  Lemma dguard_inner_from_guard_uniq_body {𝔄} (ty: type 𝔄) x ξi d g ξidx κ
      tid l Gx :
    uniq_body_pers_component ty x ξi d g ξidx κ tid l -∗
    dguard Gx (uniq_body_fmlx ty x ξi d g ξidx κ tid l) -∗
    dguard Gx (alive_fml κ) -∗
    dguard Gx (ty.(ty_ghox) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid)%FML.
  Proof.
    have ? := guard_fml_pers_at alt_here.
    iIntros "#Bor #Guniq #Gk". iApply dguard_of_all. iIntros (sem' Hs Hi).
    have ? := guard_fml_pers_at Hs.
    iDestruct (guard_fml_sem_into alt_here Hs Hi with "Guniq") as "#Gu".
    iDestruct (guard_fml_sem_into alt_here Hs Hi with "Gk") as "#Gk0".
    iDestruct (guard_rhs_iff (alive_sem_at Hs κ) with "Gk0") as "#Gκ".
    iDestruct (guard_rhs_iff (sep_sem_at Hs _ _) with "Gu") as "#Gu0".
    iDestruct (guard_rhs_sep_l with "Gu0") as "#Gvo0".
    iDestruct (guard_rhs_iff (vo_sem_at Hs _ _ _) with "Gvo0") as "#Gvo".
    iDestruct (guard_rhs_sep_r with "Gu0") as "#Gu1".
    iDestruct (guard_rhs_iff (sep_sem_at Hs _ _) with "Gu1") as "#Gu2".
    iDestruct (guard_rhs_sep_l with "Gu2") as "#Gtok0".
    iDestruct (guard_rhs_iff (idx_bor_tok_fml_sem_at Hs ξidx) with "Gtok0")
      as "#Gtok".
    rewrite /uniq_body_pers_component.
    iDestruct (idxbor_fml_into alt_here Hs Hi with "Bor") as "#Bor'".
    iDestruct (idxbor_fml_guard_at Hs κ ξidx _ (sem' Gx)
      with "Bor' Gκ Gtok") as "#Ginner".
    iDestruct (guard_rhs_sep_r with "Ginner") as "#Ginner2".
    iDestruct (guard_rhs_iff (uniq_body_fml_sem_at Hs ty x ξi tid l)
      with "Ginner2") as "#Ginner3".
    iDestruct (guard_exist_eq x d g _ _ _
      (uniq_body_at_agree_at Hs ty x ξi d g tid l) with "Gvo Ginner3")
      as "#G'".
    iDestruct (guard_rhs_sep_r with "G'") as "#G''".
    iApply (guard_rhs_iff (Q' := sem' (ty.(ty_ghox) x d g tid ∗
      l #↦!∗ ty.(ty_phys) x tid)%FML)); [|iApply "G''"].
    rewrite (sep_sem_at Hs) (ccells_sem_at Hs) //.
  Qed.

  Definition basically_dead_fml (κ: lft) : FML $oi Σ :=
    ex_fml (λ κ', ((κ ⊑x κ') ∗ [†x κ'])%FML).

  (** Persistence of the three formulas above, at a candidate *)
  Lemma basically_dead_pers_at {sem} (H : alt_sem sem) κ :
    Persistent (sem (basically_dead_fml κ)).
  Proof.
    rewrite /basically_dead_fml. apply (ex_pers_at H)=> κ'.
    apply (sep_pers_at H); [exact _|by apply dead_pers_at].
  Qed.

  Lemma basically_dead_fml_sem κ :
    bor_sem (basically_dead_fml κ) ⊣⊢ basically_dead κ.
  Proof.
    rewrite /basically_dead_fml /basically_dead ex_fml_sem.
    apply bi.exist_proper=> κ'. by rewrite bor_sep_sem dead_fml_sem incl_fml_sem.
  Qed.

  (** Changing the thread id of the borrowed body *)
  Lemma uniq_body_fml_sem_tid {𝔄} (ty: type 𝔄) x ξi tid tid' l :
    (∀ y e h, ty_gho ty y e h tid ⊣⊢ ty_gho ty y e h tid') →
    (∀ y, ty_phys ty y tid = ty_phys ty y tid') →
    bor_sem (uniq_body_fml ty x ξi tid l) ⊣⊢
      bor_sem (uniq_body_fml ty x ξi tid' l).
  Proof.
    move=> Hg Hp. rewrite !uniq_body_fml_sem.
    do 3 (apply bi.exist_proper=> ?). by rewrite Hg Hp.
  Qed.

  (** The same at a candidate interpretation *)
  Lemma uniq_body_fml_sem_tid_at {sem} (H : alt_sem sem) {𝔄} (ty: type 𝔄)
      x ξi tid tid' l :
    (∀ y e h, sem (ty.(ty_ghox) y e h tid) ⊣⊢ sem (ty.(ty_ghox) y e h tid')) →
    (∀ y, ty_phys ty y tid = ty_phys ty y tid') →
    sem (uniq_body_fml ty x ξi tid l) ⊣⊢
      sem (uniq_body_fml ty x ξi tid' l).
  Proof.
    move=> Hg Hp. rewrite /uniq_body_fml !(ex_sem_at H).
    apply bi.exist_proper=> x'. rewrite !(ex_sem_at H).
    apply bi.exist_proper=> d'. rewrite !(ex_sem_at H).
    apply bi.exist_proper=> g'.
    rewrite /uniq_body_at_fml !(sep_sem_at H) Hg Hp //.
  Qed.

  (** Changing the type of the borrowed body, at every candidate *)
  Lemma uniq_body_fml_iff_at {𝔄} (ty ty': type 𝔄) x ξi tid l :
    (∀ y, ty_phys ty y tid = ty_phys ty' y tid) →
    □ (∀ sem' (_ : alt_sem sem'), ∀ y e h,
         sem' (ty.(ty_ghox) y e h tid) ∗-∗ sem' (ty'.(ty_ghox) y e h tid)) ⊢
    □ (∀ sem' (_ : alt_sem sem'),
         sem' (uniq_body_fml ty x ξi tid l) ∗-∗
         sem' (uniq_body_fml ty' x ξi tid l)).
  Proof.
    move=> Hp. iIntros "#Eq !>" (sem' Hs). rewrite /uniq_body_fml.
    iSplit; iIntros "B";
      rewrite ?(ex_sem_at Hs); iDestruct "B" as (y) "B"; iExists y;
      rewrite ?(ex_sem_at Hs); iDestruct "B" as (e) "B"; iExists e;
      rewrite ?(ex_sem_at Hs); iDestruct "B" as (h) "B"; iExists h;
      rewrite /uniq_body_at_fml !(sep_sem_at Hs) (Hp y);
      iDestruct "B" as "(A & G & P)"; iFrame "A P";
      iDestruct ("Eq" $! sem' Hs y e h) as "[F Bk]";
      [by iApply "F"|by iApply "Bk"].
  Qed.

  (** [incl_uniq_body_pers_component] at a candidate *)
  Lemma incl_uniq_body_pers_component_at {sem} (H : alt_sem sem)
      {𝔄} (ty ty': type 𝔄) x ξi idx κ κ' tid l :
    (∀ y, ty_phys ty y tid = ty_phys ty' y tid) →
    □ (∀ sem' (_ : alt_sem sem'), ∀ y e h,
         sem' (ty.(ty_ghox) y e h tid) ∗-∗ sem' (ty'.(ty_ghox) y e h tid)) -∗
    dincl κ' κ -∗
    sem (idxbor_fml κ idx (uniq_body_fml ty x ξi tid l)) -∗
    sem (idxbor_fml κ' idx (uniq_body_fml ty' x ξi tid l)).
  Proof.
    move=> Hp. have ? := guard_fml_pers_at H. iIntros "#Eq #InLft Pc".
    iApply (idxbor_fml_shorten_at H with "InLft").
    iApply (idxbor_fml_iff_at H κ idx _ _ with "[] Pc").
    by iApply (uniq_body_fml_iff_at ty ty' x ξi tid l Hp with "Eq").
  Qed.

  (** The body formula depends on the refinement only through the prophecy
    variable's inhabitant witness, which is proof-irrelevant. *)
  Lemma uniq_body_fml_irrel {𝔄} (ty: type 𝔄) x y ξi tid l :
    prval_to_inh (vπ x) = prval_to_inh (vπ y) →
    uniq_body_fml ty x ξi tid l = uniq_body_fml ty y ξi tid l.
  Proof. rewrite /uniq_body_fml /uniq_body_at_fml=> ->. done. Qed.
  Lemma uniq_body_pers_component_irrel {𝔄} (ty: type 𝔄) x y ξi d g d2 g2 idx
      κ tid l :
    prval_to_inh (vπ x) = prval_to_inh (vπ y) →
    uniq_body_pers_component ty x ξi d g idx κ tid l =
      uniq_body_pers_component ty y ξi d2 g2 idx κ tid l.
  Proof.
    rewrite /uniq_body_pers_component=> Heq.
    by rewrite (uniq_body_fml_irrel ty x y ξi tid l Heq).
  Qed.
End uniq_util.
