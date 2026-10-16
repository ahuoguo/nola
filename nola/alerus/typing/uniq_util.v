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
    : iProp Σ := &{κ, idx} (uniq_body_fml ty x ξi tid l).

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
    rewrite llftl_bor_idx. iDestruct "Bor" as (idx) "[Bor Tok]".
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

  (** [&{κ}] gives a guard from [@[κ]].

    The original's version is stated at guard index 1 and spends a
    [guards_later_absorb_1]; there are no indices and no laters here. *)
  Lemma bor_to_guard {Px} κ :
    llft_ctx -∗ &{κ} Px =[alerus_wsat]=∗ (@[κ] &&{Wguard}&&> bor_sem Px).
  Proof.
    iIntros "#LFT Bor W".
    rewrite llftl_bor_idx. iDestruct "Bor" as (idx) "[#Bor Tok]".
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
      (@[κ] &&{Wguard}&&>
        (ty_gho ty x d g tid ∗ l #↦!∗ ty_phys ty x tid)).
  Proof.
    iIntros "#LFT Bor W". iMod (bor_to_guard with "LFT Bor W") as "[$ #G]".
    iModIntro.
    iDestruct (guard_rhs_iff (uniq_body_at_fml_sem ty x ξi x d g tid l)
      with "G") as "#G'".
    by iApply (guard_rhs_sep_r with "G'").
  Qed.

  (** Pin down a guarded existential whose witness another guard determines.

    Leaf's [guards_exist_eq], minus the later indices. *)
  Lemma guard_exist_eq {A B C} (a' : A) (b' : B) (c' : C) (P Q : iProp Σ)
    (X : A → B → C → iProp Σ) :
    (∀ a b c, (Q ∧ X a b c) ⊢ ⌜a = a' ∧ b = b' ∧ c = c'⌝) →
    (P &&{Wguard}&&> Q) -∗ (P &&{Wguard}&&> ∃ a b c, X a b c) -∗
      P &&{Wguard}&&> X a' b' c'.
  Proof.
    move=> Hent. rewrite /guard. iIntros "#gQ #gX !>" (T) "PT".
    iAssert (Q ∧ ((∃ a b c, X a b c) ∗
      ((∃ a b c, X a b c) -∗ Wguard ∗ T)))%I with "[PT]" as "H".
    { iSplit; [iDestruct ("gQ" with "PT") as "[$ _]"|by iApply "gX"]. }
    rewrite bi.sep_exist_r bi.and_exist_l. iDestruct "H" as (a) "H".
    rewrite bi.sep_exist_r bi.and_exist_l. iDestruct "H" as (b) "H".
    rewrite bi.sep_exist_r bi.and_exist_l. iDestruct "H" as (c) "H".
    iAssert (⌜a = a' ∧ b = b' ∧ c = c'⌝ ∧
      (X a b c ∗ ((∃ a b c, X a b c) -∗ Wguard ∗ T)))%I with "[H]" as "H".
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
  Definition basically_dead (κ: lft) : iProp Σ := ∃ κ', κ ⊑ κ' ∗ [†κ'].

  #[export] Instance basically_dead_persistent κ : Persistent (basically_dead κ).
  Proof. exact _. Qed.

  Lemma basically_dead_incl κ κ' :
    κ' ⊑ κ -∗ basically_dead κ -∗ basically_dead κ'.
  Proof.
    iIntros "#Incl (%κ'' & #Incl2 & #Dead)". iExists κ''. iFrame "Dead".
    iApply (guard_trans with "Incl Incl2").
  Qed.

  Lemma incl_uniq_body_pers_component {𝔄} (ty ty': type 𝔄)
      x ξi d g idx κ κ' tid l :
    κ' ⊑ κ -∗
    □ (∀ y e h t, ty_gho ty y e h t ↔ ty_gho ty' y e h t) -∗
    (∀ y t, ⌜ty_phys ty y t = ty_phys ty' y t⌝) -∗
    uniq_body_pers_component ty x ξi d g idx κ tid l -∗
    uniq_body_pers_component ty' x ξi d g idx κ' tid l.
  Proof.
    iIntros "#InLft #EqOwn %EqPhys Pc". rewrite /uniq_body_pers_component.
    iApply (llftl_idx_shorten with "InLft").
    iApply (llftl_idx_bor_iff with "[] Pc"). iIntros "!>".
    rewrite !uniq_body_fml_sem. iSplit.
    - iIntros "(%y & %e & %h & Pc & gho & pt)". iExists y, e, h.
      rewrite EqPhys. iFrame "Pc pt". by iApply "EqOwn".
    - iIntros "(%y & %e & %h & Pc & gho & pt)". iExists y, e, h.
      rewrite EqPhys. iFrame "Pc pt". by iApply "EqOwn".
  Qed.

  Lemma incl_uniq_body {𝔄} (ty ty': type 𝔄) x ξi d g idx κ κ' tid l :
    κ' ⊑ κ -∗
    □ (∀ y e h t, ty_gho ty y e h t ↔ ty_gho ty' y e h t) -∗
    (∀ y t, ⌜ty_phys ty y t = ty_phys ty' y t⌝) -∗
    uniq_body ty x ξi d g idx κ tid l -∗
    uniq_body ty' x ξi d g idx κ' tid l.
  Proof.
    iIntros "#InLft #EqOwn %EqPhys (A & Tok & Pc)". iFrame "A Tok".
    by iApply (incl_uniq_body_pers_component with "InLft EqOwn [] Pc").
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
    iDestruct (llftl_bor_idx_acc_guarded E (gsrc_fml (GFrac γ q)) κ idx
      with "LFT ξBor ξTok Gκ' [tok]") as "A".
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
End uniq_util.
