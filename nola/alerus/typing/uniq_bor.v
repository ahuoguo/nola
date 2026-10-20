(** * Unique borrows

  Ported from VerusBelt ([typing/uniq_bor.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.

  Two changes.

  - [&uniq{κ} ty]'s ghost assertion is built from the constructors of
    [TypeFml] (see [typing/ctx.v]): it holds a value observer, an indexed
    borrow of [uniq_body_fml], the guard to [l #↦∗_] and a disjunction with
    [basically_dead κ], and every one of those is a formula now.

  - [TypeContractive] is lost, and so is [TypeNonExpansive].  VerusBelt
    gets contractiveness from [idx_bor_contractive] and
    [later_contractive]: a borrow is contractive in its contents exactly
    because the contents sit under a [▷], and [&uniq{κ}]'s
    [▷ ty.(ty_gho_pers)] supplies the other one.  Later-free a borrow
    stores a formula and is merely non-expansive - the same loss as
    [own_ptr] and [&shr{κ}].

    [TypeNonExpansive] goes too, for a reason particular to the syntactic
    interpretation: its premise about lifetimes is
    [⊢ ty_lft ty ≡ₗ ty_lft ty'], a *semantic* equivalence, while
    [&uniq{κ}]'s ghost assertion names [ty_lft ty] inside a formula, where
    only a syntactic equality would do.  Plain [NonExpansive] is fine -
    [ty ≡{n}≡ ty'] does give [ty_lfts ty = ty_lfts ty'] - and that is what
    the type formers above it use.

  [uniq_send] is commented out upstream; only [uniq_send_static] is proved,
  and the time receipts it threads through disappear here. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.typing Require Import type_context programs mod_ty uniq_util
  lft_contexts.
From nola.alerus.typing Require Export type ctx.
From nola.alerus.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Implicit Type 𝔄 𝔅: syn_type.

(** [guard_and] needs the prophecy token to be a *point* proposition; the
  lemma is there, it is just not registered as an instance. *)
Local Existing Instance proph_tok_point_prop.

Section uniq_bor.
  Context `{!typeG FML Σ}.

  Program Definition uniq_bor {𝔄} (κ: lft) (ty: type 𝔄)
    : type (uniq_borₛ 𝔄) := {|
    ty_size := 1;
    ty_lfts := κ :: ty.(ty_lfts);
    ty_E := ty.(ty_E) ++ ty_outlives_E ty κ;

    ty_ghox x d g tid :=
      match x with (l, x0, ξi, d', g', idx) =>
        ((κ ⊑x ty_lft ty) ∗ ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗
         uniq_body_fmlx ty x0 ξi d' g' idx κ tid l ∗
         guard_fml (alive_fml κ) (l #↦∗_) ∗
         (basically_dead_fml κ ∨ ty.(ty_gho_persx) x0 d' g' tid))%FML
      end;

    ty_gho_persx x d g tid :=
      match x with (l, x0, ξi, d', g', idx) =>
        (⌜S d' ≤ d ∧ g' ≤ g⌝ ∗
         (basically_dead_fml κ ∨ ty.(ty_gho_persx) x0 d' g' tid) ∗
         &x{κ, idx} (uniq_body_fml ty x0 ξi tid l))%FML
      end;

    ty_phys x tid :=
      match x with (l, x0, ξi, d', g', idx) => [FVal (LitV l.1)] end;
  |}.
  Next Obligation. move=> ?? ? [[[[[??]?]?]?]?] ?. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move=> ?? ? [[[[[??]?]?]?]?] ?. done. Qed.
  Next Obligation.
    move=> 𝔄 κ ty sem H d0 g0 d1 g1 [[[[[l x0] ξi] d'] g'] idx] tid ??.
    rewrite /=.
    have ? := guard_fml_pers_at H. have ? := idxbor_fml_pers_at H.
    have ? := ty_gho_pers_pers_at ty sem H.
    have ? := basically_dead_pers_at H. have ? := or_pers_at H.
    have ? := pure_pers_at H.
    rewrite !(sep_sem_at H) !(pure_sem_at H).
    iIntros "(#A & %B & (C1 & C2 & #C3) & #D & #E)". iSplitL.
    - iFrame "E A D C1 C2 C3". iPureIntro. lia.
    - iIntros "(_ & _ & (C1 & C2 & _) & _ & _)". iFrame "E A D C1 C2 C3".
      iPureIntro. lia.
  Qed.
  Next Obligation.
    move=> 𝔄 κ ty sem H d0 g0 d1 g1 [[[[[l x0] ξi] d'] g'] idx] tid ??.
    rewrite /=.
    have ? := guard_fml_pers_at H. have ? := idxbor_fml_pers_at H.
    have ? := ty_gho_pers_pers_at ty sem H.
    have ? := basically_dead_pers_at H. have ? := or_pers_at H.
    rewrite !(sep_sem_at H) !(pure_sem_at H).
    iIntros "(%B & #E & #F)". iFrame "E F". iPureIntro. lia.
  Qed.
  Next Obligation.
    move=> 𝔄 κ ty κ0 [[[[[l x0] ξi] d'] g'] idx] d g tid ξ R Hin. rewrite /=.
    rewrite !bor_sep_sem !pure_fml_sem !or_fml_sem !basically_dead_fml_sem
      ?alive_fml_sem ?cmapstoany_fml_sem
      !vo_fml_sem !idx_bor_tok_fml_sem.
    iIntros "#LFT #Incl1 (%Hle & #Pers & #Bor) #Rk #Rg".
    iAssert (κ0 ⊑ κ)%I as "#Inκ".
    { iApply (guard_trans with "Incl1 []"). iApply llftl_intersect_incl_l. }
    iAssert (κ0 ⊑ ty_lft ty)%I as "#Inty".
    { iApply (guard_trans with "Incl1 []"). iApply llftl_intersect_incl_r. }
    iDestruct "Pers" as "[bd|InnerPers]".
    { (* The lifetime is already dead, so [@[κ0]] is absurd. *)
      iDestruct "bd" as (κ') "[#Incl0 #†κ']".
      iDestruct (dincl_sem with "Incl0") as "#Incl'". iApply guard_false.
      iApply (guard_trans with "Rk []").
      iApply (guard_trans with "[] []");
        [iApply (guard_trans with "Inκ Incl'")|].
      iApply guard_intro. iIntros "!> Alive".
      iExFalso. iApply (llftl_not_own_end with "Alive †κ'"). }
    (* Open the borrow through the guard and pin its witnesses. *)
    iAssert (R &&{Wguard}&&>
      .VO[PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ξi] x0 (d', g'))%I as "#Rvo".
    { iApply (guard_trans with "Rg []"). iApply guard_intro.
      iIntros "!> (A & B & (C & D & E) & F & G)". iFrame "C". iIntros "C".
      iFrame. }
    iAssert (R &&{Wguard}&&> idx_bor_tok idx)%I as "#Rtok".
    { iApply (guard_trans with "Rg []"). iApply guard_intro.
      iIntros "!> (A & B & (C & D & E) & F & G)". iFrame "D". iIntros "D".
      iFrame. }
    iAssert (R &&{Wguard}&&> @[κ])%I as "#Rκ".
    { iApply (guard_trans with "Rk Inκ"). }
    iDestruct (idxbor_fml_sem_1 with "Bor") as "#Bor1".
    iDestruct (llftl_idx_bor_guard' κ idx _ R with "LFT Bor1 Rκ Rtok")
      as "#Ginner".
    iDestruct (guard_rhs_sep_r with "Ginner") as "#Ginner2".
    iDestruct (guard_rhs_iff (uniq_body_fml_sem ty x0 ξi tid l) with "Ginner2")
      as "#Ginner3".
    iDestruct (guard_exist_eq x0 d' g' _ _ _
      (uniq_body_at_agree ty x0 ξi d' g' tid l) with "Rvo Ginner3") as "#Gin".
    rewrite elem_of_cons in Hin. destruct Hin as [->|Hin].
    - (* the unique reference's own prophecy variable *)
      iApply (guard_and (P:=R) with "Rvo Gin"). iIntros "And".
      iApply (proph_ctrl_and_value_obs_entails_proph_tok
        (PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ξi) x0 (vπ x0) (d', g')).
      iSplit; [by iDestruct "And" as "[_ [$ _]]"|by iDestruct "And" as "[$ _]"].
    - (* a prophecy variable of the borrowed type *)
      iApply (ty_guard_proph _ ty κ0 x0 d' g' tid ξ R Hin
        with "LFT Inty InnerPers Rk").
      iDestruct (guard_rhs_sep_r with "Gin") as "#Gin2".
      iApply (guard_rhs_sep_l with "Gin2").
  Qed.
  Next Obligation.
    move=> 𝔄 κ ty sem H [[[[[l x0] ξi] d'] g'] idx] d g tid.
    have ? := guard_fml_pers_at H. have ? := idxbor_fml_pers_at H.
    have ? := ty_gho_pers_pers_at ty sem H.
    have ? := basically_dead_pers_at H. have ? := or_pers_at H.
    have ? := pure_pers_at H. have ? := sep_pers_at H. exact _.
  Qed.
  Next Obligation.
    move=> 𝔄 κ ty [[[[[l x0] ξi] d'] g'] idx] d g tid. rewrite /=.
    rewrite !bor_sep_sem !pure_fml_sem !or_fml_sem !basically_dead_fml_sem
      ?alive_fml_sem ?cmapstoany_fml_sem
      !vo_fml_sem !idx_bor_tok_fml_sem.
    iIntros "(_ & %B & (_ & _ & #C3) & _ & #E)".
    iFrame "E C3". iPureIntro. lia.
  Qed.
End uniq_bor.

Notation "&uniq{ κ }" := (uniq_bor κ) (format "&uniq{ κ }") : lrust_type_scope.

Section uniq_bor_sem.
  Context `{!typeG FML Σ}.

  (** Unfolding [&uniq{κ}]'s ghost assertion *)
  Lemma uniq_bor_gho {𝔄} κ (ty: type 𝔄) l x0 ξi d' g' idx d g tid :
    ty_gho (uniq_bor κ ty) (l, x0, ξi, d', g', idx) d g tid ⊣⊢
      dincl κ (ty_lft ty) ∗ ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗
      uniq_body ty x0 ξi d' g' idx κ tid l ∗
      dguard (alive_fml κ) (cmapstoany_fml l) ∗
      (basically_dead κ ∨ ty_gho_pers ty x0 d' g' tid).
  Proof.
    rewrite /ty_gho /uniq_body /uniq_body_pers_component /= !bor_sep_sem
      !pure_fml_sem !or_fml_sem !basically_dead_fml_sem incl_fml_sem
      !vo_fml_sem !idx_bor_tok_fml_sem //.
  Qed.
  Lemma uniq_bor_gho_pers {𝔄} κ (ty: type 𝔄) l x0 ξi d' g' idx d g tid :
    ty_gho_pers (uniq_bor κ ty) (l, x0, ξi, d', g', idx) d g tid ⊣⊢
      ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗
      (basically_dead κ ∨ ty_gho_pers ty x0 d' g' tid) ∗
      uniq_body_pers_component ty x0 ξi d' g' idx κ tid l.
  Proof.
    rewrite /ty_gho_pers /uniq_body_pers_component /= !bor_sep_sem
      !pure_fml_sem !or_fml_sem !basically_dead_fml_sem //.
  Qed.

  Global Instance uniq_bor_ne {𝔄} κ : NonExpansive (@uniq_bor _ _ _ 𝔄 κ).
  Proof.
    move=> n ty ty' [Hsz Hlfts HE Hgho Hpers Hphys]. split=>/=.
    - done.
    - by rewrite Hlfts.
    - by rewrite HE /ty_outlives_E Hlfts.
    - move=> [[[[[l x0] ξi] d'] g'] idx] d g tid /=.
      have Hpf : ty_phys ty = ty_phys ty'.
      { fun_ext=> ?. fun_ext=> ?. apply Hphys. }
      rewrite /uniq_body_fmlx /uniq_body_fml /uniq_body_at_fml Hlfts Hpf.
      setoid_rewrite Hgho. by rewrite Hpers.
    - move=> [[[[[l x0] ξi] d'] g'] idx] d g tid /=.
      have Hpf : ty_phys ty = ty_phys ty'.
      { fun_ext=> ?. fun_ext=> ?. apply Hphys. }
      rewrite /uniq_body_fml /uniq_body_at_fml Hpf.
      setoid_rewrite Hgho. by rewrite Hpers.
    - by move=> [[[[[??]?]?]?]?] ?.
  Qed.

  Lemma uniq_stack_okay {𝔄} κ (ty: type 𝔄) : StackOkay (&uniq{κ} ty).
  Proof. by move=> [[[[[??]?]?]?]?] ?. Qed.

  Global Instance uniq_just_loc {𝔄} κ (ty: type 𝔄) : JustLoc (&uniq{κ} ty).
  Proof. iIntros ([[[[[l x0] ξi] d'] g'] idx] d g tid) "_". by iExists l.1. Qed.



  Global Instance uniq_sync {𝔄} κ (ty: type 𝔄) : Sync ty → Sync (&uniq{κ} ty).
  Proof.
    move=> SyncTy tid tid' [[[[[l x0] ξi] d'] g'] idx] d g.
    have Hp : ∀ y, ty_phys ty y tid = ty_phys ty y tid'.
    { move=> y. by have [? _] := SyncTy tid tid' y 0 0. }
    have [_ [_ Hps]] := SyncTy tid tid' x0 d' g'.
    (* the borrowed body differs only in the thread id, and [Sync] is now an
      equation of formulas, so the indexed borrow of it is too *)
    have Hbody : uniq_body_fml ty x0 ξi tid l ≡ uniq_body_fml ty x0 ξi tid' l.
    { apply uniq_body_fml_tid; [|done]=> y e h.
      by have [_ [? _]] := SyncTy tid tid' y e h. }
    split; [done|].
    split=>/=; rewrite /uniq_body_fmlx Hbody Hps //.
  Qed.

  Lemma uniq_resolve {𝔄} E L κ (ty: type 𝔄) :
    lctx_lft_alive E L κ →
    resolve E L (&uniq{κ} ty) (λ x π, snd (vπ x π) = fst (vπ x π)).
  Proof.
    move=> Alv γ q F [[[[[l x0] ξi] d'] g'] idx] d g tid ?.
    iIntros "#LFT #PROPH #UNIQ #E tok gho". rewrite uniq_bor_gho.
    iDestruct "gho" as "(#In0 & %Hle & uniq & _ & _)".
    iDestruct (dincl_sem with "In0") as "#In". iIntros "W".
    iMod (resolve_uniq_body with "LFT PROPH UNIQ In E tok uniq W")
      as "[$ (#Obs & $ & _)]"; [done|done|].
    iModIntro. iApply proph_obs_eq; [|done]=> ? /=. by f_equal.
  Qed.

  (** Subtyping of a unique reference.

    The extra premise is the price of the model (see [typing/inst.v]): the
    borrowed body is altered *inside* a borrow, and the borrow's alteration
    [st_iff] is read at every interpretation, not only at the candidates -
    that is what takes [Deriv], and with it [Jsem], out of [idx_bor].  An
    [eqtype] gives the equivalence at the candidates only, since its proof
    for a type containing a judgment goes through [Deriv_map].  The premise
    is discharged by [equiv_ghox_any] whenever the two ghost assertions are
    equal as formulas, which covers every type former whose [ty_ghox] is
    built definitionally. *)
  Lemma uniq_subtype {𝔄} E L κ κ' (ty ty': type 𝔄) :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' idₛ idₛ →
    (⊢ □ ∀ sem (_ : alt_any sem), ∀ y e h t,
        sem (ty.(ty_ghox) y e h t) ∗-∗ sem (ty'.(ty_ghox) y e h t)) →
    subtype E L (&uniq{κ} ty) (&uniq{κ'} ty') idₛ.
  Proof.
    move=> In Eqt HAny. rewrite -eqtype_id_unfold in Eqt. iIntros "L".
    iDestruct (Eqt with "L") as "#Eqt". iDestruct (In with "L") as "#In".
    iIntros "!> #E". iSplit; [done|].
    iDestruct ("Eqt" with "E")
      as (?) "[[#Lfts1 #Lfts2][#EqOwn [#EqPers %EqPhys]]]".
    iSpecialize ("In" with "E"). iSplit; [by iApply dincl_intersect_mono|].
    (* the two ghost components, at every candidate interpretation *)
    have HPhys : ∀ y t, ty_phys ty y t = ty_phys ty' y t
      by move=> ??; apply EqPhys.
    iAssert (□ ∀ t sem' (_ : alt_any sem'), ∀ y e h,
      sem' (ty.(ty_ghox) y e h t) ∗-∗ sem' (ty'.(ty_ghox) y e h t))%I
      as "#HGho".
    { iDestruct HAny as "#H". iIntros "!>" (t sem' Hs y e h).
      iApply ("H" $! sem' Hs). }
    have HDead : ∀ sem' (Hs : alt_sem sem'),
      dincl κ' κ -∗
      sem' (basically_dead_fml κ) -∗ sem' (basically_dead_fml κ').
    { move=> sem' Hs. have ? := dead_pers_at Hs.
      rewrite /basically_dead_fml !(ex_sem_at Hs).
      iIntros "#In0 (%κ'' & D)". rewrite !(sep_sem_at Hs).
      iDestruct "D" as "[#I #Dd]". iExists κ''. rewrite (sep_sem_at Hs).
      iFrame "Dd". iApply (incl_fml_mono_at Hs with "In0 [] I").
      iApply dincl_refl. }
    iSplit.
    { iIntros "!>" (sem Hsem [[[[[l x0] ξi] d'] g'] idx] d g tid).
      have ? := guard_fml_pers_at Hsem. have ? := idxbor_fml_pers_at Hsem.
      have ? := ty_gho_pers_pers_at ty sem Hsem.
      have ? := ty_gho_pers_pers_at ty' sem Hsem.
      have ? := basically_dead_pers_at Hsem.
      have ? := or_pers_at Hsem.
      iDestruct (dincl_at Hsem with "In") as "#In0".
      rewrite /= /uniq_body_fmlx !(sep_sem_at Hsem) !(pure_sem_at Hsem)
        !(or_sem_at Hsem).
      iIntros "(#Incl & %Hle & (Vo & Tok & #Bor) & #PtBase & #Pers)".
      iAssert (sem (basically_dead_fml κ') ∨
        sem (ty'.(ty_gho_persx) x0 d' g' tid))%I as "#Pers'".
      { iDestruct "Pers" as "[Dead|P]".
        - iLeft. iApply (HDead sem Hsem with "In Dead").
        - iRight. iDestruct ("EqPers" $! sem Hsem x0 d' g' tid) as "[F _]".
          by iApply "F". }
      iAssert (sem (idxbor_fml κ' idx (uniq_body_fml ty' x0 ξi tid l)))
        as "#Bor'".
      { iDestruct ("HGho" $! tid) as "#HGho'".
        iApply (incl_uniq_body_pers_component_at Hsem ty ty' x0 ξi idx κ κ'
          tid l (λ y, HPhys y tid) with "HGho' In Bor"). }
      iAssert (sem (incl_fml κ' (ty_lft ty'))) as "#Incl2".
      { iApply (incl_fml_mono_at Hsem with "In Lfts1 Incl"). }
      iAssert (sem (guard_fml (alive_fml κ') (cmapstoany_fml l))) as "#PtBase'".
      { iApply (dguard_trans_at Hsem with "In0 PtBase"). }
      iSplitL "Vo Tok".
      - iFrame "Pers' Incl2 PtBase' Vo Tok Bor'". iPureIntro. lia.
      - iIntros "(_ & _ & (Vo & Tok & _) & _ & _)".
        iFrame "Pers Incl PtBase Vo Tok Bor". iPureIntro. lia. }
    iSplit.
    { iIntros "!>" (sem Hsem [[[[[l x0] ξi] d'] g'] idx] d g tid).
      have ? := guard_fml_pers_at Hsem. have ? := idxbor_fml_pers_at Hsem.
      have ? := ty_gho_pers_pers_at ty sem Hsem.
      have ? := ty_gho_pers_pers_at ty' sem Hsem.
      have ? := basically_dead_pers_at Hsem.
      have ? := or_pers_at Hsem.
      iDestruct (dincl_at Hsem with "In") as "#In0".
      rewrite /= !(sep_sem_at Hsem) !(pure_sem_at Hsem) !(or_sem_at Hsem).
      iIntros "(%Hle & #Pers & #Bor)".
      iSplit; [iPureIntro; lia|]. iSplit.
      - iDestruct "Pers" as "[Dead|P]".
        + iLeft. iApply (HDead sem Hsem with "In Dead").
        + iRight. iDestruct ("EqPers" $! sem Hsem x0 d' g' tid) as "[F _]".
          by iApply "F".
      - iDestruct ("HGho" $! tid) as "#HGho'".
        iApply (incl_uniq_body_pers_component_at Hsem ty ty' x0 ξi idx κ κ'
          tid l (λ y, HPhys y tid) with "HGho' In Bor"). }
    { iPureIntro. by move=> [[[[[??]?]?]?]?] ?. }
  Qed.

  Lemma uniq_eqtype {𝔄} E L κ κ' (ty ty': type 𝔄) :
    lctx_lft_eq E L κ κ' → eqtype E L ty ty' idₛ idₛ →
    (⊢ □ ∀ sem (_ : alt_any sem), ∀ y e h t,
        sem (ty.(ty_ghox) y e h t) ∗-∗ sem (ty'.(ty_ghox) y e h t)) →
    eqtype E L (&uniq{κ} ty) (&uniq{κ} ty') idₛ idₛ.
  Proof.
    move=> [??][??] HAny.
    have HAny' : ⊢ □ ∀ sem (_ : alt_any sem), ∀ y e h t,
      sem (ty'.(ty_ghox) y e h t) ∗-∗ sem (ty.(ty_ghox) y e h t).
    { iDestruct HAny as "#H". iIntros "!>" (sem Hs y e h t).
      iDestruct ("H" $! sem Hs y e h t) as "[F B]".
      iSplit; iIntros "x"; [by iApply "B"|by iApply "F"]. }
    by split; apply uniq_subtype.
  Qed.

  (** Accessors on a unique reference's refinement *)
  Definition uniq_bor_loc {𝔄} (m: ~~ (uniq_borₛ 𝔄)) : cloc :=
    match m with (l, x0, ξi, d', g', idx) => l end.
  Definition uniq_bor_current {𝔄} (m: ~~ (uniq_borₛ 𝔄)) : ~~ 𝔄 :=
    match m with (l, x0, ξi, d', g', idx) => x0 end.
  Definition uniq_bor_future {𝔄} (m: ~~ (uniq_borₛ 𝔄)) (π : proph_asn) : 𝔄 :=
    (vπ m π).2.
  Definition uniq_bor_ξi {𝔄} (m: ~~ (uniq_borₛ 𝔄)) : positive :=
    match m with (l, x0, ξi, d', g', idx) => ξi end.
  Definition uniq_bor_update {𝔄} (m: ~~ (uniq_borₛ 𝔄)) (new: ~~ 𝔄)
    (m': ~~ (uniq_borₛ 𝔄)) :=
    match m, m' with
      (l, x0, ξi, _, _, _), (l', x0', ξi', _, _, _) =>
        l = l' ∧ x0' = new ∧ ξi' = ξi
    end.

  (** Writing through a unique reference.

    The original takes a [Timeless G] with [G &&{↑NllftG}&&> llctx_interp L]
    and halves it with [frac_split_guard_in_half]; here the halves are
    fractions of an [Ltok], and the half handed to the client is named as a
    formula, since the Points-To Cell Logic parks it in its write bank. *)
  Lemma write_uniq {𝔄} E L κ (ty: type 𝔄) :
    lctx_lft_alive E L κ →
    typed_write E L (&uniq{κ} ty) ty (&uniq{κ} ty) ty uniq_bor_current
      uniq_bor_update.
  Proof.
    move=> Alv. split; [done|].
    move=> [[[[[l x0] ξi] d'] g'] idx] d v tid γ q.
    iIntros "#LFT #UNIQ #E [#key f] [gho %Phys]". rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Hle & (ξVo & Tok & #Bor) & #PtBase & #Pers)".
    iIntros "W".
    iDestruct (Ltok_acc (W:=alerus_wsat) with "[$key $f] W") as "[L →W]".
    iDestruct (Alv with "L E") as "#Lkg".
    iDestruct ("→W" with "L") as "[W [_ f]]".
    iAssert (frac_tok γ (q/2) &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "[] Lkg"). iApply (Ltok_guard_frac with "key"). }
    iAssert (bor_sem (gsrc_fml (GFrac γ (q/2))) &&{Wguard}&&> @[κ])%I as "#Gκ'".
    { iApply (guard_lhs_iff (gsrc_fml_sem (GFrac γ (q/2)))). iApply "Gκ". }
    iDestruct (Ltok_split_1 with "[$key $f]") as "[[_ fa] [_ fb]]".
    iDestruct (idxbor_fml_sem_1 with "Bor") as "#Bor1".
    iDestruct (llftl_bor_idx_acc_guarded ⊤ (gsrc_fml (GFrac γ (q/2))) κ idx
      with "LFT Bor1 Tok Gκ' [fa]") as "A";
      [by iApply (gsrc_fml_sem_2 (s := GFrac γ (q/2)))|].
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "A") as "A'";
      [done|].
    iMod ("A'" with "W") as "[W [P Gback]]".
    iEval (rewrite uniq_body_fml_sem) in "P".
    iDestruct "P" as (x1 d1 g1) "(ξPc & gho & pt)".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<- Heq]. inversion Heq.
    subst d1 g1. destruct d as [|d]; [lia|].
    iModIntro. iFrame "W". iExists l, d, (gsrc_fml (GFrac γ (q/2))).
    inversion Phys as [Eqv]. iSplit; [done|]. iSplit; [done|].
    iSplitL "pt gho".
    { iExists (ty_phys ty x0 tid). iFrame "pt". rewrite /ty_own.
      iSplit; [|done].
      by iDestruct (ty_gho_depth_mono ty d' g' d (S d) x0 tid with "gho")
        as "[$ _]"; [lia|lia]. }
    iSplitL "fb"; [by iApply (gsrc_fml_sem_2 (s := GFrac γ (q/2)))|].
    iDestruct (dguard_alive_sem with "PtBase") as "#PtBase'".
    iSplit; [iApply (guard_trans with "Gκ' [PtBase']")|].
    { iApply (guard_rhs_iff (cmapstoany_fml_sem l)). iApply "PtBase'". }
    iIntros (y db') "pt fb W".
    iDestruct "pt" as (lv) "[pt [gho %phys]]". subst lv.
    iDestruct (ty_gho_pers_impl with "gho") as "#ghopers".
    iMod (uniq_update (PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ξi) y (vπ y)
      (db', S db') with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; [set_solver|].
    iDestruct ("Gback" with "[pt gho ξPc]") as "B".
    { iApply (uniq_body_fml_sem_2 with "ξPc gho pt"). }
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "B") as "B'";
      [done|].
    iMod ("B'" with "W") as "[W [Tok fa]]".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ (q/2)) with "fa") as "fa".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ (q/2)) with "fb") as "fb".
    iModIntro. iFrame "W". iExists (l, y, ξi, db', S db', idx).
    iDestruct (Ltok_split_2 with "[$key $fa] [$key $fb]") as "$".
    iSplit; [done|]. rewrite /ty_own uniq_bor_gho.
    rewrite (uniq_body_pers_component_irrel ty x0 y ξi d' g' db' (S db') idx κ
      tid l (proof_irrel _ _)).
    rewrite (proof_irrel (prval_to_inh (vπ x0)) (prval_to_inh (vπ y))).
    iSplitL; [|done]. rewrite /uniq_body.
    iSplitR; [iApply "Incl"|]. iSplitR; [iPureIntro; lia|].
    iSplitL "ξVo Tok"; [iFrame "ξVo Tok Bor"|].
    iSplitR; [iApply "PtBase"|]. iRight. iApply "ghopers".
  Qed.

  (** Reading a [Copy] type out of a unique reference.

    The original takes [£(d+1)] and spends it on
    [guards_extract_persistent_later] to get the inner ghost state out from
    under a [▷]; there is no later here, so opening the guard once is
    enough.  The guard source is a formula, as everywhere: the value
    observer, the share and the borrow token. *)
  Lemma read_uniq {𝔄} E L κ (ty: type 𝔄) :
    Copy ty → lctx_lft_alive E L κ →
    typed_read E L (&uniq{κ} ty) ty (&uniq{κ} ty) uniq_bor_current (=).
  Proof.
    move=> Cpy Alv [[[[[l x0] ξi] d'] g'] idx] d v tid γ q.
    iIntros "#LFT #E [#key f] [gho %Phys] W". rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Hle & (ξVo & Tok & #Bor) & #PtBase & #Pers)".
    set ξ := PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ξi.
    set Hx := (vo_fml ξ x0 (d', g') ∗ gsrc_fml (GFrac γ q) ∗
      idx_bor_tok_fml idx)%FML.
    have HxS : bor_sem Hx ⊣⊢
      .VO[ξ] x0 (d', g') ∗ frac_tok γ q ∗ idx_bor_tok idx.
    { rewrite /Hx !bor_sep_sem vo_fml_sem idx_bor_tok_fml_sem
        (gsrc_fml_sem (GFrac γ q)) /= //. }
    iDestruct (Ltok_acc (W:=alerus_wsat) with "[$key $f] W") as "[L →W]".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct ("→W" with "L") as "[W [_ f]]".
    iAssert (frac_tok γ q &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "[] Alv"). iApply (Ltok_guard_frac with "key"). }
    iAssert (bor_sem Hx &&{Wguard}&&> @[κ])%I as "#HGκ".
    { iApply (guard_trans with "[] Gκ"). iApply (guard_lhs_iff HxS).
      iApply guard_intro. iIntros "!> (A & B & C)". iFrame "B".
      iIntros "B". iFrame. }
    iAssert (bor_sem Hx &&{Wguard}&&> idx_bor_tok idx)%I as "#HGtok".
    { iApply (guard_lhs_iff HxS). iApply guard_intro.
      iIntros "!> (A & B & C)". iFrame "C". iIntros "C". iFrame. }
    iAssert (bor_sem Hx &&{Wguard}&&> .VO[ξ] x0 (d', g'))%I as "#HGvo".
    { iApply (guard_lhs_iff HxS). iApply guard_intro.
      iIntros "!> (A & B & C)". iFrame "A". iIntros "A". iFrame. }
    iDestruct (idxbor_fml_sem_1 with "Bor") as "#Bor1".
    iDestruct (llftl_idx_bor_guard' κ idx _ (bor_sem Hx)
      with "LFT Bor1 HGκ HGtok") as "#Ginner".
    iDestruct (guard_rhs_sep_r with "Ginner") as "#Ginner2".
    iDestruct (guard_rhs_iff (uniq_body_fml_sem ty x0 ξi tid l) with "Ginner2")
      as "#Ginner3".
    iDestruct (guard_exist_eq x0 d' g' _ _ _
      (uniq_body_at_agree ty x0 ξi d' g' tid l) with "HGvo Ginner3") as "#Gin".
    iDestruct (guard_rhs_sep_r with "Gin") as "#Gin2".
    iDestruct (guard_rhs_sep_l with "Gin2") as "#Ggho".
    iDestruct (guard_rhs_sep_r with "Gin2") as "#Gpt".
    iAssert (bor_sem Hx) with "[ξVo f Tok]" as "Hx".
    { iApply (bi.equiv_entails_1_2 _ _ HxS). iFrame. }
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "Ggho Hx Wg") as "[#T →Wg]".
    iDestruct ("→Wg" with "T") as "[Wg Hx]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iDestruct (copy_concrete with "T") as "%Conc".
    iModIntro. iFrame "W".
    iExists l, (to_concrete (ty_phys ty x0 tid)), (ty_phys ty x0 tid), Hx.
    inversion Phys. iSplit; [done|].
    iSplit; [iPureIntro; apply length_to_concrete|].
    iFrame "Hx". iSplit.
    { iApply (guard_cloc_combine with "[] []").
      - iDestruct (dguard_alive_sem with "PtBase") as "#PtBase'".
        iApply (guard_trans with "HGκ [PtBase']").
        iApply (guard_rhs_iff (cmapstoany_fml_sem l)). iApply "PtBase'".
      - iApply (guard_rhs_iff with "Gpt").
        rewrite -heap_complete_mapsto_fancy_fmap_eq fmap_to_concrete //. }
    iSplitR.
    { iIntros (l₁ c₁) "↦". rewrite -heap_complete_mapsto_fancy_fmap_eq.
      rewrite (fmap_to_concrete _ Conc). by iFrame. }
    iSplit. { iPureIntro=> _. rewrite fmap_to_concrete //. }
    iSplitR.
    { iSplit; [|done].
      iDestruct (ty_gho_depth_mono ty d' g' d d x0 tid with "T") as "[$ _]";
        lia. }
    iIntros "Hx W". iEval (rewrite HxS) in "Hx".
    iDestruct "Hx" as "(ξVo & f & Tok)".
    iModIntro. iFrame "W". iExists (l, x0, ξi, d', g', idx).
    iSplit; [done|]. iFrame "key f". rewrite /ty_own uniq_bor_gho.
    iSplitL "ξVo Tok"; [|done]. rewrite /uniq_body.
    iSplitR; [iApply "Incl"|]. iSplitR; [iPureIntro; lia|].
    iSplitL "ξVo Tok"; [iFrame "ξVo Tok Bor"|].
    iSplitR; [iApply "PtBase"|]. iApply "Pers".
  Qed.
End uniq_bor_sem.

Global Hint Rewrite @uniq_bor_gho @uniq_bor_gho_pers : fml_sem.

Section uniq_bor_typing.
  Context `{!typeG FML Σ}.


  (** [&uniq{static}] is [Send].

    The original's [⧖ d0] and its [|={…}▷=>^d] go with the time receipts.
    Changing the borrow's contents to the new thread id needs a way back,
    which at [static] is vacuous: [[†static]] is [False]. *)
  Global Instance uniq_send_static {𝔄} (ty: type 𝔄) :
    Send ty → Send (&uniq{static} ty).
  Proof.
    move=> [Hphys Hgho]. split.
    { move=> ?? [[[[[??]?]?]?]?] [[[[[??]?]?]?]?] Ha. by inversion Ha. }
    move=> tid tid' [[[[[l x0] ξi] d'] g'] idx] d g G κs.
    iIntros "#LFT #UNIQ lfts #gs K gho W". rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Hle & (ξVo & Tok & #Bor) & #PtBase & #Pers)".
    iDestruct (idxbor_fml_to_full with "Bor Tok") as "Bor2".
    iDestruct (llftl_bor_acc NalerusE _ static with "LFT Bor2 []") as "A";
      [iApply llftl_tok_unit|].
    iDestruct (fupdw_incl_mask (W:=alerus_wsat_core) (E':=NalerusE) with "A")
      as "A'"; [done|].
    iMod ("A'" with "W") as "[W [Inner Back]]".
    iEval (rewrite uniq_body_fml_sem) in "Inner".
    iDestruct "Inner" as (x1 d1 g1) "(ξPc & Gho & Pt)".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<- Heq]. inversion Heq.
    subst d1 g1.
    iMod (Hgho tid tid' x0 d' g' G κs with "LFT UNIQ lfts gs K Gho W")
      as "(W & %x' & %off & gho & %Habs & lfts & K)".
    iDestruct (ty_gho_pers_impl with "gho") as "#ghopers".
    iMod (uniq_update (PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ξi) x' (vπ x')
      (d' + off, g') with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; [solve_ndisj|].
    rewrite (proof_irrel (prval_to_inh (vπ x0)) (prval_to_inh (vπ x'))).
    iDestruct ("Back" $! (uniq_body_fml ty x' ξi tid' l)
      with "[] [ξPc gho Pt]") as "B".
    { iIntros "[_ †]". iExFalso. by iApply llftl_end_unit. }
    { iApply (uniq_body_fml_sem_2 with "ξPc gho [Pt]").
      by rewrite -(Hphys tid tid' x0 x' (eq_sym Habs)). }
    iDestruct (bupdw_incl (W:=alerus_wsat_core) with "B") as "B'".
    iMod ("B'" with "W") as "[W [Bor3 _]]".
    rewrite idxbor_fml_of_bor. iDestruct "Bor3" as (idx2) "[#Bor3 Tok3]".
    iModIntro. iFrame "W". iExists (l, x', ξi, d' + off, g', idx2), off.
    iFrame "lfts K". rewrite uniq_bor_gho.
    iSplitL.
    - rewrite /uniq_body /uniq_body_pers_component.
      iSplitR; [iApply "Incl"|]. iSplitR; [iPureIntro; lia|].
      iSplitL "ξVo Tok3"; [by iFrame "ξVo Tok3 Bor3"|].
      iSplitR; [iApply "PtBase"|]. iRight. iApply "ghopers".
    - iPureIntro. by rewrite /= Habs.
  Qed.

  Lemma tctx_uniq_mod_ty_out {𝔄 𝔅 ℭl} κ (f : 𝔄 →ₛ 𝔅) (fⁱ: 𝔅 →ₛ 𝔄) ty
      (T: tctx ℭl) p E L `{!Isoₛ f fⁱ} :
    lctx_lft_alive E L κ →
    tctx_incl E L (p ◁ &uniq{κ} (<{f;fⁱ}> ty) +:: T) (p ◁ &uniq{κ} ty +:: T)
      (λ post '(bor -:: cl), λ mask π,
        ∀ bor', uniq_bor_loc bor' = uniq_bor_loc bor →
        uniq_bor_current bor' = fⁱ ~~$ₛ (uniq_bor_current bor) →
        uniq_bor_future bor' π = fⁱ $ₛ (uniq_bor_future bor π) →
        post (bor' -:: cl) mask π).
  Proof.
    move=> Alv. split.
    { move=> ?? Eq [[??]?] ??. do 2 apply forall_proper=> ?.
      split=> ???; apply Eq; auto. }
    iIntros (γ q tid [x y] mask post) "#LFT #PROPH #UNIQ #E tok [p T] Obs W".
    destruct x as [[[[[l x0] ξi] d'] g'] ξidx].
    iDestruct "p" as (v d) "[%Hp [gho %Hphys]]". rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Hle & UniqBody & #PtBase & #Pers)".
    iDestruct (Ltok_acc (W:=alerus_wsat) with "tok W") as "[L →W]".
    iDestruct (Alv with "L E") as "#Lkg".
    iDestruct ("→W" with "L") as "[W [#key f]]".
    iAssert (frac_tok γ q &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "[] Lkg"). iApply (Ltok_guard_frac with "key"). }
    have Hmask : (↑Nllft ∪ ↑prophN ∪ ↑uniqN : coPset) ⊆ ⊤ by set_solver.
    iMod (uniq_body_transform (<{f;fⁱ}> ty) ty x0 (fⁱ ~~$ₛ x0) d' g' ξi ξidx κ
      tid l l ⊤ γ L q f _ Hmask
      with "LFT PROPH UNIQ [] Gκ [$key $f] UniqBody W")
      as "[W (%ζi & %ζidx & #Obs2 & UniqBody & tok)]".
    { iIntros "[gho pt]". rewrite mod_ty_gho /=. iModIntro. iFrame "gho pt".
      iIntros (z e h) "[gho pt]". iModIntro. iExists e, h.
      rewrite mod_ty_gho /=
        !(semi_iso' (syn_type_morphism_fn f) (syn_type_morphism_fn fⁱ)).
      iFrame. }
    iCombine "Obs Obs2" as "#Obs3".
    iModIntro. iFrame "W".
    iExists ((l, (fⁱ ~~$ₛ x0), ζi, d', g', ζidx) -:: y).
    iFrame "tok T". iSplitL "UniqBody".
    { iExists v, d. iSplit; [done|]. rewrite /ty_own uniq_bor_gho.
      iSplitL; [|by rewrite /= -Hphys].
      iSplitR.
      { iApply "Incl". }
      iSplitR; [iPureIntro; lia|]. iFrame "UniqBody".
      iSplitR; [iApply "PtBase"|].
      iDestruct "Pers" as "[Dead|P]"; [by iLeft|iRight].
      iApply "P". }
    iApply (proph_obs_impl with "Obs3")=> π [Ha Hb]. apply Ha; [done|done|].
    rewrite /uniq_bor_future /=. by rewrite Hb semi_iso'.
  Qed.

  Lemma tctx_uniq_eqtype {𝔄 𝔅 ℭl} κ (f: 𝔄 →ₛ 𝔅) (fⁱ: 𝔅 →ₛ 𝔄) ty ty'
      (T: tctx ℭl) p E L :
    eqtype E L ty ty' f fⁱ → Isoₛ f fⁱ → lctx_lft_alive E L κ →
    tctx_incl E L (p ◁ &uniq{κ} ty +:: T) (p ◁ &uniq{κ} ty' +:: T)
      (λ post '(bor -:: cl), λ mask π,
        ∀ bor', uniq_bor_loc bor' = uniq_bor_loc bor →
        uniq_bor_current bor' = f ~~$ₛ (uniq_bor_current bor) →
        uniq_bor_future bor' π = f $ₛ (uniq_bor_future bor π) →
        post (bor' -:: cl) mask π).
  Proof.
    move=> Heqtype Hiso Alv. split.
    { move=> ?? Eq [[??]?] ??. do 2 apply forall_proper=> ?.
      split=> ???; apply Eq; auto. }
    iIntros (γ q tid [x y] mask post) "#LFT #PROPH #UNIQ #E tok [p T] Obs W".
    rewrite -eqtype_unfold in Heqtype.
    destruct x as [[[[[l x0] ξi] d'] g'] ξidx].
    iDestruct "p" as (v d) "[%Hp [gho %Hphys]]". rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Hle & UniqBody & #PtBase & #Pers)".
    iDestruct (Ltok_acc (W:=alerus_wsat) with "tok W") as "[L →W]".
    iDestruct (Heqtype with "L E")
      as "(%Hsz & #[Hl1 Hl2] & #EqGho & #EqPers & %EqPhys)".
    iDestruct (Alv with "L E") as "#Lkg".
    iDestruct ("→W" with "L") as "[W [#key f]]".
    iAssert (frac_tok γ q &&{Wguard}&&> @[κ])%I as "#Gκ".
    { iApply (guard_trans with "[] Lkg"). iApply (Ltok_guard_frac with "key"). }
    have Hmask : (↑Nllft ∪ ↑prophN ∪ ↑uniqN : coPset) ⊆ ⊤ by set_solver.
    iMod (uniq_body_transform ty ty' x0 (f ~~$ₛ x0) d' g' ξi ξidx κ tid l l ⊤
      γ L q fⁱ _ Hmask with "LFT PROPH UNIQ [] Gκ [$key $f] UniqBody W")
      as "[W (%ζi & %ζidx & #Obs2 & UniqBody & tok)]".
    { iIntros "[gho pt]". iModIntro.
      iDestruct ("EqGho" $! _ alt_here x0 d' g' tid) as "[G1 _]".
      iDestruct ("G1" with "gho") as "$". rewrite EqPhys. iFrame "pt".
      iIntros (z e h) "[gho pt]". iModIntro. iExists e, h.
      rewrite EqPhys
        (semi_iso' (syn_type_morphism_fn fⁱ) (syn_type_morphism_fn f)).
      iFrame "pt". iDestruct ("EqGho" $! _ alt_here (fⁱ ~~$ₛ z) e h tid) as "[_ G2]".
      iApply "G2".
      rewrite (semi_iso' (syn_type_morphism_fn fⁱ) (syn_type_morphism_fn f)).
      iFrame "gho". }
    iCombine "Obs Obs2" as "#Obs3".
    iModIntro. iFrame "W".
    iExists ((l, (f ~~$ₛ x0), ζi, d', g', ζidx) -:: y).
    iFrame "tok T". iSplitL "UniqBody".
    { iExists v, d. iSplit; [done|]. rewrite /ty_own uniq_bor_gho.
      iSplitL; [|by rewrite /= -Hphys].
      iSplitR; [iApply (dincl_trans with "Incl Hl1")|].
      iSplitR; [iPureIntro; lia|]. iFrame "UniqBody".
      iSplitR; [iApply "PtBase"|].
      iDestruct "Pers" as "[Dead|P]"; [by iLeft|iRight].
      by iDestruct ("EqPers" $! _ alt_here x0 d' g' tid) as "[G _]"; iApply "G". }
    iApply (proph_obs_impl with "Obs3")=> π [Ha Hb]. apply Ha; [done|done|].
    rewrite /uniq_bor_future /=. by rewrite Hb semi_iso'.
  Qed.

  Lemma tctx_extract_uniq_eqtype {𝔄 𝔅 ℭl} κ (f: 𝔅 →ₛ 𝔄) (fⁱ: 𝔄 →ₛ 𝔅) ty ty'
      (T: tctx ℭl) p E L :
    lctx_lft_alive E L κ → eqtype E L ty' ty f fⁱ → Isoₛ f fⁱ →
    tctx_extract_elt E L (p ◁ &uniq{κ} ty) (p ◁ &uniq{κ} ty' +:: T) T
      (λ post '(bor -:: cl), λ mask π,
        ∀ bor', uniq_bor_loc bor' = uniq_bor_loc bor →
        uniq_bor_current bor' = f ~~$ₛ (uniq_bor_current bor) →
        uniq_bor_future bor' π = f $ₛ (uniq_bor_future bor π) →
        post (bor' -:: cl) mask π).
  Proof. move=> ???. by eapply tctx_uniq_eqtype. Qed.
End uniq_bor_typing.

Global Hint Resolve uniq_resolve uniq_subtype uniq_eqtype : lrust_typing.

(* Registering [write_uniq]/[read_uniq] with [Hint Resolve] doesn't help
  automation in some situations, but these hints let it work. *)
Global Hint Extern 0 (typed_write _ _ (&uniq{_} _) _ _ _ _ _) =>
  simple apply write_uniq : lrust_typing.
Global Hint Extern 0 (typed_read _ _ (&uniq{_} _) _ _ _ _) =>
  simple apply read_uniq : lrust_typing.
