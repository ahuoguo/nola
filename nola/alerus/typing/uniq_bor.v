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
    move=> 𝔄 κ ty d0 g0 d1 g1 [[[[[l x0] ξi] d'] g'] idx] tid ??. rewrite /=.
    rewrite !bor_sep_sem !pure_fml_sem !or_fml_sem !basically_dead_fml_sem
      !idxbor_fml_sem !guard_fml_sem !alive_fml_sem !cmapstoany_fml_sem
      !vo_fml_sem !idx_bor_tok_fml_sem.
    iIntros "(#A & %B & (C1 & C2 & #C3) & #D & #E)". iSplitL.
    - iFrame "E A D C1 C2 C3". iPureIntro. lia.
    - iIntros "(_ & _ & (C1 & C2 & _) & _ & _)". iFrame "E A D C1 C2 C3".
      iPureIntro. lia.
  Qed.
  Next Obligation.
    move=> 𝔄 κ ty d0 g0 d1 g1 [[[[[l x0] ξi] d'] g'] idx] tid ??. rewrite /=.
    rewrite !bor_sep_sem !pure_fml_sem !or_fml_sem !basically_dead_fml_sem
      !idxbor_fml_sem.
    iIntros "(%B & #E & #F)". iFrame "E F". iPureIntro. lia.
  Qed.
  Next Obligation.
    move=> 𝔄 κ ty κ0 [[[[[l x0] ξi] d'] g'] idx] d g tid ξ R Hin. rewrite /=.
    rewrite !bor_sep_sem !pure_fml_sem !or_fml_sem !basically_dead_fml_sem
      !idxbor_fml_sem !guard_fml_sem !alive_fml_sem !cmapstoany_fml_sem
      !vo_fml_sem !idx_bor_tok_fml_sem.
    iIntros "#LFT #Incl1 (%Hle & #Pers & #Bor) #Rk #Rg".
    iAssert (κ0 ⊑ κ)%I as "#Inκ".
    { iApply (guard_trans with "Incl1 []"). iApply llftl_intersect_incl_l. }
    iAssert (κ0 ⊑ ty_lft ty)%I as "#Inty".
    { iApply (guard_trans with "Incl1 []"). iApply llftl_intersect_incl_r. }
    iDestruct "Pers" as "[bd|InnerPers]".
    { (* The lifetime is already dead, so [@[κ0]] is absurd. *)
      iDestruct "bd" as (κ') "[#Incl' #†κ']". iApply guard_false.
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
    iDestruct (llftl_idx_bor_guard' κ idx _ R with "LFT Bor Rκ Rtok")
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
    move=> 𝔄 κ ty [[[[[l x0] ξi] d'] g'] idx] d g tid. rewrite /=.
    rewrite !bor_sep_sem !pure_fml_sem !or_fml_sem !basically_dead_fml_sem
      !idxbor_fml_sem. apply _.
  Qed.
  Next Obligation.
    move=> 𝔄 κ ty [[[[[l x0] ξi] d'] g'] idx] d g tid. rewrite /=.
    rewrite !bor_sep_sem !pure_fml_sem !or_fml_sem !basically_dead_fml_sem
      !idxbor_fml_sem !guard_fml_sem !alive_fml_sem !cmapstoany_fml_sem
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
      (κ ⊑ ty_lft ty) ∗ ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗
      uniq_body ty x0 ξi d' g' idx κ tid l ∗
      (@[κ] &&{Wguard}&&> l #↦∗_) ∗
      (basically_dead κ ∨ ty_gho_pers ty x0 d' g' tid).
  Proof.
    rewrite /ty_gho /uniq_body /uniq_body_pers_component /= !bor_sep_sem
      !pure_fml_sem !or_fml_sem !basically_dead_fml_sem !guard_fml_sem
      !alive_fml_sem !cmapstoany_fml_sem !vo_fml_sem !idx_bor_tok_fml_sem
      !idxbor_fml_sem //.
  Qed.
  Lemma uniq_bor_gho_pers {𝔄} κ (ty: type 𝔄) l x0 ξi d' g' idx d g tid :
    ty_gho_pers (uniq_bor κ ty) (l, x0, ξi, d', g', idx) d g tid ⊣⊢
      ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗
      (basically_dead κ ∨ ty_gho_pers ty x0 d' g' tid) ∗
      uniq_body_pers_component ty x0 ξi d' g' idx κ tid l.
  Proof.
    rewrite /ty_gho_pers /uniq_body_pers_component /= !bor_sep_sem
      !pure_fml_sem !or_fml_sem !basically_dead_fml_sem !idxbor_fml_sem //.
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
    have Hg : ∀ y e h, ty_gho ty y e h tid ⊣⊢ ty_gho ty y e h tid'.
    { move=> y e h. by have [_ [? _]] := SyncTy tid tid' y e h. }
    have Hp : ∀ y, ty_phys ty y tid = ty_phys ty y tid'.
    { move=> y. by have [? _] := SyncTy tid tid' y 0 0. }
    have Hpc : uniq_body_pers_component ty x0 ξi d' g' idx κ tid l ⊣⊢
      uniq_body_pers_component ty x0 ξi d' g' idx κ tid' l :=
      idx_bor_iff (uniq_body_fml_sem_tid ty x0 ξi tid tid' l Hg Hp).
    have [_ [_ Hps]] := SyncTy tid tid' x0 d' g'.
    split; [done|]. split.
    - rewrite !uniq_bor_gho /uniq_body Hps Hpc //.
    - rewrite !uniq_bor_gho_pers Hps Hpc //.
  Qed.

  Lemma uniq_resolve {𝔄} E L κ (ty: type 𝔄) :
    lctx_lft_alive E L κ →
    resolve E L (&uniq{κ} ty) (λ x π, snd (vπ x π) = fst (vπ x π)).
  Proof.
    move=> Alv γ q F [[[[[l x0] ξi] d'] g'] idx] d g tid ?.
    iIntros "#LFT #PROPH #UNIQ #E tok gho". rewrite uniq_bor_gho.
    iDestruct "gho" as "(#In & %Hle & uniq & _ & _)". iIntros "W".
    iMod (resolve_uniq_body with "LFT PROPH UNIQ In E tok uniq W")
      as "[$ (#Obs & $ & _)]"; [done|done|].
    iModIntro. iApply proph_obs_eq; [|done]=> ? /=. by f_equal.
  Qed.

  Lemma uniq_subtype {𝔄} E L κ κ' (ty ty': type 𝔄) :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' idₛ idₛ →
    subtype E L (&uniq{κ} ty) (&uniq{κ'} ty') idₛ.
  Proof.
    move=> In Eqt. rewrite -eqtype_id_unfold in Eqt. iIntros "L".
    iDestruct (Eqt with "L") as "#Eqt". iDestruct (In with "L") as "#In".
    iIntros "!> #E". iSplit; [done|].
    iDestruct ("Eqt" with "E")
      as (?) "[[#Lfts1 #Lfts2][#EqOwn [#EqPers %EqPhys]]]".
    iSpecialize ("In" with "E"). iSplit; [by iApply lft_intersect_mono|].
    iSplit.
    { iModIntro. iIntros ([[[[[l x0] ξi] d'] g'] idx] d g tid) "gho".
      rewrite !uniq_bor_gho.
      iDestruct "gho" as "(#Incl & %Hle & (Vo & Tok & #Bor) & #PtBase & #Pers)".
      iAssert (basically_dead κ' ∨ ty_gho_pers ty' x0 d' g' tid)%I as "#Pers'".
      { iDestruct "Pers" as "[Dead|P]".
        - iLeft. iApply (basically_dead_incl with "In Dead").
        - iRight. iDestruct ("EqPers" $! x0 d' g' tid) as "[F _]".
          iApply "F". iApply "P". }
      iAssert (uniq_body_pers_component ty' x0 ξi d' g' idx κ' tid l)%I
        as "#Bor'".
      { iApply (incl_uniq_body_pers_component ty ty' x0 ξi d' g' idx κ κ' tid l
          with "In EqOwn [] Bor"). iIntros (??). iPureIntro. apply EqPhys. }
      iDestruct (guard_trans with "In Incl") as "#Incl1".
      iDestruct (guard_trans with "Incl1 Lfts1") as "#Incl2".
      iAssert (@[κ'] &&{Wguard}&&> l #↦∗_)%I as "#PtBase'".
      { iApply (guard_trans with "In PtBase"). }
      iSplitL "Vo Tok".
      - iFrame "Pers' Incl2 PtBase' Vo Tok Bor'". iPureIntro. lia.
      - iIntros "(_ & _ & (Vo & Tok & _) & _ & _)".
        iFrame "Pers Incl PtBase Vo Tok Bor". iPureIntro. lia. }
    iSplit.
    { iModIntro. iIntros ([[[[[l x0] ξi] d'] g'] idx] d g tid) "pers".
      rewrite !uniq_bor_gho_pers.
      iDestruct "pers" as "(%Hle & #Pers & #Bor)".
      iSplit; [iPureIntro; lia|]. iSplit.
      - iDestruct "Pers" as "[Dead|P]".
        + iLeft. iApply (basically_dead_incl with "In Dead").
        + iRight. iDestruct ("EqPers" $! x0 d' g' tid) as "[F _]".
          iApply "F". iApply "P".
      - iApply (incl_uniq_body_pers_component ty ty' x0 ξi d' g' idx κ κ' tid l
          with "In EqOwn [] Bor"). iIntros (??). iPureIntro. apply EqPhys. }
    { iPureIntro. by move=> [[[[[??]?]?]?]?] ?. }
  Qed.

  Lemma uniq_eqtype {𝔄} E L κ κ' (ty ty': type 𝔄) :
    lctx_lft_eq E L κ κ' → eqtype E L ty ty' idₛ idₛ →
    eqtype E L (&uniq{κ} ty) (&uniq{κ} ty') idₛ idₛ.
  Proof. move=> [??][??]. by split; apply uniq_subtype. Qed.

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
    iDestruct (llftl_bor_idx_acc_guarded ⊤ (gsrc_fml (GFrac γ (q/2))) κ idx
      with "LFT Bor Tok Gκ' [fa]") as "A";
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
    iSplit; [iApply (guard_trans with "Gκ' PtBase")|].
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
End uniq_bor_sem.

Global Hint Rewrite @uniq_bor_gho @uniq_bor_gho_pers : fml_sem.
