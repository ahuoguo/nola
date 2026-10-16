(** * Unique borrows

  Ported from VerusBelt ([typing/uniq_bor.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.

  Two changes.

  - [&uniq{κ} ty]'s ghost assertion is built from the constructors of
    [TypeFml] (see [typing/ctx.v]): it holds a value observer, an indexed
    borrow of [uniq_body_fml], the guard to [l #↦∗_] and a disjunction with
    [basically_dead κ], and every one of those is a formula now.

  - [TypeContractive] is lost.  VerusBelt gets it from
    [idx_bor_contractive] and [later_contractive]: a borrow is contractive
    in its contents exactly because the contents sit under a [▷], and
    [&uniq{κ}]'s [▷ ty.(ty_gho_pers)] supplies the other one.  Later-free a
    borrow stores a formula and is merely non-expansive, so [&uniq{κ}] is
    [TypeNonExpansive] - the same loss as [own_ptr] and [&shr{κ}].

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
