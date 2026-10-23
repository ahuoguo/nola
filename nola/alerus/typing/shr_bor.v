(** * Shared borrows

  Ported from VerusBelt ([typing/shr_bor.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  [&shr{κ} ty] is LeLiLo's shared borrow: a *guard* from the lifetime token
  [@[κ]] to the borrowed contents.  The original takes those guards at index
  [g+1] and puts [▷^(g+1)] in front of the persistent ghost part, because
  opening a guard at index [n] costs [n] laters.  Later-free the indices and
  the [▷^(g+1)] both go.

  The price is [TypeContractive].  VerusBelt gets it from
  [guards_contractive_right_if_n_ge_1]: a guard at index ≥ 1 is contractive in
  its right-hand side exactly because opening it introduces a later.  Nola's
  guard introduces none, so it is merely non-expansive, and [&shr{κ}] is only
  [TypeNonExpansive].  Recursive types through a shared borrow are therefore
  out of reach here; see [typing/fixpoint.v]. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.typing Require Import programs.
From nola.alerus.typing Require Export type ctx.
From nola.alerus.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Implicit Type 𝔄 𝔅: syn_type.

Section shr_bor.
  Context `{!typeG FML Σ}.

  Program Definition shr_bor_st {𝔄} (κ: lft) (ty: type 𝔄)
    : simple_type (at_clocₛ 𝔄) := {|
    st_size := 1;
    st_lfts := κ :: ty.(ty_lfts);
    st_E := ty.(ty_E) ++ ty_outlives_E ty κ;

    (** The physical contents are written [syn_phys], not [ty.(ty_phys)].
      [ty_phys_eq2] says they are equal, and the difference matters: a
      points-to formula keeps its contents in the constructor's *selector*,
      which [cit] compares by equality at every level, so mentioning
      [ty.(ty_phys)] here would stop [λ T, &shr{κ} T] from being
      [Productive]. *)
    st_ghox x d g tid := [Ltx(d') := d] [Lex(gg) := g] pers_fml
      (guard_fml (alive_fml κ)
         ((x.1).1 ↦[^ (x.1).2 ]!∗ syn_phys (snd x)) ∗
       guard_fml (alive_fml κ) (ty.(ty_ghox) (snd x) d' gg tid) ∗
       store_fml (ty.(ty_gho_persx) (snd x) d' gg tid))%FML;

    st_phys x tid := [FVal (LitV (x.1).1)];
  |}.
  Next Obligation.
    (** Structurally persistent, so [&shr{κ}] does not reach for [ty]'s
      persistence law - the same reason [nola/examples/rust_halt/shrref.v]
      writes [□ cif_store (ty_shr T …)]. *)
    move=> ?? ty sem H x d g tid.
    apply (by_ltx_persistent_at H)=> d'.
    apply (by_lex_persistent_at H)=> gg.
    rewrite (pers_sem_at_any (alt_sem_any H)). exact _.
  Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    (** Both indices are *bounded* in the definition above, so weakening them
      is just widening the two bounds - the argument's own laws are never
      needed.  This is what makes [&shr{κ}] unconditionally a type, and hence
      usable as the guarded former of a recursive type. *)
    move=> ?? ty sem H d g d' g' x tid ??.
    rewrite !(by_ltx_sem_at (alt_sem_any H)).
    iIntros "(%dd & %Hdd & A)". iExists dd. iSplit; [iPureIntro; lia|].
    rewrite !(by_lex_sem_at (alt_sem_any H)).
    iDestruct "A" as (gg Hgg) "A". iExists gg. iSplit; [iPureIntro; lia|done].
  Qed.
  Next Obligation.
    (** This is where the stored persistent part is read back, and why the
      law hands its conclusion out under [Wguard]: the borrowed type's
      persistent part is behind a judgment - it has to be, or [&shr{κ}] is
      not [Productive] - and only the world satisfaction opens it. *)
    move=> ?? ty κ0 x d g tid R.
    rewrite /st_gho /=. fml_simpl. rewrite /by_lt /by_le.
    iIntros "#LFT #Incl A". iDestruct "A" as (d0 ?) "A".
    rewrite by_lex_sem /by_le. iDestruct "A" as (gg ?) "A".
    rewrite pers_fml_sem !bor_sep_sem.
    iDestruct "A" as "#(_ & Gho & St)". iIntros "#Rk _ W".
    iDestruct (store_fml_acc with "St") as "#Acc".
    iDestruct ("Acc" with "W") as "[W #Pers]".
    iApply (ty_guard_proph _ ty κ0 (snd x) d0 gg tid R
      with "LFT [] Pers Rk [] W").
    { iApply (llftl_incl_trans with "Incl []"). iApply llftl_intersect_incl_r. }
    iDestruct (dguard_alive_sem with "Gho") as "#Gho0".
    iApply (guard_trans with "Rk"). iApply (guard_trans with "Incl").
    iApply (guard_trans with "[] Gho0"). iApply llftl_intersect_incl_l.
  Qed.
  Next Obligation. done. Qed.

  (** [&shr{κ} ty] is a simple type; naming it lets its ghost assertion be
    unfolded by [shr_bor_st_gho] below. *)
  Definition shr_bor {𝔄} (κ: lft) (ty: type 𝔄) : type (at_clocₛ 𝔄) :=
    ty_of_st (shr_bor_st κ ty).

  Lemma shr_bor_st_gho {𝔄} κ (ty: type 𝔄) x d g tid :
    st_gho (shr_bor_st κ ty) x d g tid ⊣⊢ [Lt(d') := d] [Le(gg) := g]
      (dguard (alive_fml κ)
         (cells_fml (x.1).1 (x.1).2 (ty.(ty_phys) (snd x) tid)) ∗
       dguard (alive_fml κ) (ty.(ty_ghox) (snd x) d' gg tid) ∗
       bor_sem (store_fml (ty.(ty_gho_persx) (snd x) d' gg tid))).
  Proof.
    rewrite /st_gho /= -(ty_phys_eq2 _ ty (snd x) tid). fml_simpl.
    rewrite /by_lt /by_le.
    apply bi.exist_proper=> d'. apply bi.sep_proper; [done|].
    rewrite by_lex_sem /by_le. apply bi.exist_proper=> gg.
    apply bi.sep_proper; [done|].
    have ? := guard_fml_pers_at alt_here.
    have ? := ty_gho_pers_pers_at ty _ alt_here.
    rewrite pers_fml_sem !bor_sep_sem.
    (* every component is persistent, so the structural [□] the definition
       carries is invisible to clients *)
    apply bi.intuitionistic_intuitionistically; exact _.
  Qed.

  Lemma shr_bor_gho {𝔄} κ (ty: type 𝔄) x d g tid :
    ty_gho (shr_bor κ ty) x d g tid ⊣⊢ [Lt(d') := d] [Le(gg) := g]
      (dguard (alive_fml κ)
         (cells_fml (x.1).1 (x.1).2 (ty.(ty_phys) (snd x) tid)) ∗
       dguard (alive_fml κ) (ty.(ty_ghox) (snd x) d' gg tid) ∗
       bor_sem (store_fml (ty.(ty_gho_persx) (snd x) d' gg tid))).
  Proof. apply shr_bor_st_gho. Qed.
  Lemma shr_bor_gho_pers {𝔄} κ (ty: type 𝔄) x d g tid :
    ty_gho_pers (shr_bor κ ty) x d g tid ⊣⊢ [Lt(d') := d] [Le(gg) := g]
      (dguard (alive_fml κ)
         (cells_fml (x.1).1 (x.1).2 (ty.(ty_phys) (snd x) tid)) ∗
       dguard (alive_fml κ) (ty.(ty_ghox) (snd x) d' gg tid) ∗
       bor_sem (store_fml (ty.(ty_gho_persx) (snd x) d' gg tid))).
  Proof. apply shr_bor_gho. Qed.

  (** Introduction.  Most clients build a [&shr] ghost assertion from pieces
    that already live at some [dd], [gg]; they hand those over together with
    the two bounds, which are what makes the indices weakenable. *)
  Lemma shr_bor_gho_intro_st {𝔄} κ (ty: type 𝔄) x d g dd gg tid :
    dd < d → gg ≤ g →
    dguard (alive_fml κ) (cells_fml (x.1).1 (x.1).2 (ty.(ty_phys) (snd x) tid)) -∗
    dguard (alive_fml κ) (ty.(ty_ghox) (snd x) dd gg tid) -∗
    bor_sem (store_fml (ty.(ty_gho_persx) (snd x) dd gg tid)) -∗
    ty_gho (shr_bor κ ty) x d g tid.
  Proof.
    iIntros (??) "A B C". rewrite shr_bor_gho /by_lt /by_le.
    iExists dd. iSplit; [iPureIntro; lia|].
    iExists gg. iSplit; [iPureIntro; lia|]. iFrame.
  Qed.

  (** The form clients use: they hold the persistent part itself, so the
    store is allocated here.  That is the one cost of hiding it behind a
    judgment, and it is the same cost [store_alloc] carries upstream. *)
  Lemma shr_bor_gho_intro' {𝔄} κ (ty: type 𝔄) x d g dd gg tid :
    dd < d → gg ≤ g →
    dguard (alive_fml κ) (cells_fml (x.1).1 (x.1).2 (ty.(ty_phys) (snd x) tid)) -∗
    dguard (alive_fml κ) (ty.(ty_ghox) (snd x) dd gg tid) -∗
    ty_gho_pers ty (snd x) dd gg tid =[Wguard]=∗
    ty_gho (shr_bor κ ty) x d g tid.
  Proof.
    iIntros (??) "A B C".
    iMod (store_fml_alloc with "C") as "C".
    { move=> sem Hs. apply (ty_gho_pers_pers_at ty sem Hs). }
    iModIntro. by iApply (shr_bor_gho_intro_st with "A B C").
  Qed.

  (** Reading the stored persistent part back *)
  Lemma shr_bor_pers_acc {𝔄} (ty: type 𝔄) y dd gg tid :
    bor_sem (store_fml (ty.(ty_gho_persx) y dd gg tid)) ⊢
      □ |->[Wguard] ty_gho_pers ty y dd gg tid.
  Proof. apply store_fml_acc. Qed.

  (** Elimination, naming both bounded indices. *)
  Lemma shr_bor_gho_elim {𝔄} κ (ty: type 𝔄) x d g tid :
    ty_gho (shr_bor κ ty) x d g tid ⊢ ∃ d' gg, ⌜d' < d⌝ ∗ ⌜gg ≤ g⌝ ∗
      (dguard (alive_fml κ)
         (cells_fml (x.1).1 (x.1).2 (ty.(ty_phys) (snd x) tid)) ∗
       dguard (alive_fml κ) (ty.(ty_ghox) (snd x) d' gg tid) ∗
       bor_sem (store_fml (ty.(ty_gho_persx) (snd x) d' gg tid))).
  Proof.
    rewrite shr_bor_gho /by_lt /by_le.
    iIntros "(%d' & % & %gg & % & A)". iExists d', gg. by iFrame.
  Qed.

  Global Instance from_sep_shr_bor_gho {𝔄} κ (ty: type 𝔄) x d' g tid :
    FromSep (ty_gho (shr_bor κ ty) x (S d') g tid)
      (dguard (alive_fml κ)
        (cells_fml (x.1).1 (x.1).2 (ty.(ty_phys) (snd x) tid)))
      (dguard (alive_fml κ) (ty.(ty_ghox) (snd x) d' g tid) ∗
        bor_sem (store_fml (ty.(ty_gho_persx) (snd x) d' g tid))).
  Proof.
    rewrite /FromSep. iIntros "[A [B C]]".
    iApply (shr_bor_gho_intro_st with "A B C"); lia.
  Qed.

  Global Instance shr_ne {𝔄} κ : NonExpansive (@shr_bor 𝔄 κ).
  Proof. solve_ne_type. Qed.
End shr_bor.

Global Hint Rewrite @shr_bor_gho_pers @shr_bor_gho : fml_sem.

Notation "&shr{ κ }" := (shr_bor κ) (format "&shr{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG FML Σ}.

  (** The original proves [TypeContractive]; see the header for why only
    non-expansiveness survives. *)
  Global Instance shr_type_ne {𝔄} κ : TypeNonExpansive (@shr_bor _ _ _ 𝔄 κ).
  Proof.
    split; [by apply (type_lft_morphism_add_one κ)|done| | |done].
    - move=>/= n ty ty' ?? _ Eq Eq' Eqp x d g tid.
      apply by_ltx_ne=>// d'. apply by_lex_ne=>// gg.
      f_equiv. f_equiv. f_equiv.
      + f_equiv. apply Eq.
      + f_equiv. apply Eq'.
    - move=>/= n ty ty' ?? _ Eq Eq' Eqp x d g tid.
      apply by_ltx_ne=>// d'. apply by_lex_ne=>// gg.
      f_equiv. f_equiv. f_equiv.
      + f_equiv. apply Eq.
      + f_equiv. apply Eq'.
  Qed.

  Lemma shr_copy {𝔄} κ (ty: type 𝔄) : Copy (&shr{κ} ty).
  Proof. split. - typeclasses eauto. - iIntros. iPureIntro. done. Qed.

  Lemma shr_stack_okay {𝔄} κ (ty: type 𝔄) : StackOkay (&shr{κ} ty).
  Proof. done. Qed.

  Global Instance shr_sync {𝔄} κ (ty: type 𝔄) : Sync ty → Sync (&shr{κ} ty).
  Proof.
    move=> Hsync tid tid' x d g. split; [done|].
    have Hsh : st_ghox (shr_bor_st κ ty) x d g tid ≡
               st_ghox (shr_bor_st κ ty) x d g tid'.
    { apply equiv_dist=> n. simpl. apply by_ltx_ne=>// dd.
      apply by_lex_ne=>// gg.
      destruct (Hsync tid tid' (snd x) dd gg) as [phys [gho pers]].
      f_equiv. f_equiv. f_equiv.
      - f_equiv. by apply equiv_dist.
      - f_equiv. by apply equiv_dist. }
    by split.
  Qed.

  (** The original's [⧖ d0] and its [|={…}▷=>^d] are gone with the time
    receipts; changing the thread id of a shared borrow needs no step. *)
  Global Instance shr_send {𝔄} κ (ty: type 𝔄) : Sync ty → Send (&shr{κ} ty).
  Proof.
    move=> Hsync. split.
    - move=> ?? [??] [??] Ha. by inversion Ha.
    - move=> tid tid' x d g G κs.
      have [_ [Hg _]] := sync_tid (ty := &shr{κ} ty) tid tid' x d g.
      iIntros "_ _ lfts _ K A $ !>". iExists x, 0. rewrite Nat.add_0_r.
      iFrame "lfts K". iSplit; [|done]. by iApply (iff_1 Hg).
  Qed.

  Global Instance shr_just_loc {𝔄} κ (ty: type 𝔄) : JustLoc (&shr{κ} ty).
  Proof. iIntros (x d g tid) "A". by iExists _. Qed.

  Lemma shr_resolve {𝔄} κ (ty: type 𝔄) E L :
    resolve E L (&shr{κ} ty) (const (const True)).
  Proof. apply resolve_just. Qed.

  Lemma shr_type_incl {𝔄 𝔅} κ κ' (f: 𝔄 →ₛ 𝔅) ty ty' :
    dincl κ' κ -∗ type_incl ty ty' f -∗
      type_incl (&shr{κ} ty) (&shr{κ'} ty') (at_cloc_mapₛ f).
  Proof.
    iIntros "#Incl". iDestruct (dincl_sem with "Incl") as "#Incl'".
    iDestruct 1 as "(_ & #Incl2 & #Sub & #SubPers & %Phys)".
    iApply (@type_incl_simple_type _ _ _ (at_clocₛ 𝔄) (at_clocₛ 𝔅) _ _).
    - done.
    - rewrite /ty_lfts /ty_of_st /st_lfts. by iApply dincl_intersect_mono.
    - iIntros "!>" (sem Hsem x d g tid).
      destruct x as [l x].
      have ? := guard_fml_pers_at Hsem.
      have ? := ty_gho_pers_pers_at ty sem Hsem.
      rewrite /= !(by_ltx_sem_at (alt_sem_any Hsem)).
      iAssert (sem (guard_fml (alive_fml κ') (alive_fml κ))) as "#Incl0".
      { iApply (dincl_at Hsem with "Incl"). }
      iIntros "(%dd & %Hdd & A)". iExists dd. iSplit; [iPureIntro; lia|].
      rewrite !(by_lex_sem_at (alt_sem_any Hsem)).
      iDestruct "A" as (gg Hgg) "A". iExists gg. iSplit; [iPureIntro; lia|].
      rewrite !(pers_sem_at_any (alt_sem_any Hsem)) !(sep_sem_at Hsem).
      iDestruct "A" as "#(Hphys & Hgho & Hpers)". iModIntro. iSplit.
      { have HP := Phys x tid.
        rewrite -(ty_phys_eq2 _ ty x tid) -(ty_phys_eq2 _ ty') in HP.
        rewrite -HP. iApply (dguard_trans_at Hsem with "Incl0 Hphys"). }
      iSplit.
      + iApply (dguard_trans_at Hsem with "Incl0 []").
        iApply (dguard_trans_at Hsem with "Hgho []").
        iApply (dguard_intro_at Hsem). iIntros (sem' Hs) "!> gho".
        iDestruct ("Sub" $! sem' Hs with "gho") as "[$ $]".
      + iApply (store_fml_map_at Hsem with "[] Hpers").
        iIntros "!>" (sem' Hs _) "pers". by iApply ("SubPers" $! sem' Hs).
    - iPureIntro. by move=> [l x].
  Qed.

  Lemma shr_subtype {𝔄 𝔅} E L κ κ' (f: 𝔄 →ₛ 𝔅) ty ty' :
    lctx_lft_incl E L κ' κ → subtype E L ty ty' f →
    subtype E L (&shr{κ} ty) (&shr{κ'} ty') (at_cloc_mapₛ f).
  Proof.
    move=> In Sub. iIntros "L". iDestruct (In with "L") as "#In".
    iDestruct (Sub with "L") as "#Sub". iIntros "!> #?".
    iApply shr_type_incl; by [iApply "In"|iApply "Sub"].
  Qed.

  Lemma shr_eqtype {𝔄 𝔅} E L κ κ' (f: 𝔄 →ₛ 𝔅) g ty ty' :
    lctx_lft_eq E L κ κ' → eqtype E L ty ty' f g →
    eqtype E L (&shr{κ} ty) (&shr{κ'} ty') (at_cloc_mapₛ f) (at_cloc_mapₛ g).
  Proof. move=> [??] [??]. split; by apply shr_subtype. Qed.

  (** Reading out of a shared borrow.

    The original hands [typed_read] its own arbitrary [H], namely the [G] that
    guards [llctx_interp L], and spends [£(d+1)] stripping the laters of the
    guard it opens.  Here the guard source has to be a *formula* - the
    Points-To Cell Logic parks it in its read bank - and the one we have is the
    fractional share inside [Ltok]: [gsrc_fml (GFrac γ q)]. *)
  Lemma read_shr {𝔄} (ty: type 𝔄) κ E L :
    Copy ty → lctx_lft_alive E L κ →
    typed_read E L (&shr{κ} ty) ty (&shr{κ} ty) snd (=).
  Proof.
    move=> Hcopy Alv x d v tid γ q. iIntros "#LFT #E tok T W".
    iDestruct "T" as "[#gho %phys]".
    iDestruct (shr_bor_gho_elim with "gho") as (d' gi Hd' Hgi) "#(A & B & C)".
    (* Open the share once, to read off the aliveness guard. *)
    iDestruct (Ltok_acc with "tok W") as "[L →W]".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct ("→W" with "L") as "[W [#key tok]]".
    (* Compose: the share guards [llctx_interp L], which guards [@[κ]], which
      guards both the physical contents and the inner ghost state. *)
    iAssert (frac_tok γ q &&{Wguard}&&> @[κ])%I as "#G1".
    { iApply (guard_trans with "[] Alv"). iApply Ltok_guard_frac. iFrame "key". }
    iDestruct (dguard_alive_sem with "A") as "#A'".
    iDestruct (dguard_alive_sem with "B") as "#B'".
    iDestruct (guard_trans with "G1 A'") as "#GA0".
    iDestruct (guard_rhs_iff (cells_fml_sem _ _ _) with "GA0") as "#GA".
    iDestruct (guard_trans with "G1 B'") as "#GB".
    (* The inner ghost state is persistent, so opening its guard once is
      enough to keep it. *)
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "GB tok Wg") as "[#T →Wg]".
    iDestruct ("→Wg" with "T") as "[Wg tok]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iDestruct (copy_concrete with "T") as "%Conc".
    iModIntro. iFrame "W".
    iExists (fst x), (to_concrete (ty_phys ty (snd x) tid)),
      (ty_phys ty (snd x) tid), (gsrc_fml (GFrac γ q)).
    inversion phys. iSplit; [done|].
    iSplit; [iPureIntro; apply length_to_concrete|].
    iSplitL "tok". { by iApply gsrc_fml_sem_2. }
    iSplit.
    { rewrite /= gsrc_fml_sem /=.
      iApply (guard_rhs_iff with "GA").
      rewrite -heap_mapsto_cells_fancy_fmap_eq fmap_to_concrete //. }
    iSplitR.
    { iIntros (l₁ c₁) "↦". rewrite -heap_complete_mapsto_fancy_fmap_eq.
      rewrite (fmap_to_concrete _ Conc). by iFrame. }
    iSplit. { iPureIntro=> _. rewrite fmap_to_concrete //. }
    (* [T] is the inner ghost state at the bounded depth [d'] and guard index
      [gg]; the read hands it out at the outer [d], [g].  The original needs a
      [▷] here, which the bounds make unnecessary. *)
    iSplitR.
    { iSplit; [|done]. iDestruct (ty_gho_depth_mono with "T") as "$"; lia. }
    iIntros "f W". iModIntro. iFrame "W". iExists x. iSplit; [done|].
    iSplitL "f".
    { rewrite /Ltok. iFrame "key". by iApply (gsrc_fml_sem_1 (s := GFrac γ q)). }
    iSplit; [|done]. by iFrame "gho".
  Qed.
End typing.

Global Hint Resolve shr_resolve shr_subtype shr_eqtype read_shr : lrust_typing.
