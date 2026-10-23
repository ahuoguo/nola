(** * Resource-algebra ghost types

  Ported from VerusBelt ([typing/ra.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer).

  [ra_ty] is a ghost type whose ghost state is a single [own γ m] for a
  user-supplied unital camera.  It has no physical content, no borrows and no
  guards, so only [Send] and the [typed_instr]s change, with the time
  receipts. *)

From iris.proofmode Require Import proofmode.
From nola.alerus Require Import own_and.
From nola.iris Require Import guard.
From nola.alerus.lang.lib Require Import new_delete.
From nola.alerus.typing Require Import lft_contexts programs ghost own product
  tracked shr_bor freeable_util.
From nola.alerus.typing Require Export type ctx.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation WpwNotation.
Implicit Type 𝔄 𝔅: syn_type.

Section Ra.

  Context `{!typeG FML Σ}.
  Context `{G2: !inG Σ (@Ucmra' _ (~~𝔄) 𝔄_equiv 𝔄_dist 𝔄_pcore 𝔄_op 𝔄_valid 𝔄_validn 𝔄_unit 𝔄_mixin1 𝔄_mixin2 𝔄_mixin3)}.

  Hypothesis (𝔄_const  : ∀ (x : ~~𝔄) π1 π2 , @vπ 𝔄 x π1 = @vπ 𝔄 x π2).

  (** A type's ghost assertion is a formula now (see [TypeFml] in
    [typing/ctx.v]), so the resource algebra this file is parametric over has
    to have a formula standing for its ownership.  Like every other
    constructor in the development this is asked for as a class with the
    equation pinning down its semantics. *)
  Class RaFml := {
    ra_fml : positive → (~~𝔄) → FML $oi Σ;
    ra_fml_sem γ a : bor_sem (ra_fml γ a) ⊣⊢ @own _ _ G2 γ a;
    (** The constructor means the same at every candidate interpretation;
      see [AltSem] in [typing/ctx.v]. *)
    ra_fml_sem_at {sem} : alt_sem sem → ∀ γ a,
      sem (ra_fml γ a) ⊣⊢ @own _ _ G2 γ a;
  }.
  Context `{!RaFml}.

  (** Directed form, for [iApply] *)
  Lemma ra_fml_sem_2 γ a : @own _ _ G2 γ a ⊢ bor_sem (ra_fml γ a).
  Proof. by rewrite ra_fml_sem. Qed.

  (** [guard_and_own] for *stored* guards: the two guards are read at a
    candidate, combined there, and the result stored again. *)
  Lemma dguard_and_own {Px} {γ : positive} {a b c : ~~𝔄} :
    (@own _ _ G2 γ a ∧ @own _ _ G2 γ b ⊢ @own _ _ G2 γ c) →
    dguard Px (ra_fml γ a) -∗ dguard Px (ra_fml γ b) -∗
    dguard Px (ra_fml γ c).
  Proof.
    move=> Hent. have ? := guard_fml_pers_at alt_here.
    iIntros "#g1 #g2". iApply dguard_of_all. iIntros (sem' Hs Hi).
    iDestruct (guard_fml_sem_into alt_here Hs Hi with "g1") as "#G1".
    iDestruct (guard_fml_sem_into alt_here Hs Hi with "g2") as "#G2".
    iDestruct (guard_rhs_iff (ra_fml_sem_at Hs γ a) with "G1") as "#G1'".
    iDestruct (guard_rhs_iff (ra_fml_sem_at Hs γ b) with "G2") as "#G2'".
    have Heq : @own _ _ G2 γ c ⊣⊢ sem' (ra_fml γ c).
    { by rewrite (ra_fml_sem_at Hs γ c). }
    iApply (guard_rhs_iff Heq). iApply (guard_and_own Hent with "G1' G2'").
  Qed.

  Set Printing Coercions.
  Program Definition ra_ty  : type (ghostₛ (positiveₛ * 𝔄)) :=
    ty_of_gt ({|
          gt_ghox v tid :=
            let '(z, m) := v in
            ra_fml z m;
        |} : ghost_type (ghostₛ (positiveₛ * 𝔄))).
  Next Obligation.
    move => v.
    unfold indep_interp_of_syn_type in v.
    fold indep_interp_of_syn_type in v.
    destruct v as [γ v].
    move => π1 π2.
    specialize (𝔄_const v π1 π2).
    simpl.
    by f_equal.
  Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.

  (** Unfolding [ra_ty]'s ghost assertion *)
  Lemma ra_ty_gho (v : ~~ (ghostₛ (positiveₛ * 𝔄))) d g tid :
    ty_gho ra_ty v d g tid ⊣⊢ @own _ _ G2 v.1 v.2.
  Proof. destruct v. apply ra_fml_sem. Qed.
  Lemma ra_ty_gho' (v : ~~ (ghostₛ (positiveₛ * 𝔄))) d g tid :
    @own _ _ G2 v.1 v.2 ⊣⊢ ty_gho ra_ty v d g tid.
  Proof. by rewrite ra_ty_gho. Qed.


  (* Definition ra_ty  : type (at_locₛ (positiveₛ* 𝔄)) := own_ptr 0 (ra_inner). *)

  Global Instance ra_send : Send ra_ty.
  Proof.
    split; [done|]. move=> tid tid' x d g G κs.
    iIntros "_ _ lfts _ K A $ !>". iExists x, 0%nat. rewrite Nat.add_0_r.
    iFrame "lfts K". iSplit; [|done]. iExact "A".
  Qed.

  Global Instance ra_sync : Sync ra_ty.
  Proof. move => ??[??]??; split => //=. Qed.

  Lemma ra_resolve E L : resolve E L ra_ty (const (const True)).
  Proof. apply resolve_just. Qed.

End Ra.

Notation "RA_Alloc: p" := (new [ #0])%E (at level 102, p at level 150): expr_scope.
Notation "RA_Join: p1 p2" := (new [ #0])%E (at level 102, p1, p2 at level 1): expr_scope.
Notation "RA_Split: p p1 p2" := (new [ #0])%E (at level 102, p, p1, p2 at level 1): expr_scope.
Notation "RA_Unit:" := (new [ #0])%E : expr_scope.
Notation "RA_Update: self p" := (new [ #0])%E (at level 102, self, p at level 1): expr_scope.
Notation "RA_Validate: self" := (new [ #0])%E (at level 102, self at level 1): expr_scope.

Section RA_type.

  Context `{!typeG FML Σ}.
  Context `{G2: !inG Σ (@Ucmra' _ (~~𝔄) 𝔄_equiv 𝔄_dist 𝔄_pcore 𝔄_op 𝔄_valid 𝔄_validn 𝔄_unit 𝔄_mixin1 𝔄_mixin2 𝔄_mixin3) }.
  Context `{RaFml0 : !RaFml}.
  Hypothesis (𝔄_const  : ∀ (x : ~~𝔄) π1 π2 , @vπ 𝔄 x π1 = @vπ 𝔄 x π2).

  Lemma typed_ra_alloc (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I
    +[p ◁ own_ptr 0 (ghost_ty ty)]
    (RA_Alloc: p)
    (λ v, +[v ◁ own_ptr 0 (ra_ty 𝔄_const)])
    (λ post '-[(_, x)], λ mask π, valid(x) ∧ ∀ l γ, post -[(l, (γ, x))] mask π).
  Proof.
    move => tid postπ mask iκs xl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct xl as [[pl m] [ ]].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & %Hvalid & %Hpost)" => //.
    iMod (@own_alloc _ _ G2 m Hvalid) as "(%γ & Hm)". iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, (γ, m))].
    iFrame "L".
    rewrite /ra_ty/tctx_elt_interp/ty_own/=.
    iDestruct "TY" as "((% & %d & % & Hgho & %Hphys) & _)".
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hgho") as "[]"|].
    iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR => //=.
      rewrite ?own_ptr_gho /= ?ra_ty_gho. repeat rewrite heap_mapsto_fancy_vec_nil.
      by iFrame.
    - iApply (proph_obs_impl with "Obs").
      intros π' [_ ].
      apply H0.
  Qed.

  Lemma typed_ra_join (p1 p2 : path) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 (ra_ty 𝔄_const); p2 ◁ own_ptr 0 (ra_ty 𝔄_const)]
    (RA_Join: p1 p2)
    (λ v, +[v ◁ own_ptr 0 (ra_ty 𝔄_const)])
    (λ post '-[(_, (γ1, x1)); (_, (γ2, x2))], λ mask π, γ1 = γ2 ∧ ∀ l, post -[(l, (γ1, x1 ⋅ x2))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl1 [γ1 x1]] [[pl2 [γ2 x2]] []]].
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & %Hpost)" => //.
    iDestruct "TY" as "(H1 & H2 & _)".
    rewrite /ra_ty/tctx_elt_interp/ty_own/=.
    iDestruct "H1" as "(%l1 & %d1 & % & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%l2 & %d2 & % & Hown2 & %Hphys2)".
    destruct d1 as [|d1];
      [by iDestruct (false_fml_sem_1 with "Hown1") as "[]"|].
    destruct d2 as [|d2];
      [by iDestruct (false_fml_sem_1 with "Hown2") as "[]"|].
    rewrite ?own_ptr_gho /= ?ra_ty_gho.
    iDestruct "Hown1" as "(?&?&Hown1)".
    iDestruct "Hown2" as "(?&?&Hown2)".
    iCombine "Hown1 Hown2" as "Hown".
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, (γ1, (x1 ⋅ x2)))].
    iFrame "L".
    iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR => //=.
      rewrite ?own_ptr_gho /= ?ra_ty_gho.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      by iFrame.
    - iApply (proph_obs_impl with "Obs").
      intros π' [_ ].
      apply H1.
  Qed.

  Lemma typed_ra_split (self p1 p2 : path) (ty : type 𝔄) E L I :
    typed_instr E L I
    +[self ◁ own_ptr 0 (ra_ty 𝔄_const); p1 ◁ own_ptr 0 (ghost_ty ty); p2 ◁ own_ptr 0 (ghost_ty ty)] 
    (RA_Split: self p1 p2)
    (λ v, +[v ◁ own_ptr 0 (prod_ty (ra_ty 𝔄_const) (ra_ty 𝔄_const))])
    (λ post '-[(_, (γ, x)); (_, x1); (_, x2)], λ mask π, x = x1 ⋅ x2 ∧ ∀ l, post -[(l, ((γ, x1), (γ, x2)))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ x]] [[pl1 x1] [[pl2 x2] []]]].
    simpl in x1, x2.
    iDestruct "TY" as "(H & _ & _ & _)".
    iDestruct "H" as "(%pl' & %d & % & Hown & %Hphys)".
    injection Hphys => ? /=; subst pl'.
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite ?own_ptr_gho /= ?ra_ty_gho.
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & -> & %Hpost)" => //.
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, ((γ, x1), (γ, x2)))].
    iFrame "L".
    iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR => //=.
      rewrite /ty_own ?own_ptr_gho /= ?prod_ty_gho /= ?ra_ty_gho.
      iDestruct "Hown" as "(?&?&Hown1&Hown2)".
      repeat rewrite heap_mapsto_fancy_vec_nil.
      iFrame. by rewrite ?freeable_sz_full.
    - iApply (proph_obs_impl with "Obs").
      intros π' [_ ].
      apply H0.
  Qed.

  Lemma typed_ra_unit E L I :
    typed_instr E L I
    +[]
    (RA_Unit:)
    (λ v, +[v ◁ own_ptr 0 (ra_ty 𝔄_const)])
    (λ post '-[], λ mask π, ∀ l γ, post -[(l, (γ, ε))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs" => /=.
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (@own_alloc _ _ G2 ε) as "(%γ & Hm)".
    { by eapply mixin_ucmra_unit_valid. }
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, (γ, ε))].
    iFrame "L".
    rewrite /ra_ty/tctx_elt_interp/ty_own/=.
    iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR => //=.
      rewrite ?own_ptr_gho /= ?ra_ty_gho.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      by iFrame.
    - iApply (proph_obs_impl with "Obs").
      by destruct vπl.
  Qed.

  Lemma typed_ra_update (self p : path) (ty : type 𝔄) E L I :
    typed_instr E L I
    +[self ◁ own_ptr 0 (ra_ty 𝔄_const); p ◁ own_ptr 0 (ghost_ty ty)]
    (RA_Update: self p)
    (λ v, +[v ◁ own_ptr 0 (ra_ty 𝔄_const)])
    (λ post '-[(_, (γ, x)); (_, y)], λ mask π, (@cmra_update _ (ucmra_cmraR (Ucmra' (~~ 𝔄) 𝔄_mixin1 𝔄_mixin2 𝔄_mixin3)) x y) ∧ ∀ l, post -[(l, (γ, y))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ x]] [[ply y] []]].
    simpl in y.
    iDestruct "TY" as "(H & ? & _)".
    iDestruct "H" as "(%pl' & %d & % & Hown & %Hphys)".
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite ?own_ptr_gho /= ?ra_ty_gho.
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & %Hupd & _)" => //=.
    iDestruct "Hown" as "(? & ? & Hown)".
    iMod (own_update with "Hown") as "Hown" => //.
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, (γ, y))].
    iFrame "L".
    rewrite /ra_ty/tctx_elt_interp/ty_own/=.
    iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR => //=.
      rewrite ?own_ptr_gho /= ?ra_ty_gho. iFrame. done.
    - iApply (proph_obs_impl with "Obs").
      intros π' [_ ].
      apply H0.
  Qed.

  Lemma typed_ra_update_nondeterministic (self p : path) (n : nat) (ty : type (vecₛ 𝔄 n)) E L I :
    typed_instr E L I
    +[self ◁ own_ptr 0 (ra_ty 𝔄_const); p ◁ own_ptr 0 (ghost_ty ty)]
    (RA_Update: self p)
    (λ v, +[v ◁ own_ptr 0 (ra_ty 𝔄_const)])
    (λ post '-[(_, (γ, x)); (_, ys)], λ mask π, 0 < n ∧ (Vector.Forall (λ y, (@cmra_update _ (ucmra_cmraR (Ucmra' (~~ 𝔄) 𝔄_mixin1 𝔄_mixin2 𝔄_mixin3)) x y)) ys) ∧ ∀ l, Vector.Forall (λ y, post -[(l, (γ, y))] mask π) ys).
  Proof.
    move => tid postπ mask iκs vπl.
    fold indep_interp_of_syn_type.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ x]] [[plys ys] []]].
    simpl in ys.
    iDestruct "TY" as "(H & _ & _)".
    iDestruct "H" as "(%pl' & %d & % & Hown & %Hphys)".
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite ?own_ptr_gho /= ?ra_ty_gho.
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & %Hn & %Hupd & _)" => //=.
    iDestruct "Hown" as "(? & ? & Hown)".
    destruct n; first lia.
    inv_vec ys => y ys Hupd.
    iMod (own_update with "Hown") as "Hown".
    { apply Vector.Forall_cons_iff in Hupd as [Hupd ?].
      exact Hupd. }
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, (γ, y))].
    iFrame "L".
    rewrite /ra_ty/tctx_elt_interp/ty_own/=.
    iSplitL.
    - iSplitL; [|done]. iExists _, 1%nat; iSplitR => //=.
      rewrite ?own_ptr_gho /= ?ra_ty_gho.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      by iFrame.
    - iApply (proph_obs_impl with "Obs").
      intros π' [_ [_ Hpost]].
      specialize (Hpost l).
      apply Vector.Forall_cons_iff in Hpost as [Hpost ?].
      apply Hpost.
  Qed.

  Let U := (@Ucmra' _ (~~𝔄) 𝔄_equiv 𝔄_dist 𝔄_pcore 𝔄_op 𝔄_valid 𝔄_validn 𝔄_unit 𝔄_mixin1 𝔄_mixin2 𝔄_mixin3).

  (* We need the RA to be discrete otherwise to use `own_valid`, otherwise we can't turn own γ x into a pure predicate because it's only valid uptil step index n *)
  Lemma typed_ra_validate `{! CmraDiscrete U } κ (self : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[self ◁ shr_bor κ (ra_ty 𝔄_const)]
    (RA_Validate: self)
    (λ _, +[])
    (λ post '-[(l, (γ, x))], λ mask π, (valid x → post -[] mask π)).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ x]] []].
    iDestruct "TY" as "(H & _)".
    iDestruct "H" as "(%pl' & %d & % & Hown & %Hphys)".
    simpl in Hphys.
    injection Hphys => ? /=; subst pl'.
    iDestruct (shr_bor_gho_elim with "Hown") as (dd gg Hdd Hgg) "#(_ & Hshr & _)".
    iClear "Hown".
    (* iMod (proph_obs_sat with "PROPH Obs") as "(%π & %Alv & _)" => //=. *)
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (dguard_alive_sem with "Hshr") as "#Hshr0".
    iDestruct (guard_trans with "Alv Hshr0") as "#G0".
    iDestruct (guard_rhs_iff (ra_ty_gho _ _ _ _ _) with "G0") as "#G1".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "G1 L Wg") as "[Hown →Wg]".
    iDestruct (own_valid with "Hown") as "%Hvalid".
    iDestruct ("→Wg" with "Hown") as "[Wg L]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "_".
    iExists -[]. iFrame "L".
    iSplit => //.
    iApply (proph_obs_impl with "Obs").
    intros π' ?.
    by apply H0.
  Qed.

  Notation "RA_JoinShared: p1 p2" := (new [ #0])%E (at level 102, p1, p2 at level 1): expr_scope.

(*
  Lemma typed_ra_join_shared `{! CmraDiscrete U } κ (p1 p2 : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p1 ◁ shr_bor κ (ra_ty 𝔄_const); p2 ◁ shr_bor κ (ra_ty 𝔄_const)] (RA_JoinShared: p1 p2) (λ v, +[v ◁ shr_bor κ (ra_ty 𝔄_const)]) (λ post '-[(l1, (γ1, x1)); (l2, (γ2, x2))], λ mask π, γ1 = γ2 ∧ ∀ y l, x1 ≼ y → x2 ≼ y → post -[(l, (γ1, y))] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    fold indep_interp_of_syn_type.
    iIntros "LFT #PROPH UNIQ E L I TY #Obs" => /=.
    destruct vπl as [[pl1 [γ1 x1]] [[pl2 [γ2 x2]] []]].
    iDestruct "TY" as "(H1 & H2 & _)".
    iDestruct "H1" as "(%pl1' & %d1 & % & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%pl2' & %d2 & % & Hown2 & %Hphys2)".
    simpl in Hphys1, Hphys2.
    injection Hphys1 => ? /=; subst pl1'.
    injection Hphys2 => ? /=; subst pl2'.
    iDestruct (shr_bor_gho_elim with "Hown1") as (dd1 gg1 Hdd1 Hgg1)
      "#(_ & Hshr1' & _)".
    iDestruct (shr_bor_gho_elim with "Hown2") as (dd2 gg2 Hdd2 Hgg2)
      "#(_ & Hshr2' & _)".
    iDestruct (guard_rhs_iff (ra_ty_gho _ _ _ _ _) with "Hshr1'") as "#Hshr1".
    iDestruct (guard_rhs_iff (ra_ty_gho _ _ _ _ _) with "Hshr2'") as "#Hshr2".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    destruct (decide (d1 ≤ d2)) as [Hle | Hgt].
    - iDestruct (guard_trans_right with "Alv Hshr1") as "G1".
      iDestruct (guard_trans_right with "Alv Hshr2") as "G2".
      iApply wp_fupd.
      wp_lam.
      wp_bind (_ ≤ _)%E.
      iPoseProof (lguards_weaken_later _ _ _ _ (S (d2 + 1)) with "G1") as "G1'"; first lia.
      wp_pure (_ ≤ _)%E.
      iApply wp_fupd.
      wp_if.
      iIntros "!>".
      leaf_open_laters "G1'" with "L" as "Hown". { solve_ndisj. }
      iPoseProof (guards_and_point with "G1' G2") as "G3"; [ | | ..].
      2: {
        iIntros "H". iApply (and_own_discrete_ucmra with "H"). }
  *)

  Notation "RA_JoinSharedDet: p1 p2 p" := (new [ #0])%E (at level 102, p1, p2, p at level 1): expr_scope.
  
  Lemma typed_ra_join_shared_to_target `{! CmraDiscrete U } κ (p1 p2 p : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ shr_bor κ (ra_ty 𝔄_const); p2 ◁ shr_bor κ (ra_ty 𝔄_const); p ◁ own_ptr 0 (ghost_ty ty)] 
    (RA_JoinSharedDet: p1 p2 p)
    (λ v, +[v ◁ shr_bor κ (ra_ty 𝔄_const)])
    (λ post '-[(l1, (γ1, x1)); (l2, (γ2, x2)); (_, y)], λ mask π, γ1 = γ2 ∧ (∀ p, ✓ p ∧ x1 ≼ p ∧ x2 ≼ p → y ≼ p) ∧ ∀ l, post -[(l, (γ1, y))] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    fold indep_interp_of_syn_type.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl1 [γ1 x1]] [[pl2 [γ2 x2]] [[ply y] []]]].
    simpl in y.
    iDestruct "TY" as "(H1 & H2 & _ & _)".
    iDestruct "H1" as "(%pl1' & %d1 & % & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%pl2' & %d2 & % & Hown2 & %Hphys2)".
    simpl in Hphys1, Hphys2.
    injection Hphys1 => ? /=; subst pl1'.
    injection Hphys2 => ? /=; subst pl2'.
    iDestruct (shr_bor_gho_elim with "Hown1") as (dd1 gg1 Hdd1 Hgg1)
      "#(_ & Hshr1' & _)".
    iDestruct (shr_bor_gho_elim with "Hown2") as (dd2 gg2 Hdd2 Hgg2)
      "#(_ & Hshr2' & _)".
    iDestruct (Alv with "L E") as "#Alv".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & %Hy & _)" => //.
    (* The original splits on [d1 ≤ d2] only to align the two guards' later
      indices with [lguards_weaken_later]; later-free there are no indices. *)
    iPoseProof (dguard_and_own (γ:=γ1) (c:=y) with "Hshr1' Hshr2'")
      as "#Hshr3".
    { iIntros "H". iApply (and_own_discrete_ucmra_specific with "H").
      move => w Hvalid Hincl1 Hincl2. by apply Hy. }
    (* [ra_ty]'s persistent part is [True]; it still has to be parked, since
       the shared borrow holds that slot behind a judgment. *)
    iDestruct (wsat_split (W:=alerus_wsat) (W':=Wguard) with "W") as "[Wg Wr]".
    iMod (store_ty_gho_pers (ra_ty 𝔄_const) (γ1, y) 0 0 tid with "[] Wg")
      as "[Wg #StE]".
    { by iApply empty_fml_sem_2. }
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[((l, []), (γ1, y))].
    iFrame "L".
    rewrite /ra_ty/tctx_elt_interp/ty_own/=.
    iSplitL.
    + iSplitL; [|done]. iExists _, 1%nat; iSplitR => //=.
      iSplitR; [|done].
      iApply (shr_bor_gho_intro_st κ (ra_ty 𝔄_const) ((l, []), (γ1, y))
        _ _ 0 0); [lia|lia| | |].
      { iApply dguard_cells_nil. }
      { iApply "Hshr3". }
      { iApply "StE". }
    + iApply (proph_obs_impl with "Obs").
      intros π' [_ [? ?] ].
      apply H2.
  Qed.

  Notation "RA_Weaken: p1 p2" := (new [ #0])%E (at level 102, p1, p2 at level 1): expr_scope.

  Lemma typed_ra_weaken `{! CmraDiscrete U } κ (p1 p2 : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ shr_bor κ (ra_ty 𝔄_const); p2 ◁ own_ptr 0 (ghost_ty ty)]
    (RA_Weaken: p1 p2)
    (λ v, +[v ◁ shr_bor κ (ra_ty 𝔄_const)])
    (λ post '-[(l, (γ, x)); (_, y)], λ mask π, y ≼ x ∧ ∀ l, post -[(l, (γ, y))] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    fold indep_interp_of_syn_type.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ x]]  [[ply y] []] ].
    simpl in y.
    iDestruct "TY" as "(H & _ & _)".
    iDestruct "H" as "(%pl' & %d & % & Hown & %Hphys)".
    simpl in Hphys.
    injection Hphys => ? /=; subst pl'.
    iDestruct (shr_bor_gho_elim with "Hown") as (dd gg Hdd Hgg)
      "#(_ & Hshr0 & _)".
    iDestruct (Alv with "L E") as "#Alv".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & %Hincl & _)" => //.
    iPoseProof (dguard_and_own (γ:=γ) (c:=y) with "Hshr0 Hshr0") as "#Hshr'".
    { iIntros "H".
      iApply (and_own_discrete_ucmra_specific with "H").
      move => w Hvalid Hincl1 Hincl2.
      by etransitivity. }
    (* [ra_ty]'s persistent part is [True]; it still has to be parked, since
       the shared borrow holds that slot behind a judgment. *)
    iDestruct (wsat_split (W:=alerus_wsat) (W':=Wguard) with "W") as "[Wg Wr]".
    iMod (store_ty_gho_pers (ra_ty 𝔄_const) (γ, y) 0 0 tid with "[] Wg")
      as "[Wg #StE]".
    { by iApply empty_fml_sem_2. }
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[((l, []), (γ, y))].
    iFrame "L".
    rewrite /ra_ty/tctx_elt_interp/ty_own/=.
    iSplitL.
    + iSplitL; [|done]. iExists _, 1%nat; iSplitR => //=.
      iSplitR; [|done].
      iApply (shr_bor_gho_intro_st κ (ra_ty 𝔄_const) ((l, []), (γ, y))
        _ _ 0 0); [lia|lia| | |].
      { iApply dguard_cells_nil. }
      { iApply "Hshr'". }
      { iApply "StE". }
    + iApply (proph_obs_impl with "Obs").
      intros π' [_ ? ].
      apply H0.
  Qed.

  Notation "RA_UpdateWithShr: self other new_value" := (new [ #0])%E (at level 102, self,other,new_value at level 1): expr_scope.

  Lemma typed_ra_update_with_shr `{! CmraDiscrete U } κ (self other new_value : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[self ◁ own_ptr 0 (ra_ty 𝔄_const); other ◁ shr_bor κ (ra_ty 𝔄_const); new_value ◁ own_ptr 0 (ghost_ty ty)]
    (RA_UpdateWithShr: self other new_value)
    (λ out, +[out ◁ own_ptr 0 (ra_ty 𝔄_const)])
    (λ post '-[(l1, (γ1, x)); (l2, (γ2, y)); (_, z)], λ mask π, γ1 = γ2 ∧ (@cmra_update _ (ucmra_cmraR (Ucmra' (~~ 𝔄) 𝔄_mixin1 𝔄_mixin2 𝔄_mixin3)) (x ⋅ y) (z ⋅ y))  ∧ ∀ l, post -[(l, (γ1, z))] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl1 [γ1 x]] [[pl2 [γ2 y]] [[plz z] []]]].
    simpl in z.
    iDestruct "TY" as "(H1 & H2 & _ & _)".
    iDestruct "H1" as "(%pl1' & %d1 & % & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%pl2' & %d2 & % & Hown2 & %Hphys2)".
    simpl in Hphys1, Hphys2.
    injection Hphys1 => ? /=; subst pl1'.
    injection Hphys2 => ? /=; subst pl2'.
    destruct d1 as [|d1];
      [by iDestruct (false_fml_sem_1 with "Hown1") as "[]"|].
    rewrite ?own_ptr_gho /= ?ra_ty_gho.
    iDestruct "Hown1" as "(_ & _ & Hx)".
    iDestruct (shr_bor_gho_elim with "Hown2") as (dd2 gg2 Hdd2 Hgg2)
      "#(_ & Hy0 & _)".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (dguard_alive_sem' (ra_fml_sem _ _) with "Hy0") as "#Hy".
    iDestruct (guard_trans with "Alv Hy") as "#G1".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & %Hupd & _)" => //.
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "G1 L Wg") as "[Hown →Wg]".
    iCombine "Hx Hown" as "Hxy".
    iMod (own_update with "Hxy") as "Hxy" => //.
    iDestruct "Hxy" as "[Hx Hown]".
    iDestruct ("→Wg" with "Hown") as "[Wg L]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    rewrite /tctx_elt_interp/ty_own/=.
    iExists -[(l, (γ1, z))]. iFrame "L".
    iSplit => //=.
    + iSplitL "Hx"; [|done]. iExists _, 1%nat.
      rewrite own_ptr_gho /= ?ra_ty_gho /= heap_mapsto_fancy_vec_nil
        freeable_sz_full.
      iFrame "Hx". repeat iSplit; try done. by iRight.
    + iApply (proph_obs_impl with "Obs").
      intros π' [_ [_ ]].
      by apply H1.
  Qed.

  Notation "RA_UpdateWithShrNonDet: self other new_values" := (new [ #0])%E (at level 102, self,other,new_values at level 1): expr_scope.

  Lemma typed_ra_update_with_shr_non_det `{! CmraDiscrete U } κ n (self other new_values : path) (ty : type (vecₛ 𝔄 n)) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[self ◁ own_ptr 0 (ra_ty 𝔄_const); other ◁ shr_bor κ (ra_ty 𝔄_const); new_values ◁ own_ptr 0 (ghost_ty ty)]
    (RA_UpdateWithShrNonDet: self other new_values)
    (λ out, +[out ◁ own_ptr 0 (ra_ty 𝔄_const)])
    (λ post '-[(l1, (γ1, x)); (l2, (γ2, y)); (_, zs)], λ mask π, γ1 = γ2 ∧ 0 < n ∧ (Vector.Forall (λ z, (@cmra_update _ (ucmra_cmraR (Ucmra' (~~ 𝔄) 𝔄_mixin1 𝔄_mixin2 𝔄_mixin3)) (x ⋅ y) (z ⋅ y))) zs)  ∧ ∀ l, Vector.Forall (λ z, post -[(l, (γ1, z))] mask π) zs ).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "LFT #PROPH UNIQ E L $ TY #Obs" => /=.
    fold indep_interp_of_syn_type.
    destruct vπl as [[pl1 [γ1 x]] [[pl2 [γ2 y]] [[plzs zs] []]]].
    simpl in zs.
    iDestruct "TY" as "(H1 & H2 & _ & _)".
    iDestruct "H1" as "(%pl1' & %d1 & % & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%pl2' & %d2 & % & Hown2 & %Hphys2)".
    simpl in Hphys1, Hphys2.
    injection Hphys1 => ? /=; subst pl1'.
    injection Hphys2 => ? /=; subst pl2'.
    destruct d1 as [|d1];
      [by iDestruct (false_fml_sem_1 with "Hown1") as "[]"|].
    rewrite ?own_ptr_gho /= ?ra_ty_gho.
    iDestruct "Hown1" as "(_ & _ & Hx)".
    iDestruct (shr_bor_gho_elim with "Hown2") as (dd2 gg2 Hdd2 Hgg2)
      "#(_ & Hy0 & _)".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (dguard_alive_sem' (ra_fml_sem _ _) with "Hy0") as "#Hy".
    iDestruct (guard_trans with "Alv Hy") as "#G1".
    iApply fupdw_twpw_nonval; [done|]. iIntros "W".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & %Hn & %Hupd & _)" => //.
    destruct n; first lia.
    inv_vec zs => z zs Hupd.
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "G1 L Wg") as "[Hown →Wg]".
    iCombine "Hx Hown" as "Hxy".
    iMod (own_update with "Hxy") as "Hxy".
    { apply Vector.Forall_cons_iff in Hupd as [Hupd ?].
      exact Hupd. }
    iDestruct "Hxy" as "[Hx Hown]".
    iDestruct ("→Wg" with "Hown") as "[Wg L]".
    iDestruct (wsat_join (W:=alerus_wsat) with "Wg Wr") as "W".
    iModIntro. iFrame "W".
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    rewrite /tctx_elt_interp/ty_own/=.
    iExists -[(l, (γ1, z))]. iFrame "L".
    iSplit => //=.
    + iSplitL "Hx"; [|done]. iExists _, 1%nat.
      rewrite own_ptr_gho /= ?ra_ty_gho /= heap_mapsto_fancy_vec_nil
        freeable_sz_full.
      iFrame "Hx". repeat iSplit; try done. by iRight.
    + iApply (proph_obs_impl with "Obs").
      intros π' [_ [_ [? Hpost]]].
      specialize (Hpost l).
      apply Vector.Forall_cons_iff in Hpost as [Hpost ?].
      apply Hpost.
  Qed.

End RA_type.
