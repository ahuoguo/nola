(** * Ghost types

  Ported from VerusBelt ([typing/ghost.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer).

  A ghost value has no ghost state and no physical content at all, so
  everything here is trivial.  The only change is that the three allocation
  rules no longer mint a time receipt to satisfy [own_ptr]'s depth index. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.lang.lib Require Import new_delete.
From nola.alerus.typing Require Import programs own freeable_util.
From nola.alerus.typing Require Export type ctx.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.

Section ghost.
  Context `{!typeG FML Σ}.

  Program Definition ghost_ty {𝔄} (ty: type 𝔄) : type (ghostₛ 𝔄) :=
    @ty_of_st _ _ _ (ghostₛ 𝔄) ({|
      st_size := 0;
      st_lfts := ty.(ty_lfts);
      st_E := [];
      st_ghox x d g tid := empty_fml;
      st_phys x tid := [];
    |}%I : simple_type (ghostₛ 𝔄)).
  Next Obligation. move=> ?? sem H *. rewrite (empty_sem_at H). exact _. Qed.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. move=> ?? sem H *. by iIntros "$". Qed.
  Next Obligation.
    move=> 𝔄 ty κ x d g tid ξ R Hin. exfalso. simpl in Hin. set_solver.
  Qed.
  Next Obligation. done. Qed.

  Lemma ghost_ty_gho {𝔄} (ty: type 𝔄) x d g tid :
    ty_gho (ghost_ty ty) x d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.
  Lemma ghost_ty_gho_pers {𝔄} (ty: type 𝔄) x d g tid :
    ty_gho_pers (ghost_ty ty) x d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.

  Global Instance ghost_ne {𝔄} : NonExpansive (@ghost_ty 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance ghost_send {𝔄} (ty : type 𝔄) : Send (ghost_ty ty).
  Proof.
    split; [done|]. move=> tid tid' x d g G κs.
    iIntros "_ _ lfts _ K _ $ !>". iExists x, 0. rewrite Nat.add_0_r.
    iFrame "lfts K".
    iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  Global Instance ghost_sync {𝔄} (ty : type 𝔄) : Sync (ghost_ty ty).
  Proof. move=> *. split; [done|]. split; reflexivity. Qed.

  Global Instance ghost_copy {𝔄} (ty : type 𝔄) : Copy (ghost_ty ty).
  Proof. split; [exact _|]. move=> *. by iIntros "_". Qed.

  Lemma ghost_resolve {𝔄} (ty: type 𝔄) E L :
    resolve E L (ghost_ty ty) (const (const True)).
  Proof. apply resolve_just. Qed.

  Lemma ghost_constant {𝔄} E L I (ty : type 𝔄) (c: ~~𝔄) :
    typed_instr E L I
      +[] (new [ #0 ]%E)
      (λ q, +[q ◁ own_ptr 0 (ghost_ty ty)])
      (λ post '-[], λ mask π, forall l, post -[(l, c)] mask π).
  Proof.
    move=> tid postπ mask iκs [].
    iIntros "_ _ _ _ $$ TY #Obs" => /=.
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[(l, c)]. iFrame. iSplitL.
    - iExists #l, 1%nat. iSplit; [done|].
      rewrite /ty_own own_ptr_gho /= heap_mapsto_fancy_vec_nil
        freeable_sz_full.
      iSplit; [|done]. iSplit; [done|].
      iSplit; [by iRight|by iApply empty_fml_sem_2].
    - iApply (proph_obs_impl with "Obs"). done.
  Qed.

  Lemma ghost_snapshot {𝔄} E L I p (ty : type 𝔄) :
    typed_instr E L I
      +[p ◁ ty]
      (new [ #0 ]%E)
      (λ q, +[p ◁ ty; q ◁ own_ptr 0 (ghost_ty ty)])
      (λ post '-[x], λ mask π, forall l, post -[x; (l, x)] mask π).
  Proof.
    move=> tid postπ mask iκs [x []].
    iIntros "_ _ _ _ $$ [T TY] #Obs" => /=.
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[x; (l, x)]. iFrame "T". iFrame. iSplitL.
    - iExists #l, 1%nat. iSplit; [done|].
      rewrite /ty_own own_ptr_gho /= heap_mapsto_fancy_vec_nil
        freeable_sz_full.
      iSplit; [|done]. iSplit; [done|].
      iSplit; [by iRight|by iApply empty_fml_sem_2].
    - iApply (proph_obs_impl with "Obs"). done.
  Qed.

  Lemma ghost_compute {𝔄 𝔅 ℭ} E L I p1 p2 (ty1 : type 𝔄) (ty2 : type 𝔅)
      (ty: type ℭ) (f : (~~𝔄) → (~~𝔅) → (~~ℭ)) :
    typed_instr E L I
      +[p1 ◁ ty1; p2 ◁ ty2]
      (new [ #0 ]%E)
      (λ q, +[p1 ◁ ty1; p2 ◁ ty2; q ◁ own_ptr 0 (ghost_ty ty)])
      (λ post '-[x; y], λ mask π, forall l, post -[x; y; (l, f x y)] mask π).
  Proof.
    move=> tid postπ mask iκs [x [y []]].
    iIntros "_ _ _ _ $$ [T1 [T2 TY]] #Obs" => /=.
    iApply (twp_new 0); [lia|done|]. iIntros (l) "(† & ↦)".
    iExists -[x; y; (l, f x y)]. iFrame "T1 T2". iFrame. iSplitL.
    - iExists #l, 1%nat. iSplit; [done|].
      rewrite /ty_own own_ptr_gho /= heap_mapsto_fancy_vec_nil
        freeable_sz_full.
      iSplit; [|done]. iSplit; [done|].
      iSplit; [by iRight|by iApply empty_fml_sem_2].
    - iApply (proph_obs_impl with "Obs"). done.
  Qed.
End ghost.

Global Hint Rewrite @ghost_ty_gho @ghost_ty_gho_pers : fml_sem.

Global Hint Resolve ghost_resolve : lrust_typing.
