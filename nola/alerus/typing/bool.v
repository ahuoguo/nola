(** * The Boolean type

  Ported from VerusBelt ([typing/bool.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer). *)

From nola.alerus.typing Require Export type ctx.
From nola.alerus.typing Require Import programs.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation WpwNotation.

Section bool.
  Context `{!typeG FML Σ}.

  Program Definition bool_ty: type boolₛ :=
    {|
      pt_size := 1;
      pt_ghox (b: ~~boolₛ) _ := empty_fml ;
      pt_phys (b: ~~boolₛ) _ := [ FVal #b ] ;
    |}%I.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  
  Lemma bool_gho b d g tid : ty_gho bool_ty b d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.
  Lemma bool_gho_pers b d g tid : ty_gho_pers bool_ty b d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.

  Global Instance bool_copy: Copy bool_ty.
  Proof. split. - typeclasses eauto. - iIntros. iPureIntro. done. Qed.

  Global Instance bool_send: Send bool_ty.
  Proof.
    intros. split; trivial.
     - intros. unfold syn_abstract in H. subst x'. trivial.
     - iIntros (tid tid' x0 d g γ q κs) "_ _ lfts tok _ $ !>".
       iExists x0, 0%nat. iFrame "lfts tok".
       iSplit; [by iApply empty_fml_sem_2|done].
  Qed.
  
  Global Instance bool_sync: Sync bool_ty.
  Proof. move=> *. split; [done|]. split; reflexivity. Qed.

  Lemma bool_resolve E L : resolve E L bool_ty (const (const True)).
  Proof. apply resolve_just. Qed.
  
  Lemma bool_stack_okay : StackOkay bool_ty.
  Proof. done. Qed.

  Lemma type_bool_instr (b: bool) : typed_val #b bool_ty b.
  Proof.
    iIntros (????????) "_ _ _ _ $$ _ Obs".
    iApply twp_value. iExists -[b]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_hasty_val'; [|done]. iExists 0%nat.
    iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  Lemma type_bool {𝔄l 𝔅} (b: bool) (T: tctx 𝔄l) x e tr E L (I: invctx) (C: cctx 𝔅) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L I C (v ◁ bool_ty +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := #b in e) (λ post al, tr post (b -:: al)).
  Proof.
    iIntros. iApply type_let; [apply type_bool_instr|solve_typing|done..].
  Qed.

  Lemma type_nd_bool_instr E L I :
    typed_instr_ty E L I +[] NdBool bool_ty (λ post '-[], λ mask π, ∀b, post b mask π).
  Proof.
    iIntros (?????) "_ _ _ _ $$ _ #?".
    wp_nd_int z. wp_op. iExists -[_]. rewrite right_id tctx_hasty_val'; [|done].
    iSplit. { iExists 0%nat. iSplit; [by iApply empty_fml_sem_2|done]. }
    iApply proph_obs_impl; [|done]=>/= ? Hyp.
    destruct xl; apply Hyp.
  Qed.

  Lemma type_nd_bool {𝔄l 𝔅} (T: tctx 𝔄l) x e tr E L (I: invctx) (C: cctx 𝔅) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L I C (v ◁ bool_ty +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := NdBool in e)
      (λ post al mask π, ∀b, tr post (b -:: al) mask π)%type.
  Proof.
    iIntros. by iApply type_let; [apply type_nd_bool_instr|solve_typing| |done].
  Qed.

  Lemma type_if {𝔄l 𝔅l ℭ} p (T: tctx 𝔄l) (T': tctx 𝔅l) e1 e2 tr1 tr2 trx E L I (C: cctx ℭ) :
    tctx_extract_ctx E L +[p ◁ bool_ty] T T' trx →
    typed_body E L I C T' e1 tr1 -∗ typed_body E L I C T' e2 tr2 -∗
    typed_body E L I C T (if: p then e1 else e2)
      (trx ∘ (λ post '(b -:: vl), if b then tr1 post vl else tr2 post vl)).
  Proof.
    iIntros (?) "e1 e2". iApply typed_body_tctx_incl; [done|]=>/=.
    iIntros (?[b ?]???) "/= #LFT #PROPH #UNIQ #E L I C [p T] Obs".
    wp_bind p. iApply (twp_hasty with "p"). iIntros (?? _).
    iDestruct 1 as "[_true %Hphys]".
    inversion Hphys. subst v.
    destruct b; wp_case.
    - iApply ("e1" with "LFT PROPH UNIQ E L I C T").
      iApply (proph_obs_impl with "Obs"). intros π. done.
    - iApply ("e2" with "LFT PROPH UNIQ E L I C T").
      iApply (proph_obs_impl with "Obs"). intros π.  done.
  Qed.
End bool.

Global Hint Rewrite @bool_gho @bool_gho_pers : fml_sem.

Global Hint Resolve bool_resolve : lrust_typing.
