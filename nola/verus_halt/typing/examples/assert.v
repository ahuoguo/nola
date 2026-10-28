(** * [assert], ported

  Ported from VerusBelt ([typing/examples/assert.v], MIT, Hance,
  Elbeheiry, Matsushita, Dreyer).

  The first of the upstream examples, and the first use of [type_fn] in
  the port.  It is Rust's [assert_unchecked]: the precondition says the
  argument is [true], and the [false] branch is undefined behaviour.

  Two differences from upstream, both forced by the port.

  The arrow carries an execution level, so the type is
  [fn(∅; bool_ty) →{fn_lv_top} ()] rather than [fn(∅; bool_ty) → ()],
  and the rule is [type_fn_top] rather than [type_fn].  At
  [j = fn_lv_top] the body's world satisfaction is the ambient one
  ([typing/function.v]'s [typed_body_at_top]), so the body is an
  ordinary [typed_body] and the proof below is upstream's.

  Upstream applies [type_fn] through [opose proof … as H; unlock in H;
  apply H], because the [fn:] notation is locked and the many implicit
  arguments do not unify from the goal.  [type_fn_top] is applied the
  same way for the same reason. *)

From iris.proofmode Require Import proofmode.
From nola.verus_halt.typing Require Export type function product programs
  bool own cont uninit.
From nola.verus_halt.lang Require Import lang notation.

Section assert.
  Context `{!typeG FML Σ} `{FnFml0 : !FnFml}.

  (** [assert(b)] performs undefined behaviour unless [b]. *)
  Definition assert : val :=
    fn: ["b"] :=
      let: "b'" := !"b" in
      if: "b'" then
        let: "r" := new [ #0] in
        return: ["r"]
      else
        let: "r" := !(#☠) in (* undefined behaviour *)
        return: ["r"]
    .

  Lemma assert_type :
    typed_val
      assert
      ((fn(∅; bool_ty) →{fn_lv_top} ())
        (λ (c: ~~ ()) 𝛷 '-[(l, b)], λ mask π, b ∧ ∀ ret, 𝛷 ret mask π))
      (assert, ()).
  Proof.
    unfold assert. unlock.
    opose proof (@type_fn_top
        _ _ _ _ _
        [boolₛ]
        ()
        ()
        ()
        (λ y: (), FP ∅ +[bool_ty] () AtomicClosed)
        (λ (c: ~~ ()) 𝛷 '-[(l, b)] , λ mask π, b ∧ ∀ ret, 𝛷 ret mask π)
        (_)
        [BNamed "b"] _ _ _
    ) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl.
    destruct wl. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
    iApply (type_let with "[]").
      { eapply (type_deref_instr (𝔅 := boolₛ) _ (bool_ty)); trivial.
        * apply bool_stack_okay.
        * apply read_own_copy. apply bool_copy.
      }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      { iIntros (v). simpl_subst. iApply type_if.
        * apply tctx_extract_elt_here_exact.
        (* branch 1 *)
        * iApply (type_new_subtype () 0 with "[]"); first by lia.
          { apply uninit_unit_1. }
          iIntros. simpl_subst. iApply type_jump.
           -- rewrite list_elem_of_singleton. reflexivity.
           -- apply tctx_extract_elt_here_exact.
           -- apply resolve_tctx_just.
           -- reflexivity.
        (* branch 2 *)
        * iApply typed_body_vacuous.
      }
    }
    intros post [[l b] []] mask π.
    simpl. unfold trans_upper. simpl.
    intros [Hb Hforall]. intros [l1 b1] Heq. inversion Heq. subst l1. subst b1.
    destruct b; last by done. intros. apply Hforall.
    Unshelve. eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ).
  Qed.
End assert.
