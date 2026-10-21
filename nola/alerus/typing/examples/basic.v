(** * A first worked example

  [nola/examples/rust_halt/verify/] verifies its programs against the typing
  rules while staying parametric in the constructor signature [CON] and the
  judgment type [JUDG] - [type_total] is never applied there - and so does
  this.  The instance that keeps the soundness theorems from being vacuous is
  [typing/inst.v]'s [alerus_sem]; what this file does is exercise the typing
  rules themselves. *)

From nola.alerus.lang Require Import notation proofmode.
From nola.alerus.typing Require Export int programs.
From nola.bi Require Import modw.
Import ModwNotation WpwNotation.

Section basic.
  Context `{!typeG FML Σ}.

  (** A body that has run to a value is well typed under any continuation
    context: [cont_postcondition] is [True], so there is nothing left to
    prove.  This is what closes a body when the continuation context is
    empty, as it is in [typing/soundness.v]'s two theorems. *)
  Lemma type_done {𝔄l 𝔅} E L I (C: cctx 𝔅) (T: tctx 𝔄l) (v: val) tr :
    ⊢ typed_body E L I C T (of_val v) tr.
  Proof.
    rewrite /typed_body. iIntros (?????) "_ _ _ _ _ _ _ _ _".
    iApply twp_value. by rewrite /cont_postcondition.
  Qed.

  (** [let x = 42 in ()]: the smallest program that binds a typed value.

    Note the rule used.  [programs.v]'s generic [type_val] has [let: xb := v
    in e] in its conclusion for a *value* [v], so applying it to a concrete
    program asks unification to invert [of_val ?v] against a literal, which
    does not terminate here.  Every type's own rule - [int.v]'s [type_int],
    [bool.v]'s [type_bool] - puts the literal in the conclusion directly and
    applies first-order.  Upstream's [typing/examples/] never applies
    [type_val] either. *)
  Definition bind_int : expr := (let: "x" := #42 in #☠)%E.

  Lemma bind_int_typed {𝔅} E L I (C: cctx 𝔅) (tr: predl_trans' [Zₛ] 𝔅) :
    ⊢ typed_body E L I C +[] bind_int (λ post al, tr post (42%Z -:: al)).
  Proof.
    rewrite /bind_int.
    iApply type_int; last first.
    { iIntros (v'). simpl_subst. iApply (type_done _ _ _ _ _ (#☠ : val)). }
    all: solve_closed.
  Qed.

  (** Hence the trivial specification, which is the shape [type_soundness]
    asks for: every postcondition holds. *)
  Lemma bind_int_typed_true {𝔅} E L I (C: cctx 𝔅) :
    ⊢ typed_body E L I C +[] bind_int (λ _ _ _ _, True%type).
  Proof. exact (bind_int_typed _ _ _ _ (λ _ _ _ _, True%type)). Qed.
  (** [let a = 1 in let b = 2 in let c = a + b in ()]: two typed bindings
    and an operation that reads them back out of the type context.  The
    transformer is built forward into an evar by applying [typed_body_impl]
    first, which is how upstream's examples keep the composite out of the
    statement. *)
  Definition add_ints : expr :=
    (let: "a" := #1 in let: "b" := #2 in let: "c" := "a" + "b" in #☠)%E.

  Lemma add_ints_typed {𝔅} E L I (C: cctx 𝔅) :
    ⊢ typed_body E L I C +[] add_ints (λ _ _ _ _, True%type).
  Proof.
    rewrite /add_ints.
    iApply (typed_body_impl with "[]"); last first.
    { iApply type_int; last first.
      { iIntros (v1). simpl_subst.
        iApply type_int; last first.
        { iIntros (v2). simpl_subst.
          iApply type_plus; last first.
          { iIntros (v3). simpl_subst.
            iApply (type_done _ _ _ _ _ (#☠ : val)
              (λ _ _ _ _, True%type)). }
          all: solve_typing. }
        all: solve_closed. }
      all: solve_closed. }
    { by move=> *. }
  Qed.
End basic.
