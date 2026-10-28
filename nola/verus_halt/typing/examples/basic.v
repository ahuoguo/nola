(** * A first worked example

  [nola/examples/rust_halt/verify/] verifies its programs against the typing
  rules while staying parametric in the constructor signature [CON] and the
  judgment type [JUDG] - [type_total] is never applied there - and so does
  this.  The instance that keeps the soundness theorems from being vacuous is
  [typing/inst.v]'s [verus_halt_sem]; what this file does is exercise the typing
  rules themselves. *)

From nola.verus_halt.lang Require Import notation proofmode.
From nola.verus_halt.typing Require Export int programs own uninit uniq_bor.
From nola.verus_halt.lang.lib Require Import new_delete.
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
  (** [let b = new 1 in delete 1 b; ()]: a box allocated, then freed.

    Note the explicit [1] and ["b"].  [type_new]'s statement binds
    [let n' := Z.to_nat n in] and uses [n'] in the continuation's type
    context, so leaving [n] to unification makes the [iApply] diverge -
    [Timeout 60] on it fails - while passing it is instant.  Upstream's
    [typing/examples/] passes the size to [type_new_subtype] for the same
    reason.

    Note also that the [Closed] side conditions of [type_new] and
    [type_delete] are discharged by type class resolution before the
    brackets are reached, so a [solve_closed] branch would be applied to the
    *next* goal instead; that is what the stray "No matching clauses for
    match" was. *)
  Definition box_roundtrip : expr :=
    (let: "b" := new_delete.new [ #1 ] in
     new_delete.delete [ #1; "b" ];; #☠)%E.

  Lemma box_roundtrip_typed {𝔅} E L I (C: cctx 𝔅) :
    ⊢ typed_body E L I C +[] box_roundtrip (λ _ _ _ _, True%type).
  Proof.
    rewrite /box_roundtrip.
    iApply (typed_body_impl with "[]"); last first.
    { iApply (type_new 1 "b"); [lia|].
      iIntros (v). simpl_subst.
      iApply (type_delete (↯ (Z.to_nat 1)) (Z.to_nat 1) 1 v);
        [solve_typing|done|done|].
      iApply (type_done _ _ _ _ _ (#☠ : val) (λ _ _ _ _, True%type)). }
    { by move=> *. }
  Qed.
  (** [let b = new 1 in let x = 42 in b <- x; delete 1 b; ()]: the box is
    written before it is freed, which is what brings [own_ptr]'s
    [typed_write] into play.

    [type_assign] takes *both* operands out of the type context, so the
    integer has to be bound first - hence the second [let].  [write_own]
    turns the [↯ 1] the allocation produced into an [int], and the
    [delete] then has to be given [int] rather than [↯ 1]. *)
  Definition box_write : expr :=
    (let: "b" := new_delete.new [ #1 ] in
     let: "x" := #42 in
     "b" <- "x";;
     new_delete.delete [ #1; "b" ];; #☠)%E.

  Lemma box_write_typed {𝔅} E L I (C: cctx 𝔅) :
    ⊢ typed_body E L I C +[] box_write (λ _ _ _ _, True%type).
  Proof.
    rewrite /box_write.
    iApply (typed_body_impl with "[]"); last first.
    { iApply (type_new 1 "b"); [lia|].
      iIntros (vb). simpl_subst.
      iApply type_int; last first.
      { iIntros (vx). simpl_subst.
        iApply (type_assign (own_ptr 1 (↯ (Z.to_nat 1))) (↯ (Z.to_nat 1))
          (own_ptr 1 int) int);
          [solve_typing|by apply write_own|solve_typing|].
        iApply (type_delete int (Z.to_nat 1) 1 vb);
          [solve_typing|done|done|].
        iApply (type_done _ _ _ _ _ (#☠ : val) (λ _ _ _ _, True%type)). }
      all: solve_closed. }
    { by move=> *. }
  Qed.

  (** The relaxed borrow, as a subtyping fact.

    [typing/uniq_bor.v]'s [uniq_subtype] has *no* extra premise: shortening
    the lifetime of a unique borrow needs only [κ' ⊑ κ] and an equality of
    the borrowed types.  It used to need the borrowed type's own ghost
    assertion to be *semantically closed*, which is a condition no interesting
    type satisfies; the relaxed borrow of the thesis's § 6.4 is what removed
    it, and [uniq_uniq_subtype] below - a unique borrow of a unique borrow,
    where the inner type is itself a borrow - is the case that could not be
    stated before. *)
  Lemma uniq_shorten_int E L κ κ' :
    lctx_lft_incl E L κ' κ →
    subtype E L (&uniq{κ} int) (&uniq{κ'} int) idₛ.
  Proof. move=> ?. apply uniq_subtype; [done|]. apply eqtype_refl. Qed.

  Lemma uniq_shorten_uniq E L κ κ' κ0 :
    lctx_lft_incl E L κ' κ →
    subtype E L (&uniq{κ} (&uniq{κ0} int)) (&uniq{κ'} (&uniq{κ0} int)) idₛ.
  Proof. move=> ?. apply uniq_subtype; [done|]. apply eqtype_refl. Qed.
End basic.
