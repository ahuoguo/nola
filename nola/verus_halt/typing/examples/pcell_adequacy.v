(** * [pcell_example], end to end

  Ported from VerusBelt ([typing/examples/pcell_example.v]'s
  [pcell_example_executes_without_getting_stuck], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  The statement upstream ends on, and the one the whole development is
  for: a sentence about the operational behaviour of a concrete program,
  mentioning no Iris, no typing rule and no ghost state.  Upstream gets
  it from [type_soundness_closed]; here it is
  [typing/soundness.v]'s [type_safety_main], which has upstream's shape
  and became statable only once [fn] had an interpretation.

  And one sentence upstream cannot make.  Its weakest precondition is
  partial, because a guard there hands out a [▷] that only a later
  credit can pay for; this port's is total, so the same hypothesis also
  gives **termination** - [pcell_example_terminates] below. *)

From nola.verus_halt.typing Require Import inst.
From nola.verus_halt.typing.examples Require Import pcell_example.
From nola.verus_halt.lang Require Import races.

(** The model's [FnFml] is [typing/function.v]'s flat one, not
  [typing/fn_inst.v]'s stratified one, and the reason is the shape of the
  hypothesis rather than anything about the program: [type_safety_main]
  quantifies over *every* [verus_haltGS], while the stratified instance
  exists at the ones [typing/level_ctx.v]'s family builds,
  [verus_haltGS_of hLlft hGS hP hU n].  Those are the only ones
  [verus_halt_wsat_alloc] ever produces, so the restriction is in the
  statement and not in the mathematics.  See [typing/fn_inst.v]'s header
  for what the two instances differ in. *)
Section pcell_adequacy.
  Context {Σ} `{!verus_haltGpreS (cifOF verus_haltCON) Σ}.

  Local Lemma pcell_example_typed :
    ∀ H : verus_haltGS (cifOF verus_haltCON) Σ,
      ∃ (_ : Csem verus_haltCON (verus_haltJUDG Σ) Σ)
        (_ : Jsem (verus_haltJUDG Σ) (iProp Σ))
        (_ : typingCS verus_haltCON (verus_haltJUDG Σ) Σ)
        (_ : typingJS verus_haltCON (verus_haltJUDG Σ) Σ)
        (_ : FnFml),
      typed_val pcell_example main_type (pcell_example, ()).
  Proof.
    move=> H. exists verus_haltCsem, verus_haltJsem, typingCS_CON,
      typingJS_JUDG, fnFml_flat.
    exact pcell_example_type.
  Qed.

  (** Upstream's conclusion: no data race, and no thread stuck. *)
  Theorem pcell_example_executes_without_getting_stuck σ t :
    rtc erased_step ([pcell_example [exit_cont]%E], (∅, false)) (t, σ) →
    nonracing_threadpool t σ ∧
      (∀ e, e ∈ t → is_Some (to_val e) ∨ reducible e σ).
  Proof.
    apply (type_safety_main pcell_example (pcell_example, ())).
    exact pcell_example_typed.
  Qed.

  (** And the one the later-free port adds. *)
  Theorem pcell_example_terminates :
    sn erased_step ([pcell_example [exit_cont]%E], (∅, false)).
  Proof.
    apply (type_soundness_main pcell_example (pcell_example, ())).
    exact pcell_example_typed.
  Qed.
End pcell_adequacy.

Print Assumptions pcell_example_executes_without_getting_stuck.
Print Assumptions pcell_example_terminates.
