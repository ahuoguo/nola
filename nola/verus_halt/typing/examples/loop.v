(** * A loop, and why it terminates

  [typing/recursion.v]'s [type_cont_wf] at work.  The program is a
  countdown: a continuation that takes an integer, stops once it has
  reached zero, and otherwise jumps to itself with one less.  Nothing
  about it is interesting except that it is a *loop* - the port could not
  type one at all before, because [typing/cont.v]'s recursive [type_cont]
  is proved by [iLöb] upstream and a total weakest precondition has no
  Löb rule.

  What replaces Löb is the measure.  [cd_lvl] reads the loop variable off
  the continuation's own argument refinement, [lt] is the order, and
  [Wf_nat.lt_wf] is the whole termination argument: the jump at the end of
  the body has to establish [cd_lvl -[z-1] < cd_lvl -[z]], and the only
  thing that discharges it is the branch condition that got us there.
  Change the decrement to [- #0] and the [lia] on the last line of
  [countdown_typed] fails - "Cannot find witness" - which is the property
  a Löb-based rule does not have: with Löb the same program would still
  be typable, and would still not terminate. *)

From nola.verus_halt.lang Require Import notation proofmode.
From nola.verus_halt.typing Require Export int bool programs cont recursion.
From nola.verus_halt.typing Require Import inst soundness.
From nola.verus_halt.typing.examples Require Import basic.
From nola.bi Require Import modw.
Import ModwNotation WpwNotation.

Open Scope Z_scope.

(** [let n = 10 in while n > 0 { n -= 1 }], as a continuation *)
Definition countdown : expr :=
  (letcont: "k" ["n"] :=
     (let: "z" := #0 in
      let: "b" := "n" ≤ "z" in
      if: "b" then #☠
      else (let: "o" := #1 in
            let: "m" := "n" - "o" in
            jump: "k" ["m"]))
   in (let: "s" := #10 in jump: "k" ["s"]))%E.

Section loop.
  Context `{!typeG FML Σ}.

  (** The continuation's argument context, measure and specification.  The
    specification is trivial - this program computes nothing - so the only
    content of the typing is that it stops. *)
  Definition cd_tctx (vl: vec val 1) : tctx [Zₛ] := +[vhd vl ◁ int].
  Definition cd_lvl (xl: plist indep_interp_of_syn_type [Zₛ]) : nat :=
    let '(z -:: _) := xl in Z.to_nat z.
  Definition cd_spec {𝔅} : predl_trans' [Zₛ] 𝔅 := λ _ _ _ _, True%type.

  Lemma countdown_typed {𝔅} E L (I: invctx) (C: cctx 𝔅) :
    ⊢ typed_body E L I C +[] countdown (λ _ _ _ _, True%type).
  Proof.
    rewrite /countdown.
    iApply (type_cont_wf (A:=nat) (𝔄l:=[]) lt [BNamed "n"] cd_tctx cd_lvl
      (cd_spec (𝔅:=𝔅)) 11%nat L I).
    { exact Wf_nat.lt_wf. }
    all: try solve_closed.
    (** The loop body, at an arbitrary stage [a] *)
    { move=> a k vl.
      inv_vec vl=> vn.
      rewrite /subst_v /= /cd_tctx /=.
      simpl_subst.
      iApply (typed_body_impl with "[]"); last first.
      { iApply type_int.
        iIntros (vz).
        simpl_subst.
        iApply type_le.
        { solve_typing. }
        iIntros (vb).
        simpl_subst.
        iApply type_if.
        { solve_typing. }
        (** [n ≤ 0]: the loop is over *)
        { iApply (type_done _ _ _ _ _ (#☠ : val) (λ _ _ _ _, True%type)). }
        (** [n > 0]: decrement and jump, one stage down *)
        iApply type_int.
        iIntros (vo).
        simpl_subst.
        iApply type_minus.
        { solve_typing. }
        iIntros (vm).
        simpl_subst.
        iApply type_jump.
        { by apply list_elem_of_here. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. } }
      (** The one pure obligation, and the only place termination is
        argued: in the [else] branch [bool_decide (z ≤ 0)] is [false], so
        [z > 0], so [Z.to_nat (z - 1) < Z.to_nat z]. *)
      move=> post [z[]] mask π.
      rewrite /cd_lvl /cd_spec /cont_at /cont_lt /=.
      move=> [<-_].
      case_bool_decide as Hz; [done|].
      split; [lia|done]. }
    (** Entering the loop: [10] is below the starting stage [11]. *)
    iIntros (k).
    rewrite /cd_tctx /=.
    simpl_subst.
    iApply (typed_body_impl with "[]"); last first.
    { iApply type_int.
      iIntros (vs).
      simpl_subst.
      iApply type_jump.
      { by apply list_elem_of_here. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. } }
    move=> post [] mask π _.
    rewrite /cd_lvl /cd_spec /cont_lt /=.
    split; [compute; lia|done].
  Qed.
End loop.

(** * End to end

  [typing/soundness.v]'s [type_soundness] at the concrete model, in the
  shape [typing/examples/pcell_adequacy.v] has it.  The conclusion
  mentions no Iris, no typing rule and no ghost state - and it is a
  *termination* statement, which is the whole reason the recursive
  continuation rule had to be well founded rather than a Löb step. *)
Section loop_adequacy.
  Context {Σ} `{!verus_haltGpreS (cifOF verus_haltCON) Σ}.

  Local Lemma countdown_typed_inst :
    ∀ H : verus_haltGS (cifOF verus_haltCON) Σ,
      ∃ (_ : Csem verus_haltCON (verus_haltJUDG Σ) Σ)
        (_ : Jsem (verus_haltJUDG Σ) (iProp Σ))
        (_ : typingCS verus_haltCON (verus_haltJUDG Σ) Σ)
        (_ : typingJS verus_haltCON (verus_haltJUDG Σ) Σ),
      ⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx unitₛ)
          +[] countdown (λ _ _ _ _, True%type).
  Proof.
    move=> H. exists verus_haltCsem, verus_haltJsem, typingCS_CON,
      typingJS_JUDG.
    exact (countdown_typed [] [] (InvCtx [] static AtomicClosed) []).
  Qed.

  Theorem countdown_terminates :
    sn erased_step ([countdown], (∅, false)).
  Proof.
    apply (type_soundness (𝔅:=unitₛ) _ (λ _ _ _ _, True%type)); [done|].
    exact countdown_typed_inst.
  Qed.
End loop_adequacy.

Print Assumptions countdown_typed.
Print Assumptions countdown_terminates.
