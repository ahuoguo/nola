(** * A two-state exclusive token, and the guard narrowing it buys

  PLAN.md records a dead end: the port has *two* owning pointers,
  [own_ptr] whose content is in hand and extractable but which is not
  productive, and [rec.v]'s [sown_tyd] whose content is in a simple
  invariant and productive but not extractable.  The obvious merge is to
  store [Px ∨ token] and hold the token, so that the guard rules the
  right disjunct out while extraction deposits it.

  That was recorded as *structurally* impossible, and the argument was:
  narrowing a guard on a disjunction needs [guard_or_false], whose side
  condition is a guard on [False] and so sits under a [□] that an owned
  token cannot discharge; or [guard_cancel_or], whose side condition is
  [Q ∧ R ⊢ False], which "two copies of the same exclusive resource do
  not give - [P ∧ P ⊣⊢ P]".

  The second half of that is right about *two copies of one* token and
  wrong about the method.  [guard_cancel_or]'s conjunction is the
  non-separating one, and for two **different and incompatible** states
  at one ghost name it does give a contradiction - which is exactly what
  Iris's [own_and] is for, and what [nola/alerus/own_and.v] already
  bridges.  One name, two states:

    [ts_full γ]  := [own γ (Cinl (Excl ()))]   the content is inside
    [ts_taken γ] := [own γ (Cinr (Excl ()))]   it has been extracted

  [Cinl] and [Cinr] are not ordered by [≼] and their composition is
  [CsumBot], so no *valid* resource includes both: [ts_and_false].  The
  token is still exclusive, so extraction is a frame-preserving update
  from one state to the other ([ts_take]), and what it deposits in the
  store is the very thing that falsifies the guard.

  So the obstruction is not structural.  What remains to merge the two
  pointers is the ordinary work of rewriting [sown_tyd] around this
  token; [guard_two_state] below is the step that was thought
  unavailable. *)

From nola Require Export prelude.
From nola.bi Require Export guard.
From iris.algebra Require Import csum excl.
From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import proofmode.
Import GuardNotation.

(** The camera: one exclusive token with two distinguishable states *)
Definition twostateR : cmra := csumR (exclR unitO) (exclR unitO).

Class twostateG Σ := twostate_in : inG Σ twostateR.
Local Existing Instance twostate_in.
Definition twostateΣ : gFunctors := #[GFunctor twostateR].
#[export] Instance subG_twostateΣ `{!subG twostateΣ Σ} : twostateG Σ.
Proof. solve_inG. Qed.

Section two_state.
  Context `{!twostateG Σ}.
  Implicit Type γ : gname.

  (** The content is still inside *)
  Definition ts_full γ : iProp Σ := own γ (Cinl (Excl ())).
  (** The content has been extracted *)
  Definition ts_taken γ : iProp Σ := own γ (Cinr (Excl ())).

  (** *** The two states exclude each other, *non-separatingly*

    This is the lemma the dead end turned on.  [own_and] gives a common
    upper bound [c] of the two states; [Cinl] and [Cinr] are incomparable
    and their join is [CsumBot], so no valid [c] bounds both. *)
  Lemma ts_and_false γ : ts_full γ ∧ ts_taken γ ⊢ False.
  Proof.
    rewrite /ts_full /ts_taken own_and.
    iIntros "(%c & own & %Hl & %Hr)".
    iDestruct (own_valid with "own") as "%Hv".
    iPureIntro. destruct c as [x|x|]; [| |done].
    - apply Some_csum_included in Hr. naive_solver.
    - apply Some_csum_included in Hl. naive_solver.
  Qed.

  (** Separating exclusion follows, and each state is exclusive *)
  Lemma ts_sep_false γ : ts_full γ ∗ ts_taken γ ⊢ False.
  Proof. rewrite bi.sep_and. apply ts_and_false. Qed.
  Lemma ts_full_excl γ : ts_full γ ∗ ts_full γ ⊢ False.
  Proof.
    rewrite /ts_full -own_op. by iIntros "own";
      iDestruct (own_valid with "own") as "%".
  Qed.
  Lemma ts_taken_excl γ : ts_taken γ ∗ ts_taken γ ⊢ False.
  Proof.
    rewrite /ts_taken -own_op. by iIntros "own";
      iDestruct (own_valid with "own") as "%".
  Qed.

  #[export] Instance ts_full_timeless {γ} : Timeless (ts_full γ).
  Proof. exact _. Qed.
  #[export] Instance ts_taken_timeless {γ} : Timeless (ts_taken γ).
  Proof. exact _. Qed.

  (** Allocation, and extraction as a frame-preserving update *)
  Lemma ts_alloc : ⊢ |==> ∃ γ, ts_full γ.
  Proof. by iApply own_alloc. Qed.

  Lemma ts_take γ : ts_full γ ==∗ ts_taken γ.
  Proof.
    rewrite /ts_full /ts_taken. iApply own_update.
    by apply cmra_update_exclusive.
  Qed.

  (** *** The narrowing that was thought unavailable

    A guard on [ts_taken γ ∨ Px], together with the holder's own
    [ts_full γ], is a guard on [Px].  Nothing here is under a [□] that
    needs the token: [guard_cancel_or]'s side condition is the pure
    [ts_and_false], and the token enters only through the guard's own
    left-hand side, which is supplied at use. *)
  Lemma guard_two_state {W P Px : iProp Σ} γ :
    (P &&{W}&&> ts_full γ) -∗ (P &&{W}&&> (ts_taken γ ∨ Px)) -∗
    P &&{W}&&> Px.
  Proof.
    iIntros "g1 g2". iApply (guard_cancel_or with "g1 g2").
    apply ts_and_false.
  Qed.

  (** The common shape: the holder *is* the token. *)
  Lemma guard_two_state_tok {W Px : iProp Σ} γ :
    (ts_full γ &&{W}&&> (ts_taken γ ∨ Px)) -∗ ts_full γ &&{W}&&> Px.
  Proof. iIntros "g". iApply (guard_two_state with "[] g"). iApply guard_refl. Qed.

  (** *** What this does and does not buy

    It buys the **reversible accessor** on a guarded disjunction: hold the
    token, get the content, give it back, get the token back. *)
  Lemma ebox_acc {W Px : iProp Σ} γ :
    (ts_full γ &&{W}&&> (ts_taken γ ∨ Px)) -∗ ts_full γ -∗ W -∗
      Px ∗ (Px -∗ W ∗ ts_full γ).
  Proof.
    iIntros "#g tok W". iDestruct (guard_two_state_tok with "g") as "#g'".
    iApply (guard_acc with "g' tok W").
  Qed.

  (** It does **not** buy extraction, and that is worth being exact about,
    because PLAN.md's dead end was about a merge that needs both.

    [guard_acc] is [Q ∗ (Q -∗ W ∗ P)]: the only route back to [W] consumes
    the content.  Keeping [Px] and still returning [W] is therefore not
    derivable from the guard, whatever the disjunction looks like - and
    that is by design, since a guard is precisely the thing that cannot
    write to the store.  Running [ts_take] and depositing [ts_taken γ]
    where the content was needs *write* access, i.e. the store token.

    So what this file settles is the obstruction PLAN.md recorded as
    **structural** - that no side condition could rule the marker
    disjunct out.  One can.  The remaining obstacle to merging the two
    owning pointers is the other one that file records, and it is not
    this one: a store *token* names the formula it stores, so a former
    holding one admits no subtyping rule.  Getting both extraction and
    subtyping needs the stored formula to be fixed with the variation
    behind a judgment, the way an indexed borrow's content is altered.
    That is a design question, not a structural impossibility. *)
End two_state.
