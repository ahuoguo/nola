(** * Eternal resources: a persistent guard with no token to give back

  Leaf's [guards_alloc] turns a proposition into a *persistent* guard
  [□ (True &&{↑N}&&> ▷ P)] by allocating an Iris invariant, and VerusBelt uses
  it once, in [typing/lifetime.v]'s [lft_eternalize], to make a lifetime token
  live forever.

  Later-free the content of a world satisfaction is syntactic, so storing an
  arbitrary [iProp] is not available.  But nothing here needs to be arbitrary:
  what is eternalized is always [f k] for a fixed interpretation [f] and a
  *countable key* [k], so the world satisfaction can hold
  [[∗ set] k ∈ S, f k] with an authoritative [S] and hand out [◯ {[k]}] as the
  (persistent, duplicable) token.  No formula language is needed, and
  [eternal_tok_guard] carries no later. *)

From nola.bi Require Export guard modw.
From nola.iris Require Export iprop.
From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
Import GuardNotation.

Section eternal.
  Context `{!EqDecision K, !Countable K, !inG Σ (authUR (gsetUR K))}.
  Implicit Type (γ : gname) (k : K) (f : K → iProp Σ) (P : iProp Σ).

  (** World satisfaction holding the eternalized resources *)
  Definition eternal_wsat γ f : iProp Σ :=
    ∃ S, own γ (● S) ∗ [∗ set] k ∈ S, f k.
  (** The persistent token saying [k] has been eternalized *)
  Definition eternal_tok γ k : iProp Σ := own γ (◯ {[k]}).

  #[export] Instance eternal_tok_persistent {γ k} :
    Persistent (eternal_tok γ k).
  Proof. exact _. Qed.
  #[export] Instance eternal_tok_timeless {γ k} : Timeless (eternal_tok γ k).
  Proof. exact _. Qed.

  (** Allocate the world satisfaction, with the interpretation left open *)
  Lemma eternal_wsat_alloc : ⊢ |==> ∃ γ, ∀ f, eternal_wsat γ f.
  Proof.
    iMod (own_alloc (● (∅ : gsetUR K))) as (γ) "●";
      [by apply auth_auth_valid|].
    iModIntro. iExists γ. iIntros (f). iExists ∅. iFrame "●".
    by rewrite big_sepS_empty.
  Qed.

  (** Eternalize [f k] *)
  Lemma eternal_tok_alloc {γ f k} :
    f k -∗ eternal_wsat γ f ==∗ eternal_tok γ k ∗ eternal_wsat γ f.
  Proof.
    iIntros "fk [%S[● S]]".
    iMod (own_update _ _ (● (S ∪ {[k]}) ⋅ ◯ (S ∪ {[k]})) with "●") as "[● ◯]".
    { apply auth_update_alloc, gset_local_update. set_solver. }
    iAssert (own γ (◯ {[k]})) with "[◯]" as "#◯k".
    { iApply (own_mono with "◯"). apply auth_frag_mono, gset_included.
      set_solver. }
    iModIntro. iFrame "◯k". iExists (S ∪ {[k]}). iFrame "●".
    case (decide (k ∈ S))=> [?|?].
    - have -> : S ∪ {[k]} = S by set_solver. iFrame "S".
    - rewrite big_sepS_union; [|set_solver]. rewrite big_sepS_singleton.
      iFrame.
  Qed.

  (** An eternalized resource is guarded by anything, with no later *)
  Lemma eternal_tok_guard {γ f k P} :
    eternal_tok γ k ⊢ P &&{eternal_wsat γ f}&&> f k.
  Proof.
    rewrite /guard. iIntros "#◯ !>" (T) "[P toWT]".
    iDestruct ("toWT" with "P") as "[[%S[● S]] T]".
    iDestruct (own_valid_2 with "● ◯") as %[inc ?]%auth_both_valid_discrete.
    move: inc=> /gset_included ?.
    iDestruct (big_sepS_elem_of_acc _ _ k with "S") as "[$ →S]";
      [set_solver|].
    iIntros "fk". iFrame "T". iExists S. iFrame "●". by iApply "→S".
  Qed.
End eternal.
