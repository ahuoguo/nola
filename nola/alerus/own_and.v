(** * Leaf-compatible names for Iris's [own_forall] family

  The Leaf library ([guarding/own_and.v], [guarding/own_and_own_sep.v]) proved
  that [own γ a1 ∧ own γ a2] yields a common upper bound.  That development has
  since been upstreamed into Iris as [own_forall] / [own_and] and friends, so
  the AlerusBelt port can drop those 830 lines entirely.

  Iris states the inclusions with the *internal* [≼] of [iris.bi.cmra], while
  Leaf's discrete versions state them purely.  This file bridges the two, under
  the names the ported files use. *)

From nola Require Export prelude.
From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import proofmode.

Section own_and.
  Context `{!inG Σ A, !CmraDiscrete A, !CmraTotal A}.
  Implicit Type (γ : gname) (a : A).

  (** Leaf's [and_own_discrete_ucmra] *)
  Lemma and_own_discrete_ucmra γ a1 a2 :
    own γ a1 ∧ own γ a2 ⊢ ∃ c, own γ c ∗ ⌜a1 ≼ c ∧ a2 ≼ c⌝.
  Proof.
    rewrite own_and_total. iIntros "[%c[own[in1 in2]]]". iExists c. iFrame "own".
    rewrite !internal_included_discrete. iDestruct "in1" as %?.
    iDestruct "in2" as %?. by iPureIntro.
  Qed.

  (** Leaf's [and_own_discrete_ucmra_specific] *)
  Lemma and_own_discrete_ucmra_specific γ a1 a2 c :
    (∀ c', ✓ c' → a1 ≼ c' → a2 ≼ c' → c ≼ c') →
    own γ a1 ∧ own γ a2 ⊢ own γ c.
  Proof. exact (own_and_discrete_total γ a1 a2 c). Qed.

  (** Leaf's [and_own_discrete_ucmra_contradiction] *)
  Lemma and_own_discrete_ucmra_contradiction γ a1 a2 :
    (∀ c', ✓ c' → a1 ≼ c' → a2 ≼ c' → False) →
    own γ a1 ∧ own γ a2 ⊢ False.
  Proof. exact (own_and_discrete_total_False γ a1 a2). Qed.
End own_and.

Section own_and_discrete.
  Context `{!inG Σ A, !CmraDiscrete A}.
  Implicit Type (γ : gname) (a : A).

  (** Leaf's [and_own_discrete]: the inclusions are stated in [option A], so
    that no [CmraTotal] is needed *)
  Lemma and_own_discrete γ a1 a2 :
    own γ a1 ∧ own γ a2 ⊢
      ∃ c, own γ c ∗ ⌜Some a1 ≼ Some c ∧ Some a2 ≼ Some c⌝.
  Proof.
    rewrite own_and. iIntros "[%c[own[in1 in2]]]". iExists c. iFrame "own".
    rewrite !internal_included_discrete. iDestruct "in1" as %?.
    iDestruct "in2" as %?. by iPureIntro.
  Qed.
End own_and_discrete.
