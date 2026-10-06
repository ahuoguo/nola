(** * Later-free boxes

  A reconstruction of Leaf's box library ([guarding/lib/boxes.v], itself a fork
  of Iris's [base_logic/lib/boxes.v]) without the later modality.

  Leaf had already replaced Iris's invariant [inv N (slice_inv γ P)] by a guard
  [True &&{↑N}&&> ▷ (slice_inv γ P)], but two laters remained, both artifacts of
  storing a proposition inside a resource:

    box_own_prop γ P := own γ (ε, Some (to_agree (Next P)))
    slice N γ P      := box_own_prop γ P ∗ (True &&{↑N}&&> ▷ (slice_inv γ P))
    box N f P        := ∃ Φ, ▷ (P ≡ [∗ map] γ↦_ ∈ f, Φ γ) ∗ …

  Both disappear here:

  - The [▷] on the guard goes away with the later-free guard of
    [nola.bi.guard], whose storage is a world satisfaction rather than an Iris
    invariant.
  - [Next] was only needed because [iProp Σ] cannot be stored in [Σ] directly.
    Nola's simple invariants store a *syntactic formula* [Px : FML $oi Σ]
    instead, so [box_own_agree] sharpens from [⊢ ▷ (Q1 ≡ Q2)] to [⊢ Px ≡ Qx].

  Consequently a slice *is* a simple-invariant token: [sinv_tok γ Px] already
  carries both the formula agreement that [box_own_prop] provided and, through
  [sinv_tok_guard], the guard.  Only the "filled" bit needs its own ghost state,
  and since slice names and [sinv] indices are both [positive], a slice name is
  its own [sinv] index. *)

From nola.bi Require Export guard.
From nola.iris Require Export sinv guard.
From nola.alerus Require Import auth_frag.
From iris.algebra Require Import excl_auth gmap.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.
Import GuardNotation ModwNotation iPropAppNotation.

Implicit Type (Σ : gFunctors) (FML : oFunctor).

(** Ghost state for the "filled" bit of a slice *)
Class boxG Σ := boxG_inG : inG Σ (excl_authR boolO).
Local Existing Instance boxG_inG.
Definition boxΣ : gFunctors := #[GFunctor (excl_authR boolO)].
#[export] Instance subG_boxΣ `{!subG boxΣ Σ} : boxG Σ.
Proof. solve_inG. Qed.

(** A slice name, which doubles as the index of the slice's simple invariant *)
Notation slice_name := positive (only parsing).

Section box.
  Context `{!boxG Σ, !sinvGS FML Σ}.
  Implicit Type (Px Qx : FML $oi Σ) (P Q : iProp Σ)
    (sm : FML $oi Σ → iProp Σ) (γ : slice_name) (f : gmap slice_name bool).

  (** ** Definitions *)

  (** Whether a slice is currently filled *)
  Definition box_own_auth γ (a : excl_authR boolO) : iProp Σ := own γ a.

  (** What a slice stores: the "filled" bit, and the contents when filled *)
  Definition slice_body sm γ Px : iProp Σ :=
    ∃ b, box_own_auth γ (●E b) ∗ if b then sm Px else True.

  (** The world satisfaction holding every slice *)
  Definition box_wsat sm : iProp Σ := sinv_wsat (λ γ Px, slice_body sm γ Px).

  (** A slice is a simple-invariant token *)
  Notation slice := sinv_tok (only parsing).

  (** A box: a finite collection of slices whose contents add up to [P] *)
  Definition box sm f P : iProp Σ :=
    ∃ Φx : slice_name → FML $oi Σ,
      (P ≡ [∗ map] γ ↦ _ ∈ f, sm (Φx γ)) ∗
      [∗ map] γ ↦ b ∈ f, box_own_auth γ (◯E b) ∗ sinv_tok γ (Φx γ).

  (** ** Basic properties *)

  #[export] Instance box_own_auth_timeless {γ a} : Timeless (box_own_auth γ a).
  Proof. exact _. Qed.

  Lemma box_own_auth_agree {γ b1 b2} :
    box_own_auth γ (●E b1) -∗ box_own_auth γ (◯E b2) -∗ ⌜b1 = b2⌝.
  Proof.
    iIntros "● ◯". iDestruct (own_valid_2 with "● ◯") as %?%excl_auth_agree_L.
    by iPureIntro.
  Qed.

  (** The same under the *non-separating* conjunction

    This is the rule the guard's conjunction machinery needs: the two halves
    are not separately owned, only jointly available under [∧]. *)
  Lemma box_own_auth_agree_and {γ b1 b2} :
    box_own_auth γ (◯E b1) ∧ box_own_auth γ (●E b2) ⊢ ⌜b1 = b2⌝.
  Proof.
    rewrite /box_own_auth own_and_total. iIntros "[%c[own[in1 in2]]]".
    iDestruct (own_valid with "own") as %?.
    rewrite !internal_included_discrete. iDestruct "in1" as %?.
    iDestruct "in2" as %?. iPureIntro.
    have : Excl' b1 ≼ Excl' b2 by apply: auth_frag_incl.
    by rewrite Excl_included.
  Qed.

  Lemma box_own_auth_update {γ b1 b2 b3} :
    box_own_auth γ (●E b1) -∗ box_own_auth γ (◯E b2) ==∗
      box_own_auth γ (●E b3) ∗ box_own_auth γ (◯E b3).
  Proof.
    iIntros "● ◯". rewrite /box_own_auth -!own_op.
    iApply (own_update_2 with "● ◯"). apply excl_auth_update.
  Qed.

  (** Slices agree on their formulas, with no later *)
  Lemma slice_agree {γ Px Qx} : sinv_tok γ Px -∗ sinv_tok γ Qx -∗ Px ≡ Qx.
  Proof. exact sinv_tok_agree. Qed.

  (** A slice guards its own contents, with no later *)
  Lemma slice_guard {sm γ Px} :
    sinv_tok γ Px ⊢ True &&{box_wsat sm}&&> slice_body sm γ Px.
  Proof. exact sinv_tok_guard. Qed.

  (** ** The headline rule: a full box guards each of its slices

    Leaf's [box_guard], whose conclusion was [box N f P &&{↑N}&&> ▷ Q]. *)
  Lemma box_guard {sm f P γ Px} : f !! γ = Some true →
    sinv_tok γ Px ⊢ box sm f P &&{box_wsat sm}&&> sm Px.
  Proof.
    move=> full. iIntros "#slice".
    (* Start from the slice's own guard, weakening its left-hand side *)
    iDestruct (slice_guard (sm:=sm) with "slice") as "#g".
    iAssert (box sm f P &&{box_wsat sm}&&> slice_body sm γ Px)%I as "#g1".
    { iApply (guard_trans with "[] g"). iApply guard_true. }
    (* The box owns [◯E true] for γ, so the slice's bit must be [true] *)
    rewrite /slice_body.
    iDestruct (guard_exist_strengthen_lhs
      (S := λ b, ⌜b = true⌝%I) with "g1") as "#g2".
    { move=> b. iIntros "big".
      iAssert (box_own_auth γ (◯E true) ∧ box_own_auth γ (●E b))%I
        with "[big]" as "and".
      { iSplit.
        - iDestruct "big" as "[[%Φx[_ big]] _]".
          rewrite (big_sepM_delete _ f γ true full).
          by iDestruct "big" as "[[$ _]_]".
        - by iDestruct "big" as "[_[$ _]]". }
      iDestruct (box_own_auth_agree_and with "and") as %?. by iPureIntro. }
    (* With the bit known to be [true], the contents are [sm Px] *)
    iApply (guard_trans with "g2"). iApply guard_intro.
    iIntros "!> [%b[[● Px]->]]". iDestruct "Px" as "$". iIntros "Px".
    iExists true. by iFrame.
  Qed.

  (** ** Allocation *)

  (** Add a fresh, empty slice to a box

    Leaf's [slice_insert_empty].  The Iris mask [={E}=∗] becomes an update with
    the box's world satisfaction. *)
  Lemma slice_insert_empty {sm f P} Qx :
    box sm f P -∗ |=[box_wsat sm]=> ∃ γ, ⌜f !! γ = None⌝ ∗
      sinv_tok γ Qx ∗ box sm (<[γ:=false]> f) (sm Qx ∗ P).
  Proof.
    iIntros "[%Φx[#eq big]] W". rewrite /box_wsat.
    iDestruct (sinv_tok_alloc_suspend Qx with "W") as (I) "toW".
    iMod (own_alloc_cofinite (●E false ⋅ ◯E false) (I ∪ dom f)) as (γ) "[%nin ●◯]";
      [by apply excl_auth_valid|].
    rewrite own_op. iDestruct "●◯" as "[● ◯]".
    have nin' : γ ∉ I by set_solver.
    have eqγ : f !! γ = None by apply not_elem_of_dom; set_solver.
    iMod ("toW" $! γ nin') as "[#tok toW]".
    iDestruct ("toW" with "[●]") as "$"; [by iExists false; iFrame|].
    iModIntro. iExists γ. iSplit; [done|]. iFrame "tok".
    iExists (λ δ, if decide (δ = γ) then Qx else Φx δ). iSplitR.
    - have Heq : ([∗ map] δ ↦ _ ∈ <[γ:=false]> f,
          sm (if decide (δ = γ) then Qx else Φx δ)) ⊣⊢
          sm Qx ∗ [∗ map] δ ↦ _ ∈ f, sm (Φx δ).
      { rewrite big_sepM_insert; [|done]. rewrite decide_True; [|done].
        f_equiv. apply big_sepM_proper=> δ ? lk. rewrite decide_False; [done|].
        move=> ?. subst. by rewrite eqγ in lk. }
      rewrite Heq. iRewrite "eq".
      iApply (internal_eq_refl emp). done.
    - rewrite big_sepM_insert; [|done]. rewrite decide_True; [|done]. iFrame "◯ tok".
      iApply (big_sepM_mono with "big")=> δ ? lk /=. rewrite decide_False; [done|].
      move=> ?. subst. by rewrite eqγ in lk.
  Qed.

  Lemma box_alloc `{!Inhabited (FML $oi Σ)} {sm} : ⊢ box sm ∅ emp.
  Proof.
    rewrite /box. iExists (λ _, inhabitant). rewrite !big_sepM_empty.
    iSplit; [|done]. iApply (internal_eq_refl emp). done.
  Qed.
End box.
