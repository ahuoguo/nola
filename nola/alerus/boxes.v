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

  (** [box] is non-expansive in its contents

    Leaf's [box] is *contractive* thanks to the [▷] in its definition; without
    the later we only get non-expansiveness, which is all that the internal
    rewriting in [slice_split] / [slice_combine] needs. *)
  #[export] Instance box_ne {sm f} : NonExpansive (box sm f).
  Proof. rewrite /box. solve_proper. Qed.
  #[export] Instance box_proper {sm f} : Proper ((≡) ==> (≡)) (box sm f).
  Proof. apply ne_proper, _. Qed.

  (** Access a slice through the box's world satisfaction *)
  Lemma slice_acc {sm γ Px} :
    sinv_tok γ Px -∗ box_wsat sm -∗
      slice_body sm γ Px ∗ (slice_body sm γ Px -∗ box_wsat sm).
  Proof. exact sinv_tok_acc. Qed.

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

  (** Remove an empty slice from a box *)
  Lemma slice_delete_empty `{!NonExpansive sm} {f P γ Px} : f !! γ = Some false →
    sinv_tok γ Px -∗ box sm f P -∗ |=[box_wsat sm]=> ∃ P',
      (P ≡ (sm Px ∗ P')) ∗ box sm (delete γ f) P'.
  Proof.
    move=> eqγ. iIntros "#tok [%Φx[#eq big]] W".
    iDestruct (slice_acc with "tok W") as "[[%b[● _]] toW]".
    iDestruct (big_sepM_delete _ f _ false with "big") as "[[◯ #tok'] big]";
      [done|].
    iDestruct (box_own_auth_agree with "● ◯") as %->.
    iDestruct ("toW" with "[●]") as "W"; [rewrite /slice_body; by iExists false; iFrame|].
    iDestruct (slice_agree with "tok' tok") as "#eqx". iModIntro. iFrame "W".
    iExists ([∗ map] δ ↦ _ ∈ delete γ f, sm (Φx δ))%I. iSplitR.
    - iRewrite "eq". rewrite (big_opM_delete _ f γ false eqγ). iRewrite -"eqx".
      by iApply (internal_eq_refl emp).
    - iExists Φx. iFrame "big". by iApply (internal_eq_refl emp).
  Qed.

  (** Fill an empty slice *)
  Lemma slice_fill {sm f P γ Px} : f !! γ = Some false →
    sinv_tok γ Px -∗ sm Px -∗ box sm f P -∗
      |=[box_wsat sm]=> box sm (<[γ:=true]> f) P.
  Proof.
    move=> eqγ. iIntros "#tok Px [%Φx[#eq big]] W".
    iDestruct (slice_acc with "tok W") as "[[%b[● _]] toW]".
    iDestruct (big_sepM_delete _ f _ false with "big") as "[[◯ #tok'] big]";
      [done|].
    iMod (box_own_auth_update (b3:=true) with "● ◯") as "[● ◯]".
    iDestruct ("toW" with "[● Px]") as "W"; [rewrite /slice_body; by iExists true; iFrame|].
    iModIntro. iFrame "W". iExists Φx. iSplitR.
    { by rewrite big_opM_insert_override. }
    rewrite -insert_delete_eq big_opM_insert; [|by rewrite lookup_delete_eq].
    iFrame "◯ tok' big".
  Qed.

  (** Empty a full slice *)
  Lemma slice_empty `{!NonExpansive sm} {f P γ Px} : f !! γ = Some true →
    sinv_tok γ Px -∗ box sm f P -∗
      |=[box_wsat sm]=> sm Px ∗ box sm (<[γ:=false]> f) P.
  Proof.
    move=> eqγ. iIntros "#tok [%Φx[#eq big]] W".
    iDestruct (slice_acc with "tok W") as "[[%b[● Px]] toW]".
    iDestruct (big_sepM_delete _ f _ true with "big") as "[[◯ #tok'] big]";
      [done|].
    iDestruct (box_own_auth_agree with "● ◯") as %->.
    iMod (box_own_auth_update (b3:=false) with "● ◯") as "[● ◯]".
    iDestruct ("toW" with "[●]") as "W"; [rewrite /slice_body; by iExists false; iFrame|].
    iModIntro. iFrame "W Px". iExists Φx. iSplitR.
    { by rewrite big_opM_insert_override. }
    rewrite -insert_delete_eq big_opM_insert; [|by rewrite lookup_delete_eq].
    iFrame "◯ tok' big".
  Qed.

  (** Add a fresh, full slice to a box *)
  Lemma slice_insert_full `{!NonExpansive sm} {f P} Qx :
    sm Qx -∗ box sm f P -∗ |=[box_wsat sm]=> ∃ γ, ⌜f !! γ = None⌝ ∗
      sinv_tok γ Qx ∗ box sm (<[γ:=true]> f) (sm Qx ∗ P).
  Proof.
    iIntros "Qx box".
    iMod (slice_insert_empty Qx with "box") as (γ eqγ) "[#tok box]".
    iMod (slice_fill with "tok Qx box") as "box"; [by rewrite lookup_insert_eq|].
    iModIntro. iExists γ. iFrame "tok". iSplit; [done|].
    by rewrite insert_insert_eq.
  Qed.

  (** Remove a full slice from a box *)
  Lemma slice_delete_full `{!NonExpansive sm} {f P γ Px} : f !! γ = Some true →
    sinv_tok γ Px -∗ box sm f P -∗ |=[box_wsat sm]=> ∃ P',
      sm Px ∗ (P ≡ (sm Px ∗ P')) ∗ box sm (delete γ f) P'.
  Proof.
    move=> eqγ. iIntros "#tok box".
    iMod (slice_empty eqγ with "tok box") as "[$ box]".
    iMod (slice_delete_empty with "tok box") as (P') "[eq box]";
      [by rewrite lookup_insert_eq|].
    iModIntro. iExists P'. iFrame "eq".
    by rewrite delete_insert_eq ?delete_delete_eq.
  Qed.

  (** Replace a slice's contents by an equivalent one *)
  Lemma slice_iff `{!NonExpansive sm} {f P γ Px b} Qx : f !! γ = Some b →
    □ (sm Px ↔ sm Qx) -∗ sinv_tok γ Px -∗ box sm f P -∗
      |=[box_wsat sm]=> ∃ γ' P', ⌜delete γ f !! γ' = None⌝ ∗ □ (P ↔ P') ∗
        sinv_tok γ' Qx ∗ box sm (<[γ' := b]> (delete γ f)) P'.
  Proof.
    move=> eqγ. iIntros "#iff #tok box". destruct b.
    - iMod (slice_delete_full eqγ with "tok box") as (P') "(Px & #eq & box)".
      iDestruct ("iff" with "Px") as "Qx".
      iMod (slice_insert_full Qx with "Qx box") as (γ' ?) "[#tok' box]".
      iModIntro. iExists γ', _. iFrame "tok' box". iSplit; [done|].
      iRewrite "eq". iIntros "!>". by iSplit; iIntros "[? $]"; iApply "iff".
    - iMod (slice_delete_empty eqγ with "tok box") as (P') "[#eq box]".
      iMod (slice_insert_empty Qx with "box") as (γ' ?) "[#tok' box]".
      iModIntro. iExists γ', _. iFrame "tok' box". iSplit; [done|].
      iRewrite "eq". iIntros "!>". by iSplit; iIntros "[? $]"; iApply "iff".
  Qed.

  (** Split a slice in two *)
  Lemma slice_split `{!NonExpansive sm} {f P γ b Qx Qx1 Qx2} :
    f !! γ = Some b → (sm Qx ⊣⊢ sm Qx1 ∗ sm Qx2) →
    sinv_tok γ Qx -∗ box sm f P -∗ |=[box_wsat sm]=> ∃ γ1 γ2,
      ⌜delete γ f !! γ1 = None⌝ ∗ ⌜delete γ f !! γ2 = None⌝ ∗ ⌜γ1 ≠ γ2⌝ ∗
      sinv_tok γ1 Qx1 ∗ sinv_tok γ2 Qx2 ∗
      box sm (<[γ2 := b]> (<[γ1 := b]> (delete γ f))) P.
  Proof.
    move=> eqγ sep. iIntros "#tok box". destruct b.
    - iMod (slice_delete_full eqγ with "tok box") as (P') "(Qx & #eq & box)".
      rewrite sep. iDestruct "Qx" as "[Qx1 Qx2]".
      iMod (slice_insert_full Qx1 with "Qx1 box") as (γ1 nin1) "[#tok1 box]".
      iMod (slice_insert_full Qx2 with "Qx2 box") as (γ2 nin2) "[#tok2 box]".
      move: nin2=> /lookup_insert_None[nin2 ne].
      iModIntro. iExists γ1, γ2. iFrame "tok1 tok2".
      iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
      iRewrite "eq". rewrite (comm _ (sm Qx1) (sm Qx2)) -assoc. iApply "box".
    - iMod (slice_delete_empty eqγ with "tok box") as (P') "[#eq box]".
      iMod (slice_insert_empty Qx1 with "box") as (γ1 nin1) "[#tok1 box]".
      iMod (slice_insert_empty Qx2 with "box") as (γ2 nin2) "[#tok2 box]".
      move: nin2=> /lookup_insert_None[nin2 ne].
      iModIntro. iExists γ1, γ2. iFrame "tok1 tok2".
      iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
      iRewrite "eq". rewrite sep (comm _ (sm Qx1) (sm Qx2)) -assoc.
      iApply "box".
  Qed.

  (** Combine two slices into one *)
  Lemma slice_combine `{!NonExpansive sm} {f P γ1 γ2 b Qx Qx1 Qx2} :
    γ1 ≠ γ2 → f !! γ1 = Some b → f !! γ2 = Some b →
    (sm Qx ⊣⊢ sm Qx1 ∗ sm Qx2) →
    sinv_tok γ1 Qx1 -∗ sinv_tok γ2 Qx2 -∗ box sm f P -∗
      |=[box_wsat sm]=> ∃ γ, ⌜delete γ2 (delete γ1 f) !! γ = None⌝ ∗
        sinv_tok γ Qx ∗ box sm (<[γ := b]> (delete γ2 (delete γ1 f))) P.
  Proof.
    move=> ne eq1 eq2 sep. iIntros "#tok1 #tok2 box". destruct b.
    - iMod (slice_delete_full eq1 with "tok1 box") as (P1) "(Qx1 & #eqa & box)".
      iMod (slice_delete_full (γ:=γ2) (Px:=Qx2) with "tok2 box")
        as (P2) "(Qx2 & #eqb & box)"; [by simplify_map_eq|].
      iMod (slice_insert_full Qx with "[Qx1 Qx2] box") as (γ ?) "[#tok box]".
      { by rewrite sep; iFrame. }
      iModIntro. iExists γ. iFrame "tok". iSplit; [done|].
      iRewrite "eqa". iRewrite "eqb". rewrite assoc -sep. iApply "box".
    - iMod (slice_delete_empty eq1 with "tok1 box") as (P1) "[#eqa box]".
      iMod (slice_delete_empty (γ:=γ2) (Px:=Qx2) with "tok2 box")
        as (P2) "[#eqb box]"; [by simplify_map_eq|].
      iMod (slice_insert_empty Qx with "box") as (γ ?) "[#tok box]".
      iModIntro. iExists γ. iFrame "tok". iSplit; [done|].
      iRewrite "eqa". iRewrite "eqb". rewrite assoc -sep. iApply "box".
  Qed.

  (** Empty many full slices at once *)
  Lemma slice_empty_many `{!NonExpansive sm} {f P}
    (Qxs : gmap slice_name (FML $oi Σ)) :
    (∀ γ Qx, Qxs !! γ = Some Qx → f !! γ = Some true) →
    (∀ γ Qx, ⌜Qxs !! γ = Some Qx⌝ -∗ sinv_tok γ Qx) -∗ box sm f P -∗
      |=[box_wsat sm]=> ([∗ map] γ ↦ Qx ∈ Qxs, sm Qx) ∗
        box sm (((λ _, false) <$> Qxs) ∪ f) P.
  Proof.
    induction Qxs as [|γ0 Qx0 Qxs none IH] using map_ind;
      iIntros (all) "#toks box".
    { rewrite big_sepM_empty fmap_empty (left_id_L ∅ (∪)). iModIntro.
      by iFrame. }
    have nes : ∀ γ Qx, Qxs !! γ = Some Qx → γ0 ≠ γ.
    { move=> γ ? lk ?. subst. by rewrite none in lk. }
    iMod (IH with "[] box") as "[map box]".
    { move=> γ Qx lk. apply (all γ Qx).
      rewrite lookup_insert_ne; [done|exact: (nes _ _ lk)]. }
    { iIntros (γ Qx) "%lk". iApply ("toks" $! γ Qx). iPureIntro.
      rewrite lookup_insert_ne; [done|exact: (nes _ _ lk)]. }
    iMod (slice_empty (γ:=γ0) (Px:=Qx0) with "[] box") as "[Qx box]".
    { rewrite lookup_union_r;
        [by apply (all γ0 Qx0); rewrite lookup_insert_eq|].
      by rewrite lookup_fmap none. }
    { iApply ("toks" $! γ0 Qx0). iPureIntro. by rewrite lookup_insert_eq. }
    iModIntro. iSplitL "map Qx".
    { rewrite big_sepM_insert; [|done]. iFrame. }
    by rewrite fmap_insert insert_union_l.
  Qed.

  (** Fill many empty slices at once *)
  Lemma slice_fill_many {sm f P} (Qxs : gmap slice_name (FML $oi Σ)) :
    (∀ γ Qx, Qxs !! γ = Some Qx → f !! γ = Some false) →
    (∀ γ Qx, ⌜Qxs !! γ = Some Qx⌝ -∗ sinv_tok γ Qx) -∗
    ([∗ map] γ ↦ Qx ∈ Qxs, sm Qx) -∗ box sm f P -∗
      |=[box_wsat sm]=> box sm (((λ _, true) <$> Qxs) ∪ f) P.
  Proof.
    induction Qxs as [|γ0 Qx0 Qxs none IH] using map_ind;
      iIntros (all) "#toks map box".
    { rewrite fmap_empty (left_id_L ∅ (∪)). iModIntro. by iFrame. }
    have nes : ∀ γ Qx, Qxs !! γ = Some Qx → γ0 ≠ γ.
    { move=> γ ? lk ?. subst. by rewrite none in lk. }
    rewrite big_sepM_insert; [|done]. iDestruct "map" as "[Qx map]".
    iMod (IH with "[] map box") as "box".
    { move=> γ Qx lk. apply (all γ Qx).
      rewrite lookup_insert_ne; [done|exact: (nes _ _ lk)]. }
    { iIntros (γ Qx) "%lk". iApply ("toks" $! γ Qx). iPureIntro.
      rewrite lookup_insert_ne; [done|exact: (nes _ _ lk)]. }
    iMod (slice_fill (γ:=γ0) (Px:=Qx0) with "[] Qx box") as "box".
    { rewrite lookup_union_r;
        [by apply (all γ0 Qx0); rewrite lookup_insert_eq|].
      by rewrite lookup_fmap none. }
    { iApply ("toks" $! γ0 Qx0). iPureIntro. by rewrite lookup_insert_eq. }
    iModIntro. by rewrite fmap_insert insert_union_l.
  Qed.

  Lemma box_alloc `{!Inhabited (FML $oi Σ)} {sm} : ⊢ box sm ∅ emp.
  Proof.
    rewrite /box. iExists (λ _, inhabitant). rewrite !big_sepM_empty.
    iSplit; [|done]. iApply (internal_eq_refl emp). done.
  Qed.
End box.
