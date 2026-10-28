(** * Storage protocols: the algebra

  Ported from Leaf ([guarding/storage_protocol/protocol.v], as vendored by
  VerusBelt; MIT, Hance, Elbeheiry, Matsushita, Dreyer).

  A storage protocol is a resource algebra [P] of *protocol* elements, a
  resource algebra [B] of *stored* elements, and a relation [sp_rel] saying
  which stored element a protocol state holds.  The exchange laws below -
  guard, exchange, update, withdraw, deposit - are pure conditions on that
  relation, and they are what a client proves about its own protocol.

  This file is the half of Leaf's [protocol.v] that is algebra: the mixins,
  the relations, and the camera [sp_logicG] names.  None of it mentions a
  later, an [iLöb] or an invariant, so it is Leaf's text with its [Require]
  block repointed and [guarding.internal.inved] replaced by
  [nola.verus_halt.inved].

  The other half - [sp_sto], [sp_own] and the rules - is **not** here, and
  the reason is worth stating precisely, because it is a property of the
  model rather than a shortage of effort.

  Leaf's [sp_sto] holds the protocol's state in an Iris invariant

    [ownI γ (∃ state, own γ (● Inved state.1) ∗ ⌜sp_rel …⌝ ∗ f state.2)]

  and every rule opens it and pays a [▷].  Later-free that invariant has to
  become a world satisfaction over *formulas*, as [boxes.v],
  [frac_guard.v] and [lifetime/] all did.  The content is a fixed formula -
  the state sits under the existential, so [sinv] would serve - and a
  [cifcon] *can* carry the [B]-indexed family [f] that the body needs: a
  constructor with selector [{B : Type & gname}] and inductive domain
  [projT1] typechecks, and [f b] composes out of [cif_ex], [cif_pure],
  [cif_sep] and [cif_big_sepL] over [map_to_list].

  What does not go through is [own γ (● Inved p)] *as a constructor of the
  formula language*.  A constructor's semantics is an [Ecsem], a fixed
  function of the selector, the data and the children; it cannot produce an
  [own] at a camera the client chose, because it has no way to obtain the
  [inG], and [verus_haltCON] is one global signature - a single [Σ] does not
  contain every camera.

  That is a fact about [cifcon], and for a while I read it as a wall.  It is
  not, because the authority never needed to be in a formula:
  [storage_protocol_logic.v] threads it in a world satisfaction instead, the
  way [boxes.v], [frac_guard.v] and [lifetime/] thread theirs, and the whole
  of Leaf's logic half goes through that way.

  Where the fact *does* bite is one level up, in [typing/protocol.v]: the
  storage-protocol **types** hold [sp_sto] and [sp_own] inside [ty_ghox],
  which is a formula.  The port has an established idiom for exactly this
  and it is [typing/ra.v]'s: ask for the formula as a class with its
  semantics pinned,

    [Class RaFml := { ra_fml : positive → ~~𝔄 → FML $oi Σ;
                      ra_fml_sem γ a : bor_sem (ra_fml γ a) ⊣⊢ own γ a; … }]

  and leave it to whoever has a concrete [CON] to supply.  [RaFml] has no
  instance either, for the [Ecsem] reason above.  So [typing/protocol.v] is
  portable on the same footing as [typing/ra.v], under an [SpFml] of the
  same shape - which is what remains of this chain. *)

From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import auth.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import proofmode.
From iris.proofmode Require Import coq_tactics.

From stdpp Require Export namespaces.

From nola.verus_halt Require Import inved.

Class SPRel (P : Type) (B : Type) := sp_rel : P → B → Prop.

Class SPInv (P : Type) := sp_inv : P → Prop.
Class SPInterp (P : Type) (B : Type) := sp_interp : P → B.

Class StorageMixin P B
    `{Equiv P, PCore P, Op P, Valid P, Unit P}
    {equ_p: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B, SPRel P B}
    {equ_b: @Equivalence B (≡)}
:= {
    protocol_ra_mixin: RAMixin P; (* ignore valid *)
    base_ra_mixin: RAMixin B; (* ignore core *)
    
    protocol_unit_left_id : LeftId equiv (ε : P) op;
    base_unit_left_id : LeftId equiv (ε : B) op;

    sp_rel_proper: Proper ((≡) ==> (≡) ==> (↔)) sp_rel;
    interp_val: ∀ (p: P) (b: B) , sp_rel p b → ✓ b;
}. 
Global Arguments protocol_ra_mixin (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments base_ra_mixin (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments protocol_unit_left_id (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments base_unit_left_id (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments sp_rel_proper (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments interp_val (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _} (_).

Class StorageMixinII P B
    `{Equiv P, PCore P, Op P, Valid P, Unit P}
    {equ_p: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B, SPInv P, SPInterp P B}
    {equ_b: @Equivalence B (≡)}
:= {
    protocol_ra_mixin_ii: RAMixin P;
    base_ra_mixin_ii: RAMixin B; (* completely ignore core *)
    
    protocol_unit_left_id_ii : LeftId equiv (ε : P) op;
    base_unit_left_id_ii : LeftId equiv (ε : B) op;

    sp_inv_proper_ii: Proper ((≡) ==> (↔)) sp_inv;
    sp_interp_proper_ii: Proper ((≡) ==> (≡)) sp_interp;
    interp_val_ii: ∀ (p: P) , sp_inv p → ✓ (sp_interp p);
}.
Global Arguments protocol_ra_mixin_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments base_ra_mixin_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments protocol_unit_left_id_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments base_unit_left_id_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments sp_inv_proper_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments sp_interp_proper_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments interp_val_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).

Section PropMap.
  Context {Σ: gFunctors}.
  Context `{Equiv B, Op B, Valid B, Unit B}.
  
  Definition wf_prop_map (f: B → iProp Σ) :=
      Proper ((≡) ==> (≡)) f
      ∧ f ε ≡ (True)%I
      ∧ (∀ a b , ✓(a ⋅ b) → f (a ⋅ b) ≡ (f a ∗ f b) % I).
End PropMap.

Section StorageRelations.
  Context `{Equiv P, PCore P, Op P, Valid P, Unit P, SPRel P B}.
  Context `{Equiv B, PCore B, Op B, Valid B, Unit B}.
  
  Definition storage_protocol_guards (p: P) (b: B) :=
      ∀ q (t: B) , sp_rel (p ⋅ q) t → b ≼ t.
      
  Definition storage_protocol_exchange (p1 p2: P) (b1 b2: B)  :=
      ∀ q t1, sp_rel (p1 ⋅ q) t1 →
          ∃ t2, sp_rel (p2 ⋅ q) t2
          ∧ ✓(t1 ⋅ b1)
          ∧ t1 ⋅ b1 ≡ t2 ⋅ b2.
          
  Definition storage_protocol_update (p1 p2: P) :=
      ∀ q t1 , sp_rel (p1 ⋅ q) t1 → sp_rel (p2 ⋅ q) t1.
          
  Definition storage_protocol_withdraw (p1 p2: P) (b2: B)  :=
      ∀ q t1 , sp_rel (p1 ⋅ q) t1 → ∃ t2, sp_rel (p2 ⋅ q) t2
          ∧ t1 ≡ t2 ⋅ b2.
          
  Definition storage_protocol_deposit (p1 p2: P) (b1: B)  :=
      ∀ q t1 , sp_rel (p1 ⋅ q) t1 → ∃ t2, sp_rel (p2 ⋅ q) t2
          ∧ ✓(t1 ⋅ b1)
          ∧ t1 ⋅ b1 ≡ t2.
          
  Definition storage_protocol_exchange_nondeterministic (p1: P) (b1: B) (output_ok: P → B → Prop)  :=
      ∀ q t1 , sp_rel (p1 ⋅ q) t1 → ∃ p2 b2 t2 , output_ok p2 b2
          ∧ sp_rel (p2 ⋅ q) t2
          ∧ ✓(t1 ⋅ b1)
          ∧ t1 ⋅ b1 ≡ t2 ⋅ b2.
End StorageRelations.

Section StorageRelationsII.
  Context {P B: Type}.
  Context `{Equiv P, PCore P, Op P, Valid P, Unit P, SPInv P, SPInterp P B}.
  Context `{Equiv B, PCore B, Op B, Valid B, Unit B}.
  
  Definition storage_protocol_guards_ii (p: P) (b: B) :=
      ∀ q , sp_inv (p ⋅ q) → b ≼ sp_interp (p ⋅ q).
      
  Definition storage_protocol_exchange_ii (p1 p2: P) (b1 b2: B)  :=
      ∀ q , sp_inv (p1 ⋅ q) → sp_inv (p2 ⋅ q)
          ∧ ✓(sp_interp (p1 ⋅ q) ⋅ b1)
          ∧ sp_interp (p1 ⋅ q) ⋅ b1 ≡ sp_interp (p2 ⋅ q) ⋅ b2.
          
  Definition storage_protocol_update_ii (p1 p2: P) :=
      ∀ q , sp_inv (p1 ⋅ q) → sp_inv (p2 ⋅ q)
          ∧ sp_interp (p1 ⋅ q) ≡ sp_interp (p2 ⋅ q).
          
  Definition storage_protocol_withdraw_ii (p1 p2: P) (b2: B)  :=
      ∀ q , sp_inv (p1 ⋅ q) → sp_inv (p2 ⋅ q)
          ∧ sp_interp (p1 ⋅ q) ≡ sp_interp (p2 ⋅ q) ⋅ b2.
          
  Definition storage_protocol_deposit_ii (p1 p2: P) (b1: B)  :=
      ∀ q , sp_inv (p1 ⋅ q) → sp_inv (p2 ⋅ q)
          ∧ ✓(sp_interp (p1 ⋅ q) ⋅ b1)
          ∧ sp_interp (p1 ⋅ q) ⋅ b1 ≡ sp_interp (p2 ⋅ q).
          
  Definition storage_protocol_exchange_nondeterministic_ii (p1: P) (b1: B) (output_ok: P → B → Prop) :=
      ∀ q , sp_inv (p1 ⋅ q) → ∃ p2 b2 , output_ok p2 b2
          ∧ sp_inv (p2 ⋅ q)
          ∧ ✓(sp_interp (p1 ⋅ q) ⋅ b1)
          ∧ sp_interp (p1 ⋅ q) ⋅ b1 ≡ sp_interp (p2 ⋅ q) ⋅ b2.
End StorageRelationsII.

Section StorageRelationsIILemmas.
  Context `{Equiv B, PCore B, Op B, Valid B, Unit B}.
  Context `{Equiv P, PCore P, Op P, Valid P, Unit P, SPInv P, SPInterp P B}.
  Context {equ_p: @Equivalence P (≡)}.
  Context {equ_b: @Equivalence B (≡)}.
  Context {storage_mixin_ii: StorageMixinII P B}.
  
  Global Instance sp_rel_of_ii : SPRel P B := λ p b , sp_inv p ∧ sp_interp p ≡ b.
          
  Local Instance base_ra_op_proper : Proper ((≡) ==> (≡) ==> (≡)) (@op B _).
  Proof using storage_mixin_ii.
    unfold Proper, "==>". intros x y Heq x0 y0 Heq0.
    enough (x ⋅ x0 ≡ y ⋅ x0) as X.
    { setoid_rewrite X.
      eapply (ra_op_proper _ (base_ra_mixin_ii _ _ storage_mixin_ii)). trivial. }
    setoid_rewrite (ra_comm _ (base_ra_mixin_ii _ _ storage_mixin_ii) x x0).
    setoid_rewrite (ra_comm _ (base_ra_mixin_ii _ _ storage_mixin_ii) y x0).
    eapply (ra_op_proper _ (base_ra_mixin_ii _ _ storage_mixin_ii)). trivial.
  Qed.
  
  Local Instance base_ra_valid_proper : Proper ((≡) ==> (↔)) (@valid B _).
  Proof using storage_mixin_ii.
    unfold Proper, "==>". intros x y Heq. split.
    - intros Hval. eapply (ra_validN_proper _ (base_ra_mixin_ii _ _ storage_mixin_ii)).
        { eapply Heq. } apply Hval.
    - intros Hval. eapply (ra_validN_proper _ (base_ra_mixin_ii _ _ storage_mixin_ii)).
        { symmetry. eapply Heq. } apply Hval.
  Qed.
  
  Lemma eq_storage_protocol_guards_ii (p: P) (b: B)
    : storage_protocol_guards p b ↔ storage_protocol_guards_ii p b.
  Proof using equ_b.
    unfold storage_protocol_guards, storage_protocol_guards_ii. split.
    - intros Q q spi. apply (Q q). split; trivial.
    - intros Q q t [Hi Heq]. destruct (Q q Hi) as [z Hj]. exists z.
      setoid_rewrite <- Heq. trivial.
  Qed.
   
  Lemma eq_storage_protocol_exchange_ii (p1 p2: P) (b1 b2: B)
    : storage_protocol_exchange p1 p2 b1 b2 ↔ storage_protocol_exchange_ii p1 p2 b1 b2.
  Proof using storage_mixin_ii.
    unfold storage_protocol_exchange, storage_protocol_exchange_ii. split.
    - intros Q q Hspi. destruct (Q q (sp_interp (p1 ⋅ q))) as [b [[Hbi Hbin] [Hc1 Hceq]]].
      + split; trivial.
      + split; trivial. split; trivial. setoid_rewrite Hbin. trivial.
    - intros Q q t1 [Hspi Heq]. exists (sp_interp (p2 ⋅ q)).
      destruct (Q q Hspi) as [Hspi2 [Hval Heq2]]. split; trivial.
      + split; trivial.
      + split; trivial.
        * setoid_rewrite <- Heq; trivial.
        * setoid_rewrite <- Heq; trivial.
  Qed.
  
  Lemma eq_storage_protocol_update_ii (p1 p2: P)
    : storage_protocol_update p1 p2 ↔ storage_protocol_update_ii p1 p2.
  Proof using equ_b.
    unfold storage_protocol_update, storage_protocol_update_ii. split.
    - intros Q q Hspi. destruct (Q q (sp_interp (p1 ⋅ q))) as [b Hb].
      + split; trivial.
      + split; trivial.
    - intros Q q t1 [Hspi Heq].
      destruct (Q q Hspi) as [Hspi2 Heq2]. split; trivial.
      + setoid_rewrite <- Heq2. trivial.
  Qed.
  
  Lemma eq_storage_protocol_withdraw_ii (p1 p2: P) (b2: B)
    : storage_protocol_withdraw p1 p2 b2 ↔ storage_protocol_withdraw_ii p1 p2 b2.
  Proof using storage_mixin_ii.
    unfold storage_protocol_withdraw, storage_protocol_withdraw_ii. split.
    - intros Q q Hspi. destruct (Q q (sp_interp (p1 ⋅ q))) as [b [[Hba Hbb] Hc]].
      + split; trivial.
      + split; trivial. setoid_rewrite Hbb. trivial.
    - intros Q q t1 [Hspi Heq]. exists (sp_interp (p2 ⋅ q)).
      destruct (Q q Hspi) as [Hspi2 Heq2]. split; trivial.
      + split; trivial.
      + setoid_rewrite <- Heq. trivial.
  Qed.
  
  Lemma eq_storage_protocol_deposit_ii (p1 p2: P) (b1: B)
    : storage_protocol_deposit p1 p2 b1 ↔ storage_protocol_deposit_ii p1 p2 b1.
  Proof using storage_mixin_ii.
    unfold storage_protocol_deposit, storage_protocol_deposit_ii. split.
    - intros Q q Hspi. destruct (Q q (sp_interp (p1 ⋅ q))) as [b [[Hbi Hbin] [Hc1 Hceq]]].
      + split; trivial.
      + split; trivial. split; trivial. setoid_rewrite Hbin. trivial.
    - intros Q q t1 [Hspi Heq]. exists (sp_interp (p2 ⋅ q)).
      destruct (Q q Hspi) as [Hspi2 [Hval Heq2]]. split; trivial.
      + split; trivial.
      + split; trivial.
        * setoid_rewrite <- Heq; trivial.
        * setoid_rewrite <- Heq; trivial.
  Qed.
  
  Lemma eq_storage_protocol_exchange_nondeterministic_ii (p1: P) (b1: B) (output_ok: P → B → Prop)
    : storage_protocol_exchange_nondeterministic p1 b1 output_ok
      ↔ storage_protocol_exchange_nondeterministic_ii p1 b1 output_ok.
  Proof using storage_mixin_ii.
    unfold storage_protocol_exchange_nondeterministic,
      storage_protocol_exchange_nondeterministic_ii. split.
     - intros Q q Hspi.
        destruct (Q q (sp_interp (p1 ⋅ q))) as [p2 [b2 [t2 [Hoo [Hrel [Hval Heq]]]]]].
      + split; trivial.
      + destruct Hrel as [Ha Hb]. exists p2. exists b2. split; trivial. split; trivial.
        split; trivial. setoid_rewrite Hb. trivial.
     - intros Q q t1 [Hinv Hint]. destruct (Q q Hinv) as [p2 [b2 [Hoo [Hspinv [Hval Heq]]]]].
        exists p2. exists b2. exists (sp_interp (p2 ⋅ q)). split; trivial.
        split.
        + split; trivial.
        + split.
          * setoid_rewrite <- Hint. trivial.
          * setoid_rewrite <- Hint. trivial.
  Qed.
End StorageRelationsIILemmas.

Global Instance storage_mixin_from_ii
  `{Equiv B, PCore B, Op B, Valid B, Unit B}
  `{Equiv P, PCore P, Op P, Valid P, Unit P, SPInv P, SPInterp P B}
  {equ_p: @Equivalence P (≡)}
  {equ_b: @Equivalence B (≡)}
  (storage_mixin_ii: StorageMixinII P B) : StorageMixin P B.
Proof.
    split.
     - apply (protocol_ra_mixin_ii P B storage_mixin_ii).
     - apply (base_ra_mixin_ii P B storage_mixin_ii).
     - apply (protocol_unit_left_id_ii P B storage_mixin_ii).
     - apply (base_unit_left_id_ii P B storage_mixin_ii).
     - intros x y Heq x0 y0 Heq0. split.
        + intros [Hinv HeqX]. split.
          * rewrite (sp_inv_proper_ii _ _ storage_mixin_ii). { apply Hinv. } symmetry.
              apply Heq.
          * setoid_rewrite Heq0 in HeqX.
            rewrite (sp_interp_proper_ii _ _ storage_mixin_ii). { apply HeqX. }
            symmetry. apply Heq.
        + intros [Hinv HeqX]. split.
          * rewrite (sp_inv_proper_ii _ _ storage_mixin_ii). { apply Hinv. }
              apply Heq.
          * setoid_rewrite <- Heq0 in HeqX.
            rewrite (sp_interp_proper_ii _ _ storage_mixin_ii). { apply HeqX. }
            apply Heq.
     - intros p b [Ha Hb]. rewrite base_ra_valid_proper. 
      { apply (interp_val_ii _ _ storage_mixin_ii). apply Ha. } { trivial. }
Qed.

(** Exported, unlike Leaf's: [storage_protocol_logic.v] is a separate file
  here, so the camera it builds on has to be nameable from outside. *)
#[export] Instance sp_rel_pinv {P B : Type} {ir: SPRel P B} : InternalPInv P :=
  λ p , ∃ b , sp_rel p b.
  
Definition internal_protocol_mixin_storage_mixin
    `{Equiv P, PCore P, Op P, Valid P, Unit P}
    {equ_p: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B, SPRel P B}
    {equ_b: @Equivalence B (≡)}
    (storage_mixin: StorageMixin P B)
    : InternalProtocolMixin P.
Proof.
  destruct storage_mixin as [Q1 Q2 Q3 Q4 irp Q5]. split; trivial.
  unfold Proper, "==>", impl. intros x y Heq. unfold pinv, sp_rel_pinv.
  intros [b J]. unfold Proper, "==>", impl in irp.
  setoid_rewrite (irp x y _ b b) in J; trivial. exists b. trivial.
Qed.

Class sp_logicG
    `{Equiv P, PCore P, Op P, Valid P, Unit P} `{equ_p: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B, SPRel P B} `{equ_b: @Equivalence B (≡)}
    (storage_mixin: StorageMixin P B) Σ
:= {
  (** [#[global]], unlike Leaf's [#[local]]: the logic lives in a separate
    file here ([storage_protocol_logic.v]), so the [inG] has to escape. *)
  #[global] sp_authG :: inG Σ (authUR (inved_protocolUR
                          (internal_protocol_mixin_storage_mixin storage_mixin)))
}.

Definition sp_logicΣ
    `{Equiv P, PCore P, Op P, Valid P, Unit P} `{equ_p: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B, SPRel P B} `{equ_b: @Equivalence B (≡)}
    (storage_mixin: StorageMixin P B)
: gFunctors := #[
  GFunctor (authUR (inved_protocolUR
                          (internal_protocol_mixin_storage_mixin storage_mixin)))
].

Global Instance subG_sp_logicΣ
  `{Equiv P, PCore P, Op P, Valid P, Unit P} `{equ_p: @Equivalence P (≡)}
  `{Equiv B, PCore B, Op B, Valid B, Unit B, SPRel P B} `{equ_b: @Equivalence B (≡)}
  (storage_mixin: StorageMixin P B) Σ
    : subG (sp_logicΣ storage_mixin) Σ → sp_logicG storage_mixin Σ.
Proof.
  solve_inG.
Qed.
