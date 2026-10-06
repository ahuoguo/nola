(** * Ported from VerusBelt/AlerusBelt ([lambda_verus/util/atomic_lock_counter.v], MIT,
  Hance, Elbeheiry, Matsushita, Dreyer).  Later-free as it stands. *)

From iris.proofmode Require Import proofmode.
From nola.alerus.util Require Import basic.
From iris.algebra Require Import gset coPset dfrac_agree auth gmultiset view list gmap excl numbers.
From iris.base_logic.lib Require Import own.
Set Default Proof Using "Type".

(* Fragments add together, but subtract from the Auth, so they all add up to (0, ∅).
   Every AlcFrag needs to have count >= 1, so we use n to represent a count of (S n). *)
Inductive alc_car :=
  | AlcUnit
  | AlcAuth (n: nat) (c: coPset)
  | AlcFrag (n: nat) (c: coPset)
  | AlcBot.

Instance alc_op : Op alc_car := λ a b, match a, b with
    | AlcUnit, x => x
    | x, AlcUnit => x
    | AlcAuth _ _, AlcAuth _ _ => AlcBot
    | AlcAuth n1 c1, AlcFrag n2 c2 =>
        if bool_decide(S n2 ≤ n1 ∧ c2 ⊆ c1) then AlcAuth (n1 - S n2) (c1 ∖ c2) else AlcBot
    | AlcFrag n2 c2, AlcAuth n1 c1 =>
        if bool_decide(S n2 ≤ n1 ∧ c2 ⊆ c1) then AlcAuth (n1 - S n2) (c1 ∖ c2) else AlcBot
    | AlcFrag n1 c1, AlcFrag n2 c2 =>
        if bool_decide(c1 ## c2) then AlcFrag (n1 + n2 + 1) (c1 ∪ c2) else AlcBot
    | AlcBot, _ => AlcBot
    | _, AlcBot => AlcBot
end.

Instance alc_valid : Valid alc_car := λ a, match a with
    | AlcUnit => True
    | AlcFrag n c => True
    | AlcAuth n c => n=0 → c=∅
    | AlcBot => False
end.

Instance alc_equiv : Equiv alc_car := λ a b , a = b.

Instance alc_pcore : PCore alc_car := λ a , Some AlcUnit.

Lemma alc_comm : Comm (=) alc_op.
Proof.
  intros x y. destruct x as [|nx cx|nx cx|]; destruct y as [|ny cy|ny cy|]; trivial.
  unfold alc_op. case_bool_decide as Hd; case_bool_decide as Hd2; try set_solver.
  f_equal. { lia. } { set_solver. }
Qed.

Lemma alc_assoc : Assoc (=) alc_op.
Proof.
  intros [|nx cx|nx cx|] [|ny cy|ny cy|] [|nz cz|nz cz|]; try done; unfold alc_op;
    try (case_bool_decide; done); repeat case_bool_decide; try done; try f_equal; trivial;
    try lia;
    try (exfalso; (match goal with | [ H' : ¬ _ |- _ ] =>
      apply H'; destruct_and?; try split; try lia; set_solver end));
    set_solver.
Qed.

Lemma left_id x :
    (AlcUnit) ⋅ x = x.
Proof. done. Qed.

Definition alc_ra_mixin : RAMixin alc_car.
Proof. split.
    - typeclasses eauto.
    - intros. exists cx. done.
    - typeclasses eauto.
    - apply alc_assoc.
    - apply alc_comm.
    - intros x cx H2. unfold pcore, alc_pcore in H2. inversion H2. apply left_id.
    - intros x cx H2. unfold pcore, alc_pcore in H2. inversion H2. done.
    - intros x y cx incl H2. unfold pcore, alc_pcore in H2. inversion H2.
      exists (AlcUnit). split; try done. exists (AlcUnit). rewrite left_id; trivial.
    - intros [|nx cx|nx cx|] [|ny cy|ny cy|]; try done.
      unfold "✓", alc_valid, "⋅", alc_op. case_bool_decide; last done. lia.
Qed.

Canonical Structure alcO := discreteO alc_car.
Canonical Structure alcR := discreteR alc_car alc_ra_mixin.

Global Instance alc_cmra_discrete : CmraDiscrete alcR.
Proof. apply discrete_cmra_discrete. Qed.

Global Instance alc_unit : Unit alc_car := AlcUnit.

Definition alc_ucmra_mixin : UcmraMixin alc_car.
Proof. split; done. Qed.

Canonical Structure alcUR := Ucmra alc_car alc_ucmra_mixin.

Class alc_logicG Σ := {
  #[global] alc_logic_inG :: inG Σ alcUR
}.

Definition alc_logicΣ : gFunctors := #[ GFunctor alcUR ].

Global Instance subG_alc_logicΣ {Σ} : subG alc_logicΣ Σ → alc_logicG Σ.
Proof. solve_inG. Qed.


Section atomic_util.
  Context {Σ: gFunctors}.
  Context {cmapl: alc_logicG Σ}.
  
  Local Lemma entails_from_eq γ (x y : alc_car) :
      x = y → own γ x ⊢ own γ y.
  Proof. intros ->. done. Qed.

  Definition atomic_lock_ctr (γ: gname) (n: nat) (c: coPset) : iProp Σ :=
    own γ (AlcAuth n (⊤ ∖ c)).

  Definition atomic_lock_handle (γ: gname) (c: coPset) : iProp Σ :=
    own γ (AlcFrag 0 c).

  Local Arguments atomic_lock_ctr _ _ _ /: simpl nomatch.

  Lemma atomic_lock_ctr_alloc : ⊢ |==> ∃ γ , atomic_lock_ctr γ 0 ⊤. 
  Proof.
    simpl.
    iMod (own_alloc (AlcAuth 0 (⊤ ∖ ⊤) : alcUR)) as "[% H]"; last by iFrame.
    replace (⊤ ∖ ⊤) with (∅: coPset) by set_solver. done.
  Qed.

  Lemma atomic_lock_ctr_inc γ n c d : d ⊆ c → atomic_lock_ctr γ n c ⊢ atomic_lock_ctr γ (n + 1) (c ∖ d) ∗ atomic_lock_handle γ d.
  Proof.
    move => Hdc.
    rewrite /atomic_lock_ctr/atomic_lock_handle.
    rewrite <- own_op. apply entails_from_eq.
    unfold "⋅", alcR, cmra_op, alc_op. case_bool_decide as Ha.
      - f_equal; first lia. set_solver.
      - exfalso. apply Ha. split; first lia. set_solver.
  Qed.
    
  Lemma atomic_lock_ctr_dec γ n c d : atomic_lock_ctr γ (n + 1) c -∗ atomic_lock_handle γ d -∗ atomic_lock_ctr γ n (c ∪ d). 
  Proof.
    iIntros "Hc Hd". iCombine "Hc Hd" as "Hc".
    iDestruct (own_valid with "Hc") as "%Hval".
    iApply (entails_from_eq with "Hc"). move: Hval.
    unfold "⋅", "✓", alcR, cmra_op, cmra_valid, alc_op, alc_valid.
    intro Hval. case_bool_decide as Ha.
      - f_equal; first lia. set_solver.
      - exfalso. apply Ha. split; first lia. set_solver.
  Qed.

  Lemma atomic_lock_ctr_ge0 γ c d : atomic_lock_ctr γ 0 c -∗ atomic_lock_handle γ d -∗ False.
  Proof.
    iIntros "Hc Hd".
    rewrite  /atomic_lock_ctr/atomic_lock_handle.
    iCombine "Hc Hd" as "H".
    iDestruct (own_valid with "H") as "%Hvalid". exfalso.
    unfold "⋅", "✓", alcR, cmra_op, cmra_valid, alc_op, alc_valid in Hvalid.
    case_bool_decide as Ha; first lia. done.
  Qed.

  Lemma atomic_lock_ctr_top γ c : atomic_lock_ctr γ 0 c ⊢ ⌜c = ⊤⌝.
  Proof.
    iIntros "Hc".
    iDestruct (own_valid with "Hc") as "%Hvalid". iPureIntro.
    unfold "✓", alcR, cmra_valid, alc_valid in Hvalid.
    have Hv := Hvalid eq_refl. apply set_eq. intros x. split; set_solver.
  Qed.

  Lemma atomic_lock_ctr_handle_disjoint γ n c d : atomic_lock_ctr γ n c -∗ atomic_lock_handle γ d -∗ ⌜c ## d⌝. 
  Proof.
    iIntros "Hc Hd". iCombine "Hc Hd" as "Hc".
    iDestruct (own_valid with "Hc") as "%Hvalid". iPureIntro.
    unfold "⋅", "✓", alcR, cmra_op, cmra_valid, alc_op, alc_valid in Hvalid.
    case_bool_decide; set_solver.
  Qed.
End atomic_util.
