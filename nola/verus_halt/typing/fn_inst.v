(** * The first model of [FnFml]

  [typing/function.v]'s [FnFml] has been the one class in the
  development with no instance, so [fn] has been the one type former
  the model does not interpret, and [typing/soundness.v]'s theorems are
  stated about a typing judgment for that reason.  This file gives it a
  model.

  ** What made it impossible, and what changed

  Two fields, both fixed in [typing/function.v] and both found by
  auditing the class against the thesis rather than against the code.

  The formula side needed no judgment and no new constructor.  This
  port's [fn] is capture-free, so [fn_pure_candidate]'s
  [tfn_fml := pure_fml (⊢ fn_body …)] is an honest reading of "this
  value is a function whose body is well typed", and [pure_sem_at_any]
  makes it candidate-independent for free - which is what
  [nola/bi/deriv.v]'s [der_const] needs.  What stood in the way was
  that [FnFml] asked for an [⊣⊢] whose introduction direction is
  [fn_body ⊢ ⌜⊢ fn_body⌝] - **false**, and so not something any model
  was ever going to supply.  The class now asks for elimination at
  every candidate and introduction at the *Coq* level, which is the
  shape every use in the development already has.

  The world side needed the obligation split in two.  The old
  [fn_wsat_lv_acc] read [verus_halt_wsat ={∅}=∗ fn_wsat_lv j ∗ …] with
  no side condition, which looks like the thesis's "a caller lends a
  callee the part its level names" and is satisfiable by no real
  family - [verus_halt_wsat] at one level's names and
  [verus_halt_wsat_below P ns j] are different propositions with no
  frame-preserving step between them.  It is now [fn_wsat_top], one
  equation saying the ambient world *is* the family's top, plus an
  accessor guarded by [j < fn_lv_top].

  ** What this model is, exactly

  The one-level family: [ns = [n]] for the ambient names [n], hence
  [fn_lv_top = 1] and two callable arrow levels, [j = 1] and [j = 0].

  [fn_lv_top] cannot be larger, and the reason is worth stating because
  it is the whole of what is still missing.  [fn_wsat_top] forces the
  family's top to be the *ambient* [verus_halt_wsat], and
  [verus_halt_wsat] is one level's own machinery - [llft_wsat], the
  box, the invariants, the store, at one [verus_haltNames].  A family
  of length [L+1] has [verus_halt_wsat_below … (L+1)] equal to the
  shared half beside [L+1] distinct level halves, which is not
  [verus_halt_wsat] at any single level's names.  So the levels a
  typing derivation can see are bounded by what the *ambient* ghost
  state is, and that is one.

  The two levels differ exactly as the thesis says they should.

  [j = 1] is [j = i], the top of the family: [fn_Wlv 1 ⊣⊢
  verus_halt_wsat] ([fn_Wlv_top]), so a level-1 body is an ordinary
  [typed_body] ([typed_body_at_top]) and every rule in [typing/]
  applies to it unchanged.  This is the level an ordinary function is
  written at, and the one the examples use.

  [j = 0] is the stratified case: a level-0 body runs under
  [verus_halt_wsat_below … 0], which is [verus_halt_shared] -
  [llft_inv_shared ∗ llft_other_shared], the lifetime algebra's tokens,
  kill order, minted atoms and outlives relation - beside [send_wsat],
  and **nothing else** ([fn_Wlv_0]).  No borrows, no box, no
  invariants, no store: those are [verus_halt_wsat_lvl], level 0's own.

  ** What it does not settle

  The level is a real distinction here but it is not yet load-bearing,
  and the reason is not in this file.  A level-[j] arrow has
  [ty_lev = S j] ([typing/function.v]'s [fn_ty_lev]), and the
  discipline wants a slot holding it to be at machinery level [≥ S j],
  so that opening the slot needs execution level [> j] and a level-[j]
  body cannot reach its own slot - [knot_not_typable].  This port's
  borrow formers do not record a machinery level at all: [typing/own.v],
  [own_rec.v], [uniq_bor.v] and [shr_bor.v] all set a slot's level to
  its *pointee's*, and [verus_halt_wsat_lvl] is one monolithic block
  per level.  So [knot_not_typable] has no premise to be discharged
  from, and what actually keeps a self-referential function out is
  something cruder and quite separate: a total [twp] has no Löb rule,
  so [⊢ fn_body …] has nothing to prove itself with.  VerusBelt's
  [type_fnrec] is exactly the rule that needs one, and it is the rule
  this port does not have.

  Worth saying plainly, because an earlier note in [typing/function.v]
  got it wrong: no choice of [fn_wsat_lv] can make a divergent program
  typable.  [typing/soundness.v]'s [type_soundness] takes
  [⊢ typed_body … e tr] to [sn erased_step] and is a Rocq theorem, so
  every [FnFml] whose obligations are provable is sound by
  construction.  What a degenerate instance loses is content, not
  soundness.

  [typing/function.v]'s [knot_not_typable] is the argument in general,
  and [typing/strat_bor.v] is where the same argument is mechanized end
  to end over a model that *does* index its slots by level. *)

From nola.verus_halt.typing Require Export inst.
From nola.verus_halt.typing Require Import function level_ctx ctx
  programs inv_context cont_context type_context.
From iris.proofmode Require Import proofmode.
Import ModwNotation iPropAppNotation.

Section fn_inst.
  Context {Σ} `{!verus_haltGpreS (cifOF verus_haltCON) Σ,
    !invGS_gen HasNoLc Σ}.
  Context (hLlft : llft_logicGS Σ) (hGS : heapGS (cifOF verus_haltCON) Σ)
    (hP : prophG Σ) (hU : uniqG Σ) (n : verus_haltNames (CON:=verus_haltCON) (Σ:=Σ)).

  #[local] Instance fn_inst_GS : verus_haltGS (cifOF verus_haltCON) Σ :=
    verus_haltGS_of hLlft hGS hP hU n.

  Notation Pc := (verus_halt_lvl_const hLlft hGS hP hU).

  Definition fn_Wlv (j : nat) : iProp Σ :=
    verus_halt_wsat_below hLlft hGS hP hU Pc [n] j ∗ send_wsat.

  Lemma fn_Wlv_top : verus_halt_wsat ⊣⊢ fn_Wlv 1.
  Proof.
    rewrite /fn_Wlv /verus_halt_wsat_below /verus_halt_shared /=
      bi.sep_emp /verus_halt_wsat verus_halt_wsat_core_split. done.
  Qed.
  Lemma fn_Wlv_acc {j} : (j ≤ 1)%nat →
    ⊢ □ (fn_Wlv 1 ={∅}=∗ fn_Wlv j ∗ (fn_Wlv j ={∅}=∗ fn_Wlv 1)).
  Proof.
    move=> Hle.
    rewrite /fn_Wlv
      (verus_halt_wsat_below_le hLlft hGS hP hU (P:=Pc) (ns:=[n]) Hle).
    iIntros "!> [[B Br] S] !>". iFrame "B S". iIntros "[B S] !>". iFrame.
  Qed.

  Definition fnFml_one_level : @FnFml (cifOF verus_haltCON) Σ _ := {|
    fn_wsat_lv := fn_Wlv;
    fn_lv_top := 1;
    fn_wsat_top := fn_Wlv_top;
    fn_wsat_lv_acc j := @fn_Wlv_acc j;
    fn_fml A 𝔄l 𝔅 ℭ j fp spec x := tfn_fml fn_Wlv j fp spec x;
    fn_fml_elim sem H A 𝔄l 𝔅 ℭ j fp spec x := tfn_elim H fn_Wlv j fp spec x;
    fn_fml_intro A 𝔄l 𝔅 ℭ j fp spec x := tfn_intro fn_Wlv j fp spec x;
    fn_fml_pers sem H A 𝔄l 𝔅 ℭ j fp spec x := tfn_pers H fn_Wlv j fp spec x;
    fn_fml_specialize sem H A B 𝔄l 𝔅 ℭ σ j fp spec x :=
      tfn_specialize H σ fn_Wlv j fp spec x;
  |}.
  (** *** The two levels

    [j = 1] is the top, so [fn_Wlv 1 ⊣⊢ verus_halt_wsat] ([fn_Wlv_top]),
    a level-1 body is an ordinary [typed_body] by [typing/function.v]'s
    [typed_body_at_top], and [type_fn_top]/[type_call_top] are the rules
    for it - the shape VerusBelt's own [type_fn] and [type_call] have. *)

  (** [j = 0] is the stratified case: the lifetime logic's shared half -
    tokens, kill order, minted atoms, outlives relation - beside
    [send_wsat], and **nothing else**.  No borrow bookkeeping, no box,
    no shared-borrow family, no invariants, no store: those are
    [verus_halt_wsat_lvl], which is level 0's own and which
    [verus_halt_wsat_below … 0] does not include. *)
  Lemma fn_Wlv_0 : fn_Wlv 0 ⊣⊢ verus_halt_wsat_shared ∗ send_wsat.
  Proof. by rewrite /fn_Wlv verus_halt_wsat_below_0. Qed.

  (** And the family is a family: the two are genuinely different, with
    the level-0 world strictly inside the top one. *)
  Lemma fn_Wlv_0_1 : ⊢ □ (fn_Wlv 1 ={∅}=∗ fn_Wlv 0 ∗ (fn_Wlv 0 ={∅}=∗ fn_Wlv 1)).
  Proof. exact (fn_Wlv_acc (Nat.le_0_l 1)). Qed.

End fn_inst.

(** The model rests on nothing but what [typing/inst.v]'s own theorems do. *)
Print Assumptions fnFml_one_level.
