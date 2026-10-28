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

  Two models.  [fnFml_one_level] is the one-level family - [ns = [n]]
  for the ambient names [n], hence [fn_lv_top = 1] and two callable
  arrow levels, [j = 1] and [j = 0].  [fnFml_levels] at the end of this
  file is the family at its full length.

  [fn_lv_top] used to be stuck at 1, and the reason is worth recording
  because what fixed it is one conjunct.  [fn_wsat_top] forces the
  family's top to be the *ambient* [verus_halt_wsat], and
  [verus_halt_wsat] was one level's own machinery - [llft_wsat], the
  box, the invariants, the store, at one [verus_haltNames].  A family of
  length [L] has top [verus_halt_shared ∗ ∗_{k<L} Wbor_k], which is not
  one level's at any names, and no frame-preserving step makes up the
  difference: the lower levels have to exist before the body runs and
  nothing creates them.

  So the ambient world gained somewhere to put them -
  [verus_haltGS]'s [verus_halt_Wx], which [verus_haltGS_of] sets to
  [emp] and [verus_haltGS_of_lv] fills.  Nothing inside
  [verus_halt_wsat_core] mentions it, so a level's own package is still
  a function of its names alone and the levels stay non-circular.

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
  and the reason is not in this file - nor, any more, is it the length
  of the family.  A level-[j] arrow has
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
    rewrite /fn_Wlv /verus_halt_wsat_below /verus_halt_shared
      /verus_halt_wsat verus_halt_wsat_core_split /=. iSplit.
    - iIntros "[[A B] [C _]]". iFrame.
    - iIntros "[[A [B _]] C]". iFrame.
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

(** * The model at the family's full length

  The one above has [fn_lv_top = 1], and its header says why: [FnFml]'s
  [fn_wsat_top] makes the family's top the *ambient* [verus_halt_wsat],
  and [verus_halt_wsat] used to be one level's machinery.  A family of
  length [L] has top [verus_halt_shared ∗ ∗_{k<L} Wbor_k], which is not
  one level's at any names, and no frame-preserving step makes up the
  difference: the lower levels have to exist before the body runs and
  nothing creates them.

  So the ambient world got a conjunct for them - [verus_haltGS]'s
  [verus_halt_Wx], which [verus_haltGS_of] sets to [emp] and
  [verus_haltGS_of_lv] fills.  Here it is filled, and [fn_lv_top] is the
  family's length.

  The ambient names are the **bottom** level's, which is what makes the
  shared half line up on both sides of [fnlv_Wlv_top]:
  [verus_halt_shared] is pinned to the bottom ([typing/level_ctx.v]),
  because [llft_other_shared] holds the outlives guards and an [fguard]
  is taken over *a* level's [llft_wsatG] - and level 0's machinery is in
  [∗_{k<j} Wbor_k] for every [j ≥ 1], so a guard stored there is
  openable at every execution level a body can be at.

  What this still does **not** buy is the level being load-bearing, and
  that is a third thing, named in [fn_inst]'s header above: this port's
  borrow formers record a slot's level as its *pointee's*, so
  [knot_not_typable] has no premise to be discharged from.
  [typing/strat_bor.v] is the same argument mechanized end to end over a
  model that does index its slots by level. *)
Section fn_inst_lv.
  Context {Σ} `{!verus_haltGpreS (cifOF verus_haltCON) Σ,
    !invGS_gen HasNoLc Σ}.
  Context (hLlft : llft_logicGS Σ) (hGS : heapGS (cifOF verus_haltCON) Σ)
    (hP : prophG Σ) (hU : uniqG Σ)
    (n0 : verus_haltNames (CON:=verus_haltCON) (Σ:=Σ))
    (ns' : list (verus_haltNames (CON:=verus_haltCON) (Σ:=Σ))).

  Notation Pc := (verus_halt_lvl_const hLlft hGS hP hU).

  (** The levels *above* the ambient one, which is level 0 *)
  Definition fnlv_Wx : iProp Σ :=
    [∗ list] k ↦ n ∈ ns', lvl_wsat_lvl (Pc (S k) n).

  #[local] Instance fn_inst_lv_GS : verus_haltGS (cifOF verus_haltCON) Σ :=
    verus_haltGS_of_lv hLlft hGS hP hU n0 fnlv_Wx.

  (** The family.  It is [verus_halt_wsat_below]'s shape - one shared
    half beside the level halves below [j] - written with **level 0 as
    the ambient package** rather than as [Pc 0 n0]'s.  The two are the
    same proposition, since the only difference between the two
    [verus_haltGS]es is [verus_halt_Wx] and neither half projects it, but
    they are not the same *term*, and leaving that to conversion costs
    minutes where this costs nothing. *)
  Definition fnlv_tail (j : nat) : iProp Σ :=
    [∗ list] k ↦ n ∈ take j ns', lvl_wsat_lvl (Pc (S k) n).

  Definition fnlv_lvls (j : nat) : iProp Σ :=
    match j with
    | 0 => emp
    | S j' => verus_halt_wsat_lvl ∗ fnlv_tail j'
    end.

  Definition fnlv_Wlv (j : nat) : iProp Σ :=
    (verus_halt_wsat_shared ∗ fnlv_lvls j) ∗ send_wsat.

  Lemma fnlv_Wx_eq : verus_halt_Wx = fnlv_Wx.
  Proof. reflexivity. Qed.

  Lemma fnlv_tail_all : fnlv_tail (length ns') = fnlv_Wx.
  Proof. by rewrite /fnlv_tail firstn_all. Qed.

  Lemma fnlv_tail_le {j j'} : (j ≤ j')%nat →
    fnlv_tail j' ⊣⊢ fnlv_tail j ∗
      ([∗ list] k ↦ n ∈ drop j (take j' ns'),
        lvl_wsat_lvl (Pc (S (length (take j ns') + k)) n)).
  Proof.
    move=> Hle. rewrite /fnlv_tail -{1}(take_drop j (take j' ns'))
      big_sepL_app take_take Nat.min_l //.
  Qed.

  (** The family's top, as the three things that are allocated: level
    0's core at the ambient package, [send_wsat], and the levels above.
    [fnlv_names_alloc] below produces the first and the third. *)
  Lemma fnlv_wsat_parts :
    verus_halt_wsat ⊣⊢ verus_halt_wsat_core ∗ send_wsat ∗ fnlv_Wx.
  Proof. by rewrite /verus_halt_wsat fnlv_Wx_eq. Qed.

  Lemma fnlv_Wlv_top : verus_halt_wsat ⊣⊢ fnlv_Wlv (S (length ns')).
  Proof.
    rewrite /fnlv_Wlv /verus_halt_wsat verus_halt_wsat_core_split
      fnlv_Wx_eq. cbn [fnlv_lvls]. rewrite fnlv_tail_all. iSplit.
    - iIntros "[[A B] [C D]]". iFrame.
    - iIntros "[[A [B D]] C]". iFrame.
  Qed.

  Lemma fnlv_Wlv_acc {j} : (j ≤ S (length ns'))%nat →
    ⊢ □ (fnlv_Wlv (S (length ns')) ={∅}=∗
         fnlv_Wlv j ∗ (fnlv_Wlv j ={∅}=∗ fnlv_Wlv (S (length ns')))).
  Proof.
    move=> Hle. rewrite /fnlv_Wlv. destruct j as [|j'].
    { cbn [fnlv_lvls]. iIntros "!> [[S L] send] !>".
      iSplitR "L"; [by iFrame "S send"|].
      iIntros "[[S _] send] !>". iFrame "S L send". }
    have Hle' : (j' ≤ length ns')%nat by lia.
    cbn [fnlv_lvls]. rewrite (fnlv_tail_le Hle').
    iIntros "!> [[S [L [T R]]] send] !>".
    iSplitR "R"; [by iFrame "S L T send"|].
    iIntros "[[S [L T]] send] !>". iFrame "S L T R send".
  Qed.

  Definition fnFml_levels : @FnFml (cifOF verus_haltCON) Σ _ := {|
    fn_wsat_lv := fnlv_Wlv;
    fn_lv_top := S (length ns');
    fn_wsat_top := fnlv_Wlv_top;
    fn_wsat_lv_acc j := @fnlv_Wlv_acc j;
    fn_fml A 𝔄l 𝔅 ℭ j fp spec x := tfn_fml fnlv_Wlv j fp spec x;
    fn_fml_elim sem H A 𝔄l 𝔅 ℭ j fp spec x := tfn_elim H fnlv_Wlv j fp spec x;
    fn_fml_intro A 𝔄l 𝔅 ℭ j fp spec x := tfn_intro fnlv_Wlv j fp spec x;
    fn_fml_pers sem H A 𝔄l 𝔅 ℭ j fp spec x := tfn_pers H fnlv_Wlv j fp spec x;
    fn_fml_specialize sem H A B 𝔄l 𝔅 ℭ σ j fp spec x :=
      tfn_specialize H σ fnlv_Wlv j fp spec x;
  |}.

  (** The family is a genuine one, and the two ends are the ones the
    thesis names.  The bottom is the lifetime algebra's shared half
    beside [send_wsat] and **nothing else** - no borrows, no box, no
    shared-borrow family, no invariants, no store.  Each step up adds
    exactly one level's borrow machinery. *)
  Lemma fnlv_Wlv_0 :
    fnlv_Wlv 0 ⊣⊢ verus_halt_wsat_shared ∗ send_wsat.
  Proof.
    rewrite /fnlv_Wlv. cbn [fnlv_lvls]. by rewrite bi.sep_emp.
  Qed.

  Lemma fnlv_Wlv_S_0 : fnlv_Wlv 1 ⊣⊢ fnlv_Wlv 0 ∗ verus_halt_wsat_lvl.
  Proof.
    rewrite fnlv_Wlv_0 /fnlv_Wlv. cbn [fnlv_lvls].
    rewrite /fnlv_tail /= bi.sep_emp. iSplit.
    - iIntros "[[A B] C]". iFrame.
    - iIntros "[[A C] B]". iFrame.
  Qed.

  Lemma fnlv_Wlv_S j : (j < length ns')%nat →
    fnlv_Wlv (S (S j)) ⊣⊢ fnlv_Wlv (S j) ∗
      ([∗ list] k ↦ n ∈ drop j (take (S j) ns'),
        lvl_wsat_lvl (Pc (S (length (take j ns') + k)) n)).
  Proof.
    move=> Hlt. rewrite /fnlv_Wlv. cbn [fnlv_lvls].
    rewrite (fnlv_tail_le (Nat.le_succ_diag_r j)).
    iSplit; [by iIntros "[[A [B [C D]]] E]"; iFrame
            |by iIntros "[[[A [B C]] E] D]"; iFrame].
  Qed.
End fn_inst_lv.

(** ** The levelled world, allocated

  [verus_halt_names_alloc_lv] is what makes the bottom level's half land
  at the **ambient** package rather than at [verus_haltGS_of … n0]: its
  [Wx] is instantiated with [fnlv_Wx], which the further levels supply.
  The two packages are the same proposition either way - neither half of
  the world projects [verus_halt_Wx] - but they are not the same term,
  and the conversion between them is not cheap. *)
Lemma fnlv_names_alloc {Σ}
  `{!verus_haltGpreS (cifOF verus_haltCON) Σ, !invGS_gen HasNoLc Σ}
  (hGS : heapGS (cifOF verus_haltCON) Σ) (hP : prophG Σ) (hU : uniqG Σ) L :
  ⊢ |==> ∃ (hLlft : llft_logicGS Σ) (n0 : verus_haltNames)
    (ns' : list verus_haltNames), ⌜length ns' = L⌝ ∗
    @verus_halt_wsat_core (cifOF verus_haltCON) Σ
      (fn_inst_lv_GS hLlft hGS hP hU n0 ns') _ ∗
    fnlv_Wx hLlft hGS hP hU ns'.
Proof.
  iMod verus_halt_names_alloc_lv as (hLlft n0) "[#Wits W0]".
  iMod (verus_halt_names_more_list_alloc hGS hP hU hLlft L with "Wits")
    as (ns' Hlen) "Wns".
  iAssert (fnlv_Wx hLlft hGS hP hU ns') with "[Wns]" as "Wx".
  { rewrite /fnlv_Wx. iApply (big_sepL_mono with "Wns")=> k n _ /=.
    iIntros "W". iApply (names_wsat_lvl_of with "W"). }
  iModIntro. iExists hLlft, n0, ns'. iSplitR; [done|]. iFrame "Wx".
  iApply ("W0" $! hGS hP hU (fnlv_Wx hLlft hGS hP hU ns')).
Qed.

(** Both models rest on nothing but what [typing/inst.v]'s own theorems
  do. *)
Print Assumptions fnFml_one_level.
Print Assumptions fnFml_levels.
