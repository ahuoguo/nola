(** * Storage protocols: the logic, later-free

  Ported from Leaf ([guarding/storage_protocol/protocol.v]'s
  [Section StorageLogic], as vendored by VerusBelt; MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  ** The invariant becomes a world satisfaction

  Leaf keeps a protocol's state in an Iris invariant at the protocol's own
  ghost name,

    [ownI γ (∃ state, own γ (● Inved state.1) ∗ ⌜sp_rel …⌝ ∗ f state.2)]

  so every rule carries a mask [{[γ]}] and every opening pays a [▷].  Here
  it is an explicit world satisfaction, as [box_wsat], [shr_wsat] and
  [send_wsat] are: [sp_wsat γ f] *is* that body, threaded by hand.  So
  [sp_sto] keeps only what is persistent about a protocol - the
  well-formedness of [f] and the unit fragment - and the rules are updates
  and guards over [sp_wsat γ f] with no mask and no later.

  [sp_guard] is the rule the protocol exists for, and it is the one that
  shows what the later-free setting buys: Leaf's conclusion is
  [sp_own γ p &&{↑N}&&> ▷ f b], and the [▷] is why its clients then need
  [guards_remove_later_rhs] and a [Timeless] side condition.  Here it is
  [sp_own γ p &&{sp_wsat γ f}&&> f b].

  ** The exchange family

  Leaf proves its exchange with [own_sep_auth_incll_nondet] from
  [guarding/own_and_own_sep.v] - 530 lines of [iResUR]-level reasoning
  about [uPred_ownM] and [iRes_singleton] - which this port had dropped,
  because Iris upstreamed the *conjunction* rules ([own_and_total]) and the
  separating one was not among them.

  It is not needed.  An exchange holds [sp_own γ p1] and the authority
  [own γ (● Inved st)], learns [st ≡ p1 ⋅ z], and must move to
  [own γ (● Inved (p2 ⋅ z))] with [p2] chosen *from* [z].  That is not a
  [local_update] - a local update fixes its target before seeing the frame
  - but it is exactly a [cmra_updateP], which may choose its result after
  seeing it.  [own_auth_frag_updateP] below is that update, in forty lines:
  the frame of [● state ⋅ ◯ p1] has to be a fragment
  ([auth_frag.v]'s [auth_op_rhs_is_frag]), so [z] is determined by it and
  [p2] may be picked afterwards.

  Everything in this file is closed under the global context.

  ** What is not here

  [typing/protocol.v], the user-facing storage-protocol *types*, which is
  blocked on something else: it needs [sp_sto] and [sp_own] inside a
  *formula*, and an [Ecsem] cannot produce an [own] at a camera the client
  chose.  See [storage_protocol.v]'s header. *)

From iris.algebra Require Export cmra updates auth.
From iris.algebra Require Import proofmode_classes.
From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

From nola.bi Require Export guard modw.
From nola.iris Require Export guard.
From nola.verus_halt Require Import inved storage_protocol own_and auth_frag.

Import GuardNotation ModwNotation.

Set Default Proof Using "All".

(** ** The frame-preserving update behind every exchange

  Leaf proves this with [own_sep_auth_incll_nondet] from
  [guarding/own_and_own_sep.v], 530 lines of [iResUR]-level reasoning about
  [uPred_ownM] and [iRes_singleton].  It is a [cmra_updateP] and nothing
  more.

  The point is why it is not a [local_update].  A local update fixes its
  target before seeing the frame; here the leftover [z] - and so the [p2]
  chosen from it - *is* the frame.  A frame-preserving update to a
  *predicate* is exactly the right shape: the frame of [● state ⋅ ◯ p1]
  has to be a fragment ([auth_frag.v]'s [auth_op_rhs_is_frag]), so [z] is
  determined by it and [p2] may be picked afterwards. *)
Section auth_updateP.
  Context {Σ : gFunctors} {A : ucmra} `{!inG Σ (authUR A), !CmraDiscrete A}.

  Lemma own_auth_frag_updateP γ (p1 state : A) (ok : A → A → Prop)
    (cond : ∀ z, state ≡ p1 ⋅ z → ✓ state → ∃ p2, ok p2 z ∧ ✓ (p2 ⋅ z)) :
    own γ (● state) -∗ own γ (◯ p1) ==∗
      ∃ z p2, ⌜ok p2 z ∧ state ≡ p1 ⋅ z⌝ ∗ own γ (● (p2 ⋅ z)) ∗ own γ (◯ p2).
  Proof.
    iIntros "auth frag". iCombine "auth frag" as "own".
    iMod (own_updateP
      (λ y, ∃ z p2, y = (● (p2 ⋅ z) ⋅ ◯ p2) ∧ ok p2 z ∧ state ≡ p1 ⋅ z)
      with "own") as (y) "[%Hy own]".
    { apply cmra_discrete_updateP=> mz Hval.
      destruct mz as [w|]; simpl in Hval.
      - (* the frame is there: it must be a fragment *)
        rewrite -assoc in Hval.
        have [q Hq] := auth_op_rhs_is_frag (C:=A) state (◯ p1 ⋅ w) Hval.
        destruct w as [wa wfr]. inversion Hq as [[Ha Hpq]].
        rewrite left_id in Ha. subst wa.
        rewrite Hq in Hval.
        have [Hincl Hv] := proj1 (auth_both_valid_discrete state q) Hval.
        have [z0 Hz0] := Hincl.
        have Hst : state ≡ p1 ⋅ (wfr ⋅ z0).
        { rewrite assoc Hpq. exact Hz0. }
        have [p2 [Hok Hp2]] := cond _ Hst Hv.
        exists (● (p2 ⋅ (wfr ⋅ z0)) ⋅ ◯ p2). split.
        { by exists (wfr ⋅ z0), p2. }
        simpl. rewrite -assoc.
        have -> : (◯ p2 ⋅ View (rel:=auth_view_rel) None wfr)
          = (◯ (p2 ⋅ wfr) : authUR A) by rewrite auth_frag_op.
        apply auth_both_valid_discrete. split; [|done].
        exists z0. by rewrite -assoc.
      - (* no frame *)
        have [Hincl Hv] := proj1 (auth_both_valid_discrete state p1) Hval.
        have [z Hz] := Hincl.
        have [p2 [Hok Hp2]] := cond _ Hz Hv.
        exists (● (p2 ⋅ z) ⋅ ◯ p2). split; [by exists z, p2|].
        apply auth_both_valid_discrete. split; [|done]. apply cmra_included_l. }
    destruct Hy as (z & p2 & -> & Hok & Hst).
    iDestruct "own" as "[auth frag]". iModIntro. iExists z, p2. by iFrame.
  Qed.
End auth_updateP.

Section sp_logic.
  Context {P B : Type}.
  Context `{Equiv P, PCore P, Op P, Valid P, HPUnit: Unit P, SPRel P B}.
  Context `{Equiv B, PCore B, Op B, Valid B, Unit B}.
  Context `{equ_p: @Equivalence P (≡)}.
  Context `{equ_b: @Equivalence B (≡)}.
  Context `{storage_mixin: !StorageMixin P B}.
  Context {Σ: gFunctors}.
  Context `{sp_i: !sp_logicG storage_mixin Σ}.

  Local Notation iProp := (iProp Σ).
  Implicit Type (γ : gname) (p : P) (b : B) (f : B → iProp).

  Local Instance sm_interp_proper' : Proper ((≡) ==> (≡) ==> (↔)) sp_rel.
  Proof. destruct storage_mixin. trivial. Qed.

  Local Instance inved_proper' : Proper ((≡) ==> (≡)) (@Inved P).
  Proof. unfold Proper, "==>". intros. by unfold "≡", inved_protocol_equiv. Qed.

  (** The camera is discrete, which is what lets every inclusion below be a
    pure fact rather than an internal one. *)
  #[local] Instance sp_discrete :
    CmraDiscrete (inved_protocolR
      (internal_protocol_mixin_storage_mixin storage_mixin)).
  Proof. apply discrete_cmra_discrete. Qed.

  (** ** The three propositions

    [sp_wsat γ f] is Leaf's invariant body; [sp_sto γ f] what is persistent
    about the protocol; [sp_own γ p] a share of its state. *)
  Definition sp_wsat γ f : iProp :=
    ∃ pb : P * B,
      own γ (● Inved pb.1) ∗ ⌜sp_rel pb.1 pb.2⌝ ∗ f pb.2.

  Definition sp_sto γ f : iProp :=
    ⌜wf_prop_map f⌝ ∗ own γ (◯ (Inved (ε : P))).

  Definition sp_own γ p : iProp := own γ (◯ (Inved p)).

  Lemma pcore_inved_unit : pcore (Inved (ε : P)) ≡ Some (Inved ε).
  Proof.
    unfold pcore, inved_protocol_pcore. destruct (pcore ε) as [p|] eqn:x;
      [|trivial].
    have p_ra_mixin := (protocol_ra_mixin _ _ storage_mixin).
    have k := ra_pcore_l _ p_ra_mixin (ε : P) p x.
    generalize k. rewrite ra_comm; trivial.
    rewrite protocol_unit_left_id; trivial.
    intro R. by setoid_rewrite R.
  Qed.

  #[local] Instance pers_own_frag_inved_unit γ :
    Persistent (own γ (◯ (Inved (ε : P)))).
  Proof.
    apply own_core_persistent, auth_frag_core_id. unfold CoreId.
    apply pcore_inved_unit.
  Qed.

  #[export] Instance sp_sto_persistent γ f : Persistent (sp_sto γ f).
  Proof. exact _. Qed.
  #[export] Instance sp_own_timeless γ p : Timeless (sp_own γ p).
  Proof. exact _. Qed.
  #[export] Instance sp_own_proper γ : Proper ((≡) ==> (⊣⊢)) (sp_own γ).
  Proof. solve_proper. Qed.

  (** ** The ownership algebra *)

  Lemma own_inved_op (a a' : P) γ :
    own γ (◯ Inved a) ∗ own γ (◯ Inved a') ⊣⊢ own γ (◯ Inved (a ⋅ a')).
  Proof. by rewrite -own_op. Qed.

  Lemma sp_own_op (a a' : P) γ :
    sp_own γ (a ⋅ a') ⊣⊢ sp_own γ a ∗ sp_own γ a'.
  Proof. by rewrite /sp_own own_inved_op. Qed.

  (** [a ≼ b] in [InvedProtocol P] is [a ≼ b] in [P], because [P] is unital *)
  Lemma incl_of_inved_incl_assumes_unital (p1 p2 : P)
    (incll : @included (InvedProtocol P) (inved_protocol_equiv P)
      (inved_protocol_op P) (Inved p1) (Inved p2)) : p1 ≼ p2.
  Proof.
    unfold "≼" in incll. destruct incll as [z incll]. destruct z as [|p].
    - unfold "⋅", inved_protocol_op, "≡", inved_protocol_equiv in incll.
      unfold "≼". exists ε. setoid_rewrite (@comm P).
      + setoid_rewrite incll.
        setoid_rewrite protocol_unit_left_id; trivial. apply storage_mixin.
      + apply (ra_comm _ (protocol_ra_mixin _ _ storage_mixin)).
    - unfold "≡", inved_protocol_equiv, "⋅", inved_protocol_op in incll.
      unfold "≼". by exists p.
  Qed.

  (** Leaf's [auth_frag_conjunct], over Iris's own conjunction rule and
    [auth_frag.v]'s [auth_frag_incl]. *)
  Lemma auth_frag_conjunct γ p state :
    own γ (◯ Inved p) ∧ own γ (● Inved state) ⊢ ⌜p ≼ state⌝.
  Proof.
    rewrite and_own_discrete_ucmra. iIntros "(%c & own & %Hi)".
    destruct Hi as [Hi1 Hi2]. iDestruct (own_valid with "own") as %Hv.
    iPureIntro. apply incl_of_inved_incl_assumes_unital.
    exact (auth_frag_incl _ _ _ Hi2 Hi1 Hv).
  Qed.

  Lemma auth_frag_conjunct_to_incl γ p state (W : iProp) :
    own γ (◯ Inved p) ∧ (own γ (● Inved state) ∗ W) ⊢ ⌜p ≼ state⌝.
  Proof.
    iIntros "x".
    iAssert (own γ (◯ Inved p) ∧ own γ (● Inved state))%I with "[x]" as "t".
    { iSplit; [by iDestruct "x" as "[$ _]"|by iDestruct "x" as "[_[$ _]]"]. }
    by iApply auth_frag_conjunct.
  Qed.

  (** ** SP-Guard, later-free

    Leaf's [sp_guard], whose conclusion is [sp_own γ p &&{↑N}&&> ▷ f b].  The
    [▷] is gone and the mask is the world satisfaction. *)
  Lemma sp_guard_wf p b γ f (g : storage_protocol_guards p b)
      (wfm : wf_prop_map f) :
    ⊢ sp_own γ p &&{sp_wsat γ f}&&> f b.
  Proof.
    (* A guard to the whole world satisfaction, which is an existential *)
    iDestruct (guard_wsat_out (W:=sp_wsat γ f) (W':=sp_wsat γ f)
      (P:=sp_own γ p)) as "g".
    rewrite {2}/sp_wsat.
    (* Strengthen it with what holding [sp_own γ p] beside it forces *)
    have Hs : ∀ a : P * B,
      (sp_own γ p ∧ (own γ (● Inved a.1) ∗ ⌜sp_rel a.1 a.2⌝ ∗ f a.2))
        ⊢ ⌜p ≼ a.1⌝.
    { move=> a. rewrite /sp_own.
      iApply (auth_frag_conjunct_to_incl γ p a.1
        (⌜sp_rel a.1 a.2⌝ ∗ f a.2)). }
    iDestruct (guard_exist_strengthen_lhs (A:=(P * B)%type)
      (S:=λ a : P * B, ⌜p ≼ a.1⌝%I) Hs (λ _, bi.pure_persistent _)
      with "g") as "gg".
    (* ...and read [f b] off it *)
    destruct wfm as [fprop [funit fop]].
    iAssert ((∃ a : P * B,
      (own γ (● Inved a.1) ∗ ⌜sp_rel a.1 a.2⌝ ∗ f a.2) ∗ ⌜p ≼ a.1⌝)
        &&{sp_wsat γ f}&&> f b)%I as "g2".
    { iApply guard_intro.
      iIntros "!> (%pb & (auth & %Hrel & fb) & %Hincl)".
      have [z Hz] := Hincl.
      have Hrel' : sp_rel (p ⋅ z) pb.2.
      { by setoid_rewrite <-Hz. }
      have [bz Hbz] := g z pb.2 Hrel'.
      have Hval : ✓ (b ⋅ bz).
      { destruct (base_ra_mixin _ _ storage_mixin). setoid_rewrite <-Hbz.
        exact (interp_val _ _ storage_mixin _ _ Hrel'). }
      have Hsplit : f pb.2 ⊣⊢ f b ∗ f bz.
      { rewrite (fprop _ _ Hbz). exact (fop _ _ Hval). }
      rewrite Hsplit. iDestruct "fb" as "[$ fbz]".
      iIntros "fb". iExists pb. rewrite Hsplit.
      iSplitL; [|by iPureIntro]. iFrame "auth fb fbz". by iPureIntro. }
    iApply (guard_trans with "gg g2").
  Qed.

  (** [sp_sto] is only ever used for the well-formedness it carries, so the
    rule holds of any well-formed [f] whether or not a [sp_sto] is held.
    That is what [typing/protocol.v] needs: it builds a *stored* guard, at
    an interpretation where it holds no resource at all. *)
  Lemma sp_guard p b γ f (g : storage_protocol_guards p b) :
    sp_sto γ f ⊢ sp_own γ p &&{sp_wsat γ f}&&> f b.
  Proof. iIntros "[%wfm _]". by iApply sp_guard_wf. Qed.

  (** ** The exchange family

    Leaf's [own_sep_inv_incll_helper_nondet]: the pure core, verbatim. *)
  Definition unInved (z : InvedProtocol P) : P :=
    match z with Inved z0 => z0 | Nah => ε end.

  Lemma inved_op_unInved (a : P) z : Inved a ⋅ z ≡ Inved (a ⋅ unInved z).
  Proof.
    have Hru : a ⋅ ε ≡ a.
    { rewrite (ra_comm _ (protocol_ra_mixin _ _ storage_mixin)).
      apply (protocol_unit_left_id _ _ storage_mixin). }
    destruct z as [|z0]; [|done]. simpl. by setoid_rewrite Hru.
  Qed.

  Lemma own_sep_inv_incll_helper_nondet (p1 st : P) (t1 : B)
      (output_ok : P → P → Prop)
      (cond : ∀ q, sp_rel (p1 ⋅ q) t1 →
        ∃ p2 t2, output_ok p2 q ∧ sp_rel (p2 ⋅ q) t2) :
    ∀ z : InvedProtocol P, sp_rel st t1 → ✓ (Inved st) →
      Inved p1 ⋅ z ≡ Inved st →
      ∃ p2, output_ok p2 (unInved z) ∧ ✓ (Inved p2 ⋅ z).
  Proof.
    move=> z inv v eq.
    have Hru : ∀ x : P, x ⋅ ε ≡ x.
    { move=> x. rewrite (ra_comm _ (protocol_ra_mixin _ _ storage_mixin)).
      apply (protocol_unit_left_id _ _ storage_mixin). }
    destruct z as [|p].
    - unfold "⋅", inved_protocol_op, "≡", inved_protocol_equiv in eq.
      unfold "⋅", inved_protocol_op, "✓", inved_protocol_valid, unInved.
      have pi2 : sp_rel (p1 ⋅ (ε : P)) t1.
      { by setoid_rewrite (Hru p1); setoid_rewrite eq. }
      have [p2 [t2 [oo c]]] := cond ε pi2.
      exists p2. split; [done|]. exists ε. unfold pinv, sp_rel_pinv.
      by exists t2.
    - unfold "⋅", inved_protocol_op, "≡", inved_protocol_equiv in eq.
      unfold "⋅", inved_protocol_op, "✓", inved_protocol_valid, unInved.
      have pi2 : sp_rel (p1 ⋅ p) t1 by setoid_rewrite eq.
      have [p2 [t2 [oo c]]] := cond p pi2.
      exists p2. split; [done|]. exists ε. unfold pinv, sp_rel_pinv.
      exists t2. by setoid_rewrite (Hru (p2 ⋅ p)).
  Qed.

  (** Leaf's [own_sep_inv_incll_nondet], over [own_auth_frag_updateP] rather
    than over 530 lines of [iResUR] reasoning. *)
  Lemma own_sep_inv_incll_nondet γ (p1 st : P) (t1 : B)
      (output_ok : P → P → Prop)
      (cond : ∀ q, sp_rel (p1 ⋅ q) t1 →
        ∃ p2 t2, output_ok p2 q ∧ sp_rel (p2 ⋅ q) t2)
      (pi : sp_rel st t1) :
    own γ (◯ Inved p1) -∗ own γ (● Inved st) ==∗
      ∃ z p2 : P, ⌜output_ok p2 z ∧ st ≡ p1 ⋅ z⌝
        ∗ own γ (◯ Inved p2) ∗ own γ (● Inved (p2 ⋅ z)).
  Proof.
    iIntros "frag auth".
    iMod (own_auth_frag_updateP _ (Inved p1) (Inved st)
      (λ y z, ∃ p2 : P, y = Inved p2 ∧ output_ok p2 (unInved z))
      with "auth frag") as (z y) "(%Hok & auth & frag)".
    { move=> z Heq Hv.
      have [p2 [Hoo Hval]] := own_sep_inv_incll_helper_nondet p1 st t1
        output_ok cond z pi Hv (symmetry Heq).
      exists (Inved p2). split; [by exists p2|done]. }
    destruct Hok as [[p2 [-> Hoo]] Hst].
    iModIntro. iExists (unInved z), p2.
    rewrite (inved_op_unInved p2 z). iFrame "auth frag". iPureIntro.
    split; [done|]. move: Hst. by rewrite (inved_op_unInved p1 z).
  Qed.

  (** *** SP-Exchange, nondeterministic

    Leaf's conclusion is [… ={{[γ]}}=∗ …] with [▷ f b1] and [▷ f b2]; here
    the mask is the world satisfaction and the laters are gone. *)
  Lemma sp_exchange_nondeterministic p1 b1 (output_ok : P → B → Prop) γ f
      (exchng : storage_protocol_exchange_nondeterministic p1 b1 output_ok) :
    sp_sto γ f -∗ sp_own γ p1 -∗ f b1 -∗ sp_wsat γ f ==∗
      (∃ p2 b2, ⌜output_ok p2 b2⌝ ∗ sp_own γ p2 ∗ f b2) ∗ sp_wsat γ f.
  Proof.
    iIntros "[%wfm _] own fb (%pb & auth & %Hrel & ft)".
    destruct wfm as [fprop [funit fop]].
    iMod (own_sep_inv_incll_nondet γ p1 pb.1 pb.2
      (λ p2 q, ∃ b2 t2, output_ok p2 b2 ∧ sp_rel (p2 ⋅ q) t2
        ∧ ✓ (pb.2 ⋅ b1) ∧ pb.2 ⋅ b1 ≡ t2 ⋅ b2)
      with "own auth") as (z p2) "([%Hbig %Hincl] & own & auth)".
    { move=> q Hq. have [p2' [b2 [t2 Hex]]] := exchng q pb.2 Hq.
      exists p2', t2. split; [|tauto]. exists b2, t2. tauto. }
    { done. }
    destruct Hbig as [b2 [t2 [Hoo [Hpix [Hvix Heq]]]]].
    have Hval2 : ✓ (t2 ⋅ b2).
    { destruct (base_ra_mixin _ _ storage_mixin). by setoid_rewrite <-Heq. }
    have Hsp : f pb.2 ∗ f b1 ⊣⊢ f t2 ∗ f b2.
    { rewrite -(fop _ _ Hvix) (fprop _ _ Heq). exact (fop _ _ Hval2). }
    iCombine "ft fb" as "fs". iEval (rewrite Hsp) in "fs".
    iDestruct "fs" as "[ft fb]".
    iModIntro. iSplitR "auth ft".
    { iExists p2, b2. by iFrame. }
    iExists (p2 ⋅ z, t2). by iFrame.
  Qed.

  (** *** SP-Exchange *)
  Lemma sp_exchange p1 p2 b1 b2 γ f
      (exchng : storage_protocol_exchange p1 p2 b1 b2) :
    sp_sto γ f -∗ sp_own γ p1 -∗ f b1 -∗ sp_wsat γ f ==∗
      (sp_own γ p2 ∗ f b2) ∗ sp_wsat γ f.
  Proof.
    iIntros "#sto own fb W".
    iMod (sp_exchange_nondeterministic p1 b1
      (λ p2' b2', p2' = p2 ∧ b2' = b2) γ f with "sto own fb W")
      as "[(%p2' & %b2' & %Hoo & own & fb) $]".
    { move=> q t1 Hq. have [t2 Hex] := exchng q t1 Hq.
      exists p2, b2, t2. tauto. }
    destruct Hoo as [-> ->]. by iFrame.
  Qed.

  (** *** SP-Update, SP-Withdraw, SP-Deposit

    Leaf derives all three from the exchange by taking one side to be the
    unit, and so does this. *)
  Local Lemma base_right_id : ∀ x : B, x ⋅ ε ≡ x.
  Proof.
    move=> x. rewrite (ra_comm _ (base_ra_mixin _ _ storage_mixin)).
    apply (base_unit_left_id _ _ storage_mixin).
  Qed.

  Local Lemma sto_unit γ f : sp_sto γ f -∗ f (ε : B).
  Proof.
    iIntros "[%wfm _]". destruct wfm as [fprop [funit fop]].
    by rewrite funit.
  Qed.

  Lemma sp_update p1 p2 γ f (upd : storage_protocol_update p1 p2) :
    sp_sto γ f -∗ sp_own γ p1 -∗ sp_wsat γ f ==∗ sp_own γ p2 ∗ sp_wsat γ f.
  Proof.
    have Hex : storage_protocol_exchange p1 p2 (ε : B) (ε : B).
    { move=> q t1 Hq. exists t1. split; [by apply upd|]. split; [|done].
      destruct (base_ra_mixin _ _ storage_mixin).
      setoid_rewrite (base_right_id t1).
      exact (interp_val _ _ storage_mixin _ _ Hq). }
    iIntros "#sto own W". iDestruct (sto_unit with "sto") as "fe".
    iMod (sp_exchange p1 p2 ε ε γ f Hex with "sto own fe W")
      as "[[$ _] $]". done.
  Qed.

  Lemma sp_withdraw p1 p2 b2 γ f
      (wd : storage_protocol_withdraw p1 p2 b2) :
    sp_sto γ f -∗ sp_own γ p1 -∗ sp_wsat γ f ==∗
      (sp_own γ p2 ∗ f b2) ∗ sp_wsat γ f.
  Proof.
    have Hex : storage_protocol_exchange p1 p2 (ε : B) b2.
    { move=> q t1 Hq. have [t2 [Hr Ht]] := wd q t1 Hq. exists t2.
      split; [done|]. destruct (base_ra_mixin _ _ storage_mixin).
      setoid_rewrite (base_right_id t1). split; [|done].
      exact (interp_val _ _ storage_mixin _ _ Hq). }
    iIntros "#sto own W". iDestruct (sto_unit with "sto") as "fe".
    iMod (sp_exchange p1 p2 ε b2 γ f Hex with "sto own fe W") as "[$ $]".
    done.
  Qed.

  Lemma sp_deposit p1 p2 b1 γ f
      (dep : storage_protocol_deposit p1 p2 b1) :
    sp_sto γ f -∗ sp_own γ p1 -∗ f b1 -∗ sp_wsat γ f ==∗
      sp_own γ p2 ∗ sp_wsat γ f.
  Proof.
    have Hex : storage_protocol_exchange p1 p2 b1 (ε : B).
    { move=> q t1 Hq. have [t2 [Hr [Hv Ht]]] := dep q t1 Hq. exists t2.
      split; [done|]. split; [done|].
      destruct (base_ra_mixin _ _ storage_mixin).
      by setoid_rewrite (base_right_id t2). }
    iIntros "#sto own fb W".
    iMod (sp_exchange p1 p2 b1 ε γ f Hex with "sto own fb W")
      as "[[$ _] $]". done.
  Qed.

  (** ** Allocating a protocol

    Leaf's [sp_alloc] allocates the invariant; here it produces the world
    satisfaction, which the caller then threads. *)
  Lemma sp_alloc p b f (Hrel : sp_rel p b) (wfm : wf_prop_map f) :
    f b ==∗ ∃ γ, sp_sto γ f ∗ sp_own γ p ∗ sp_wsat γ f.
  Proof.
    have Hunit : ∀ x : P, ε ⋅ x ≡ x.
    { apply (protocol_unit_left_id _ _ storage_mixin). }
    iIntros "fb".
    iMod (own_alloc (● Inved p ⋅ ◯ Inved p)) as (γ) "[auth frag]".
    { apply auth_both_valid_discrete. split.
      - by exists Nah.
      - exists ε, b. have Hc : p ⋅ ε ≡ p.
        { rewrite (ra_comm _ (protocol_ra_mixin _ _ storage_mixin)).
          apply Hunit. }
        by setoid_rewrite Hc. }
    iAssert (own γ (◯ Inved (ε : P)) ∗ own γ (◯ Inved p))%I with "[frag]"
      as "[#unit frag]".
    { rewrite own_inved_op. by setoid_rewrite (Hunit p). }
    iModIntro. iExists γ. iSplitR.
    { rewrite /sp_sto. iSplitR; [done|]. iExact "unit". }
    rewrite /sp_own /sp_wsat. iFrame "frag". iExists (p, b). by iFrame.
  Qed.

  (** ** SP-Unit, SP-Mono, SP-Valid and the conjunction rule

    Leaf's [sp_own_unit], [sp_own_mono], [sp_own_valid], [sp_own_and] and
    [sp_own_and_specific].  None of them touches a later or an invariant, so
    all five are Leaf's, read over the world satisfaction instead of the
    mask.  They are what the *typing* rules of
    [nola/verus_halt/typing/protocol.v] need beyond the exchange family. *)

  (** *** SP-Unit *)
  Lemma sp_own_unit γ f : sp_sto γ f ⊢ sp_own γ (ε : P).
  Proof. by iIntros "[_ $]". Qed.

  (** *** SP-Mono *)
  Lemma sp_own_mono γ a1 a2 : a2 ≼ a1 → sp_own γ a1 ⊢ sp_own γ a2.
  Proof.
    move=> [t Heq]. rewrite (sp_own_proper γ _ _ Heq) sp_own_op.
    by iIntros "[$ _]".
  Qed.

  (** *** SP-Valid

    [✓ Inved p] is [∃ b, pinv (p ⋅ b)] by [inved.v]'s very definition, and
    [pinv] is [sp_rel]'s existential ([storage_protocol.v]'s [sp_rel_pinv]),
    so holding a share says the protocol has *some* completion. *)
  Lemma sp_own_valid γ p : sp_own γ p ⊢ ⌜∃ q b, sp_rel (p ⋅ q) b⌝.
  Proof.
    rewrite /sp_own. iIntros "own". iDestruct (own_valid with "own") as %Hv.
    iPureIntro. move: Hv. rewrite auth_frag_valid=> [[q [b ?]]]. by exists q, b.
  Qed.

  (** *** The conjunction rule

    Two shares seen under the *non-separating* conjunction are two shares of
    one state.  Iris's [own_and] gives a common upper bound in the [auth]
    camera; [auth_frag.v]'s [view_frag_included_frag] turns it into a
    *fragment*, and [incl_of_inved_incl_assumes_unital] reads the inclusion
    back in [P]. *)
  Lemma sp_own_and x y γ :
    sp_own γ x ∧ sp_own γ y ⊢ ∃ z, ⌜x ≼ z ∧ y ≼ z⌝ ∗ sp_own γ z.
  Proof.
    rewrite /sp_own and_own_discrete_ucmra.
    iIntros "(%c & own & %Hi)". destruct Hi as [Hx Hy].
    have [bz [Hmax Hle]] := view_frag_included_frag c.
    destruct bz as [|z].
    { (* [Nah] is above no [Inved], so the bound is an [Inved] *)
      exfalso. have [z2 Hz2] := Hmax _ Hx. by destruct z2. }
    iExists z. iSplitR.
    { iPureIntro. split; apply incl_of_inved_incl_assumes_unital;
        [exact (Hmax _ Hx)|exact (Hmax _ Hy)]. }
    iApply (own_mono with "own"). exact Hle.
  Qed.

  Lemma sp_own_and_specific x y z γ :
    (∀ w, x ≼ w ∧ y ≼ w → z ≼ w) →
    sp_own γ x ∧ sp_own γ y ⊢ sp_own γ z.
  Proof.
    move=> Hw. rewrite sp_own_and. iIntros "(%w & [%Hx %Hy] & own)".
    iApply (sp_own_mono with "own"). by apply Hw.
  Qed.
End sp_logic.
