(** * Execution levels for the port: one package of ghost state per level

  [typing/levels.v] builds the level machinery abstractly, over a bare
  [sinv] family.  This file builds it for the *port's own* world
  satisfaction, which is the first step PLAN.md's item 2 lists:

  >  1. [alerusGS_at : nat → alerusGS FML Σ] and
  >     [alerus_wsat_below j := ∗_{k<j} alerus_wsat (GS k) (Sem k)], which is
  >     [lvs_below] with [alerus_wsat] in place of [lv_wsat].

  Why a *package* rather than a ghost name.  [typing/strat.v] settles that
  one world satisfaction at one interpretation cannot serve two levels: a
  caller at level [i] must hand a callee at level [j ≤ i] a world
  satisfaction it can give away, and the callee's is interpreted by
  [⟦⟧ᶜ_j].  [alerus_wsat ⟦⟧ᶜ_j] and [alerus_wsat ⟦⟧ᶜ_i] are the same ghost
  state under different [BorSem]s and neither entails the other, so the
  split has to be in the ghost state.

  What divides, and what does not.

  - *Per level*: everything that holds a formula, i.e. everything whose
    world satisfaction mentions [bor_sem] - the lifetime logic's box and
    shared-borrow families, the non-atomic and cancellable non-atomic
    invariants, the fractional guards, the store.  Each is a ghost
    *name* beside a [_pre] class, so [L] of them come out of one [Σ].
  - *Shared*: the heap, the invariant machinery, the prophecies and the
    unique-borrow ghost state.  The thesis shares the heap for the same
    reason - it lives in the state interpretation, not in [Winv] - and
    the prophecy assertions of a type at level [k] have to be the same
    propositions as those of a type at level [i], or no rule relating the
    two levels could be stated at all.

  [send_wsat] is shared too, and that is a fact rather than a choice:
  it is [cna_lifetimes atomic_pool_name ∅], whose [own] is at an [inG] of
  [cnaGpreS] and at a pool name from [uniqG], so it does not mention
  [cna_name] and is literally the same proposition at every level.  It
  therefore sits *beside* the family, as [alerus_wsat] has it sit beside
  [alerus_wsat_core].

  Nothing here levels the *interpretation*: [Csem] is still a parameter,
  so each level is the same interpretation at different ghost state.
  Making level [k]'s interpretation call only levels [< k] - which is what
  [fn_fml] needs - is a later step, and it is the one that needs a level
  on every type former.

  **One thing this file still gets wrong on purpose.**  [alerusNames]
  carries a whole [llft_logicGS], so each level here has its own
  *lifetime tokens* as well as its own borrows: [@[κ]] at level [k] is a
  different proposition from [@[κ]] at level [j], and nothing transfers
  between them.  That is the tower of lifetime logics PLAN.md calls
  prohibitive, and it is not the design.

  What the design wants is [llft_name], [d_name], [log_name],
  [mint_name], [oset_name] and [osub_name] shared for the whole run, and
  only [bor_name] and [o_name] - and with them the box and the
  shared-borrow family - varying with the level.  Everything that stood
  in the way of that is now gone, and the record of what each step cost
  is in PLAN.md:

  - [lifetime/ra.v]'s split made the two halves nameable apart.
  - A level's view of the dead set may *lag* the shared kill order and
    catch up lazily ([lifetime/level.v]); so may its outlives relation,
    bounded by an [Osub] fragment.  That is what made a level's piece of
    the invariant a *closed* proposition, which is what lets several of
    them be held at once as [∗_{k<j} Wbor_k].
  - The lifetime logic no longer fixes the world its *stored* guards -
    inclusions, indexed borrows', the outlives guards - live at: it
    takes a family ([LlftWG]'s [llft_Wix]/[llft_Wmore]), each of whose
    worlds extends the ambient one.  That is what a guard stored at
    level [k] and opened by a body holding [∗_{h<j} Wbor_h] needs.
  - [bor_name] and [o_name] are now [LlftBorNames], a class of their
    own, so [llft_wsatG] is a function of the level's borrow names.

  What is left is therefore *construction*, not expressibility: a lemma
  allocating one level's borrow machinery against the *existing* shared
  state (a second [bor_alloc]/[outlives_alloc]/box/shared-borrow family,
  with [lv_inv] at the empty prefix of the kill order), and the split of
  [alerus_wsat_core] into the half held once and the half held per
  level, so that [alerus_wsat_below P ns j] is [∗_{k<j} Wbor_k] beside
  one shared copy rather than [j] copies of everything.

  So what is sound here is the *shape*: [L] packages out of one [Σ],
  [∗_{k<j} Winv_k], and [ty-lev].  Which ghost state each package may
  vary is the thing being fixed next. *)

From iris.algebra Require Import gmap_view agree auth gset.
From iris.proofmode Require Import proofmode.
From nola.alerus.lang Require Import adequacy proofmode notation.
From nola.alerus.typing Require Export model_inst.
From nola.alerus.typing Require Import type_context programs.
From nola.bi Require Import modw wpw.
Import ModwNotation WpwNotation iPropAppNotation.

(** ** The ghost state, before allocation

  Moved here from [typing/soundness.v], which now takes it from this file:
  allocating one level and allocating [L] of them are the same lemma. *)
Class alerusGpreS (FML : oFunctor) Σ : Type := AlerusGpreS {
  #[global] alerus_preG_lrust :: lrustGpreS FML Σ;
  #[global] alerus_preG_llft :: llft_logicGpreS Σ;
  #[global] alerus_preG_sinv :: sinvGpreS FML Σ;
  #[global] alerus_preG_proph :: prophPreG Σ;
  #[global] alerus_preG_uniq :: uniqPreG Σ;
  #[global] alerus_preG_cna :: cnaGpreS FML Σ;
  #[global] alerus_preG_frac :: fracGuardGpreS FML Σ;
  #[global] alerus_preG_eternal :: inG Σ (authUR (gsetUR lft));
  #[global] alerus_preG_llctx ::
    inG Σ (gmap_viewR gname (agreeR (leibnizO llctx)));
  #[global] alerus_preG_lfts ::
    inG Σ (gmap_viewR gname (agreeR (leibnizO (gmultiset lft))));
  #[global] alerus_preG_twostate :: twostateG Σ;
}.

Definition alerusΣ FML `{!oFunctorContractive FML} : gFunctors :=
  #[lrustΣ FML; llft_logicΣ; sinvΣ FML; prophΣ; uniqΣ; cnaΣ FML;
    fracGuardΣ FML; GFunctor (constRF (authUR (gsetUR lft)));
    fracKeyΣ llctx; fracKeyΣ (gmultiset lft); twostateΣ].

(** [solve_inG] does not scale here.  Its last step is
  [split; (assumption || by apply _)], which hands each of the ten fields
  to typeclass resolution; on [lrustGpreS FML Σ] that search does not
  terminate in any practical time (measured: over eight hours, against
  0.00s for the named instance).  So the fields are discharged by name,
  and the [subΣ] hypothesis is taken apart one entry at a time rather
  than by [repeat], so that each entry has a name to be discharged by. *)
#[export] Instance subG_alerusGpreS {FML Σ} `{!oFunctorContractive FML} :
  subG (alerusΣ FML) Σ → alerusGpreS FML Σ.
Proof.
  intros H. unfold alerusΣ in H.
  apply subG_inv in H as [Hlrust H]. apply subG_inv in H as [Hllft H].
  apply subG_inv in H as [Hsinv H]. apply subG_inv in H as [Hproph H].
  apply subG_inv in H as [Huniq H]. apply subG_inv in H as [Hcna H].
  apply subG_inv in H as [Hfrac H]. apply subG_inv in H as [Hetern H].
  apply subG_inv in H as [Hllctx H]. apply subG_inv in H as [Hlfts H].
  apply subG_inv in H as [Hts _].
  split.
  - by apply subG_lrustGpreS.
  - by apply subG_lt_logicΣ.
  - by apply subG_sinvΣ.
  - by apply subG_prophPreG.
  - by apply subG_uniqPreG.
  - by apply subG_cnaGpreS.
  - by apply subG_fracGuardGpreS.
  - exact (subG_inG _ _ Hetern).
  - by apply subG_fracKeyGpreS.
  - by apply subG_fracKeyGpreS.
  - exact (subG_inG _ _ Hts).
Qed.

(** ** The world satisfaction, as a function of the ghost state

  [alerus_wsat] and [alerus_wsat_core] are stated in a section that fixes
  an [alerusGS] as an *instance*, so with two of them in scope neither can
  be named.  These are the same definitions with every class argument
  explicit, which is what a family indexed by the level needs. *)
Section wsat_at.
  Context `{!typingC CON} {JUDG Σ} `{!alerusGS (cifOF CON) Σ,
    !typingJ CON JUDG Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
    !typingCS CON JUDG Σ, !typingJS CON JUDG Σ}.

  Definition alerus_wsat_core_at : iProp Σ := alerus_wsat_core.
  Definition alerus_wsat_at : iProp Σ := alerus_wsat.
  Definition alerus_WGuard_at' : iProp Σ := alerus_WGuard.

  (** The two halves, with every class argument explicit, which is what
    a family indexed by the level needs: [alerus_wsat_shared_at] is held
    *once*, at the bottom level's package, and [alerus_wsat_lvl_at] is
    held once per level. *)
  Definition alerus_wsat_shared_at : iProp Σ := alerus_wsat_shared.
  Definition alerus_wsat_lvl_at : iProp Σ := alerus_wsat_lvl.

  Lemma alerus_wsat_core_at_split :
    alerus_wsat_core_at ⊣⊢ alerus_wsat_shared_at ∗ alerus_wsat_lvl_at.
  Proof. exact alerus_wsat_core_split. Qed.

  Lemma alerus_wsat_at_eq : alerus_wsat_at = alerus_wsat.
  Proof. done. Qed.
  Lemma alerus_wsat_core_at_eq : alerus_wsat_core_at = alerus_wsat_core.
  Proof. done. Qed.
End wsat_at.

Section level.
  Context `{!typingC CON} {JUDG Σ}
    `{!alerusGpreS (cifOF CON) Σ, !invGS_gen HasNoLc Σ,
      !typingJ CON JUDG Σ}.

  (** *** One level's ghost names

    Every field is either a bare [gname] or a record that is a [_pre] class
    plus bare [gname]s; none of them adds a component to the global camera,
    which is why there is no maximum level here any more than in
    [typing/levels.v]. *)
  Record alerusNames : Type := AlerusNames {
    (** The borrow bookkeeping's two names.  Since [lifetime/ra.v]'s
      split these are separable from the rest of the lifetime logic,
      and they are what a level varies.  The lifetime tokens, the kill
      order, the minted atoms and the outlives relation's shared half
      are one per *run* and are no longer in this record: they are
      handed to [alerusGS_of] beside the heap, the prophecies and the
      unique borrows. *)
    an_bor : LlftBorNames Σ;
    an_sinv : sinvGS (cifOF CON) Σ;
    an_naInv : gname;
    an_cna : cnaGS (cifOF CON) Σ;
    an_frac : fracGuardGS (cifOF CON) Σ;
    an_llctx : fracKeyGS llctx Σ;
    an_lfts : fracKeyGS (gmultiset lft) Σ;
    an_shr : gname;
    an_eternal : gname;
    an_store : gname;
  }.

  (** The port's [alerusGS_at]: one level's ghost state, with the shared
    parts - the heap, the prophecies, the unique borrows - handed in. *)
  Definition alerusGS_of (hLlft : llft_logicGS Σ)
      (hGS : heapGS (cifOF CON) Σ)
      (hP : prophG Σ) (hU : uniqG Σ) (n : alerusNames)
    : alerusGS (cifOF CON) Σ :=
    AlerusGS (cifOF CON) Σ _ hLlft (an_bor n) (an_sinv n) hGS
      (NaInvGS (cifOF CON) Σ (@sinvGS_pre _ _ (an_sinv n)) _ (an_naInv n))
      _ hP hU (an_cna n) (an_frac n) _ (an_llctx n) (an_lfts n) _
      (an_shr n) (an_eternal n) (an_store n).

  (** *** Allocating one level

    The names come out first and the interpretation goes in afterwards, for
    the reason the rest of this port records: [bor_sem] is [⟦⟧ᶜ(der)] and
    its [Csem] mentions the very ghost state being allocated. *)
  Lemma alerus_names_alloc :
    ⊢ |==> ∃ (hLlft : llft_logicGS Σ) (n : alerusNames),
      llft_shared_wits ∗ ∀ (hGS : heapGS (cifOF CON) Σ)
      (hP : prophG Σ) (hU : uniqG Σ) (Cs : Csem CON JUDG Σ)
      (Js : Jsem JUDG (iProp Σ))
      (CS : @typingCS CON JUDG Σ _ (alerusGS_of hLlft hGS hP hU n) _ Cs Js),
      @alerus_wsat_core_at CON _ JUDG Σ (alerusGS_of hLlft hGS hP hU n) _
        Cs Js CS.
  Proof.
    iMod (frac_key_wsat_alloc (K:=llctx)) as (Hllctx) "Wllctx".
    iMod (frac_key_wsat_alloc (K:=gmultiset lft)) as (Hlfts) "Wlfts".
    (* [K] has to be given: the lifetime logic's minted-atom camera is
      another [inG Σ (authUR (gsetUR _))], so resolution would otherwise
      pick [lt_atom] here. *)
    iMod (eternal_wsat_alloc (K:=lft)) as (γe) "We".
    iMod (frac_wsat_alloc (FML:=cifOF CON)) as (Hfrac) "Wfrac".
    iMod (llft_wsat_alloc (FML:=cifOF CON)) as (Hllft Hbor Hsinv shr)
      "[#Wits Wllft]".
    iMod (na_inv_wsat_alloc_name (FML:=cifOF CON)) as (γna) "Wna".
    iMod (cna_wsat_alloc (FML:=cifOF CON)) as (Hcna) "Wcna".
    iMod (sinv_wsat_alloc_name (FML:=cifOF CON) (sinvGS0 := Hsinv))
      as (γst) "Wstore".
    iModIntro.
    iExists Hllft,
      (AlerusNames Hbor Hsinv γna Hcna Hfrac Hllctx Hlfts shr γe γst).
    iFrame "Wits".
    iIntros (hGS hP hU Cs Js CS).
    rewrite /alerus_wsat_core_at /alerus_wsat_core.
    iSplitR "Wcna Wna"; last first.
    { iSplitL "Wcna"; first by iApply "Wcna".
      iApply "Wna". iApply ne_internal_ne; try exact _. }
    iApply ("Wllft" $! _ alerus_WG). rewrite /alerus_WG.
    iSplitL "We"; first iApply "We".
    iSplitL "Wfrac"; first (iApply "Wfrac"; iApply ne_internal_ne;
      try exact _).
    iSplitL "Wllctx"; first iExact "Wllctx".
    iSplitL "Wlfts"; first iExact "Wlfts".
    rewrite /alerus_store_wsat dinv_wsat_sinv. iApply "Wstore".
    iIntros (?). iApply ne_internal_ne; try exact _.
  Qed.

  (** *** Allocating a *further* level

    The same, against a lifetime logic that already exists: no second
    [llft_logicGS], so no second copy of the lifetime tokens, the kill
    order, the minted atoms or the outlives relation.  What comes out is
    the level's half alone - [llft_bor_wsat_alloc] is what makes that
    possible, and the level is born at the empty prefix of the kill
    order, which is sound because a level may lag. *)
  Lemma alerus_names_alloc_more (hLlft : llft_logicGS Σ) :
    llft_shared_wits -∗ |==> ∃ n : alerusNames,
      ∀ (hGS : heapGS (cifOF CON) Σ)
      (hP : prophG Σ) (hU : uniqG Σ) (Cs : Csem CON JUDG Σ)
      (Js : Jsem JUDG (iProp Σ))
      (CS : @typingCS CON JUDG Σ _ (alerusGS_of hLlft hGS hP hU n) _ Cs Js),
      @alerus_wsat_lvl_at CON _ JUDG Σ (alerusGS_of hLlft hGS hP hU n) _
        Cs Js CS.
  Proof.
    iIntros "#Wits".
    iMod (frac_key_wsat_alloc (K:=llctx)) as (Hllctx) "Wllctx".
    iMod (frac_key_wsat_alloc (K:=gmultiset lft)) as (Hlfts) "Wlfts".
    iMod (eternal_wsat_alloc (K:=lft)) as (γe) "We".
    iMod (frac_wsat_alloc (FML:=cifOF CON)) as (Hfrac) "Wfrac".
    iMod (llft_bor_wsat_alloc (FML:=cifOF CON) with "Wits")
      as (Hbor Hsinv shr) "Wbor".
    iMod (na_inv_wsat_alloc_name (FML:=cifOF CON)) as (γna) "Wna".
    iMod (cna_wsat_alloc (FML:=cifOF CON)) as (Hcna) "Wcna".
    iMod (sinv_wsat_alloc_name (FML:=cifOF CON) (sinvGS0 := Hsinv))
      as (γst) "Wstore".
    iModIntro.
    iExists (AlerusNames Hbor Hsinv γna Hcna Hfrac Hllctx Hlfts shr γe γst).
    iIntros (hGS hP hU Cs Js CS).
    rewrite /alerus_wsat_lvl_at /alerus_wsat_lvl.
    iSplitR "Wbor Wcna Wna"; last first.
    { iDestruct ("Wbor" $! _ _ _ _) as "[Wbw Wbo]".
      iFrame "Wbw Wbo". iSplitL "Wcna"; first by iApply "Wcna".
      iApply "Wna". iApply ne_internal_ne; try exact _. }
    rewrite /alerus_WG.
    iSplitL "We"; first iApply "We".
    iSplitL "Wfrac"; first (iApply "Wfrac"; iApply ne_internal_ne;
      try exact _).
    iSplitL "Wllctx"; first iExact "Wllctx".
    iSplitL "Wlfts"; first iExact "Wlfts".
    rewrite /alerus_store_wsat dinv_wsat_sinv. iApply "Wstore".
    iIntros (?). iApply ne_internal_ne; try exact _.
  Qed.
End level.

(** ** The family, and the thesis's [∗_{k<j} Winv_k]

  A level is a package: its ghost names, and the semantics of the formula
  language *at* them.  The semantics has to be part of it because
  [typingCS]/[typingJS] are stated about the ghost state - the point of
  [AlerusSem] being split off [alerusGS] ([typing/ctx.v]) is that one ghost
  state can carry several interpretations, and here several ghost states
  carry one interpretation.

  The semantics is a function of the level's *position* as well as its
  names, [∀ k n, LvlAt n].  That is not decoration.  A level's [Csem] is
  built from the constructors and the constructors from the ghost state,
  so the names alone would do - until [fn_fml].  A function type's ghost
  assertion has to be a formula whose semantics mentions no candidate
  ([typing/function.v]'s [fn_fml_sem], and [nola/bi/deriv.v]'s
  [der_const] for why that is the whole obligation), and the only way to
  have one is to read the body at the interpretation of a level *below*
  this one - already constructed when this one is being defined.  Taking
  [P] at the position is what lets the family be built by induction on
  it, with level [k]'s [lvl_Cs] and [lvl_Js] mentioning [P j] for
  [j < k].  [LvlAt] already gives every level its own [Csem] and [Jsem];
  this is what lets them differ *by level* rather than only by name. *)
Section family.
  Context `{!typingC CON} {JUDG Σ}
    `{!alerusGpreS (cifOF CON) Σ, !invGS_gen HasNoLc Σ,
      !typingJ CON JUDG Σ}.
  (** The lifetime logic is *shared*: one [llft_logicGS] for the whole
    run, beside the heap, the prophecies and the unique borrows.  That is
    the thing this file used to get wrong on purpose. *)
  Context (hLlft : llft_logicGS Σ).
  Context (hGS : heapGS (cifOF CON) Σ) (hP : prophG Σ) (hU : uniqG Σ).
  Implicit Type (j k L : nat).

  (** The semantic half of a level, at given names *)
  Record LvlAt n : Type := MkLvlAt {
    lvl_Cs : Csem CON JUDG Σ;
    lvl_Js : Jsem JUDG (iProp Σ);
    lvl_CS :
      @typingCS CON JUDG Σ _ (alerusGS_of hLlft hGS hP hU n) _ lvl_Cs lvl_Js;
    lvl_JS :
      @typingJS CON JUDG Σ _ (alerusGS_of hLlft hGS hP hU n) _
        lvl_Cs lvl_Js lvl_CS;
  }.
  Arguments lvl_Cs {_} _. Arguments lvl_Js {_} _.
  Arguments lvl_CS {_} _. Arguments lvl_JS {_} _.

  (** One level's *whole* world satisfaction, [send_wsat] excluded: that
    one is literally the same proposition at every level (see the note at
    the top of this file), so it sits beside the family rather than in
    it. *)
  Definition lvl_wsat_core {n} (p : LvlAt n) : iProp Σ :=
    @alerus_wsat_core_at CON _ JUDG Σ (alerusGS_of hLlft hGS hP hU n) _
      (lvl_Cs p) (lvl_Js p) (lvl_CS p).

  (** Its two halves.  [lvl_wsat_shared] is held **once** for the whole
    run - there is one lifetime algebra, one kill order, one minted set
    and one outlives relation - and [lvl_wsat_lvl] once per level. *)
  Definition lvl_wsat_shared {n} (p : LvlAt n) : iProp Σ :=
    @alerus_wsat_shared_at CON _ JUDG Σ (alerusGS_of hLlft hGS hP hU n) _
      (lvl_Cs p) (lvl_Js p) (lvl_CS p).
  Definition lvl_wsat_lvl {n} (p : LvlAt n) : iProp Σ :=
    @alerus_wsat_lvl_at CON _ JUDG Σ (alerusGS_of hLlft hGS hP hU n) _
      (lvl_Cs p) (lvl_Js p) (lvl_CS p).

  Lemma lvl_wsat_core_split {n} (p : LvlAt n) :
    lvl_wsat_core p ⊣⊢ lvl_wsat_shared p ∗ lvl_wsat_lvl p.
  Proof. exact alerus_wsat_core_at_split. Qed.

  (** The shared half, pinned to the **bottom** level's package.

    It has to be pinned to one of them, because [llft_other_shared]
    holds the outlives guards and an [fguard] is taken over *a* level's
    [llft_wsatG] - see [typing/ctx.v]'s [alerus_Wix].  Pinning it to the
    bottom is what makes it usable by everyone: [∗_{k<j} Wbor_k]
    contains level 0's machinery for every [j ≥ 1], so a body at any
    execution level can open a guard stored there. *)
  Definition alerus_shared (P : ∀ k n, LvlAt n) (ns : list alerusNames)
    : iProp Σ :=
    match ns with [] => emp | n0 :: _ => lvl_wsat_shared (P 0 n0) end.

  (** The whole family: the shared half once, and one half per level.
    The list index *is* the execution level. *)
  Definition alerus_wsats (P : ∀ k n, LvlAt n) ns : iProp Σ :=
    alerus_shared P ns ∗ [∗ list] k ↦ n ∈ ns, lvl_wsat_lvl (P k n).

  (** [alerus_wsat_below P ns j]: the thesis's [∗_{k<j} Winv_k].

    [j = 0] leaves the shared half rather than [emp].  That is not a
    deviation but what the port needs: a function at execution level 0
    touches no borrow and no invariant, but it still has a lifetime
    context, and the lifetime tokens are in the shared half. *)
  Definition alerus_wsat_below (P : ∀ k n, LvlAt n) ns j : iProp Σ :=
    alerus_shared P ns ∗ [∗ list] k ↦ n ∈ take j ns, lvl_wsat_lvl (P k n).

  Lemma alerus_wsat_below_0 {P ns} :
    alerus_wsat_below P ns 0 ⊣⊢ alerus_shared P ns.
  Proof. by rewrite /alerus_wsat_below /= bi.sep_emp. Qed.

  (** A lower execution level's world satisfaction sits inside a higher
    one's - the thesis's [ty-lev], as a world-satisfaction inclusion.
    The shared half is on both sides and the difference is exactly the
    levels in between. *)
  Lemma alerus_wsat_below_le {P ns j j'} : (j ≤ j')%nat →
    alerus_wsat_below P ns j' ⊣⊢
      alerus_wsat_below P ns j ∗
        [∗ list] k ↦ n ∈ drop j (take j' ns),
          lvl_wsat_lvl (P (length (take j ns) + k) n).
  Proof.
    move=> Hle. rewrite /alerus_wsat_below.
    rewrite -{1}(take_drop j (take j' ns)) big_sepL_app take_take Nat.min_l //.
    by rewrite assoc.
  Qed.

  #[export] Instance wsat_incl_alerus_below {P ns j j'} (Hle : (j ≤ j')%nat) :
    WsatIncl (alerus_wsat_below P ns j') (alerus_wsat_below P ns j)
      ([∗ list] k ↦ n ∈ drop j (take j' ns),
         lvl_wsat_lvl (P (length (take j ns) + k) n)) :=
    alerus_wsat_below_le Hle.

  (** A full run of top level [length ns] is [alerus_wsat_below P ns
    (length ns)] *)
  Lemma alerus_wsat_below_full {P ns} :
    alerus_wsat_below P ns (length ns) ⊣⊢ alerus_wsats P ns.
  Proof. by rewrite /alerus_wsat_below /alerus_wsats take_ge. Qed.

  (** *** Allocating the family

    As many levels as asked for, out of one [Σ]: every per-level component
    is a ghost name beside a [_pre] class, so nothing is added to the
    global camera and there is no maximum level - the point
    [typing/levels.v] makes abstractly, now at the port's own state. *)
  Definition names_wsat n : iProp Σ :=
    ∀ (Cs : Csem CON JUDG Σ) (Js : Jsem JUDG (iProp Σ))
      (CS : @typingCS CON JUDG Σ _ (alerusGS_of hLlft hGS hP hU n) _ Cs Js),
      @alerus_wsat_core_at CON _ JUDG Σ (alerusGS_of hLlft hGS hP hU n) _
        Cs Js CS.

  Definition names_wsat_lvl n : iProp Σ :=
    ∀ (Cs : Csem CON JUDG Σ) (Js : Jsem JUDG (iProp Σ))
      (CS : @typingCS CON JUDG Σ _ (alerusGS_of hLlft hGS hP hU n) _ Cs Js),
      @alerus_wsat_lvl_at CON _ JUDG Σ (alerusGS_of hLlft hGS hP hU n) _
        Cs Js CS.

  Lemma names_wsat_lvl_of {n} (p : LvlAt n) :
    names_wsat_lvl n ⊢ lvl_wsat_lvl p.
  Proof. rewrite /names_wsat_lvl /lvl_wsat_lvl. iIntros "W". by iApply "W". Qed.

  (** The ∀ cannot be distributed over the ∗ - that is not a law - so the
    split happens *after* the interpretation is chosen, which is the only
    place it is needed. *)
  Lemma names_wsat_split {n} (p : LvlAt n) :
    names_wsat n ⊢ lvl_wsat_shared p ∗ lvl_wsat_lvl p.
  Proof.
    rewrite /names_wsat -lvl_wsat_core_split /lvl_wsat_core.
    iIntros "W". by iApply "W".
  Qed.
End family.

Arguments LvlAt {_ _ _ _ _ _ _} _ _ _ _ _.
Arguments MkLvlAt {_ _ _ _ _ _ _} _ _ _ _ _ _ _ _ _.
Arguments lvl_Cs {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments lvl_Js {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments lvl_CS {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments lvl_JS {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments lvl_wsat_core {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments lvl_wsat_shared {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments lvl_wsat_lvl {_ _ _ _ _ _ _ _ _ _ _ _} _.

(** ** Allocating the whole run

  The lifetime logic comes out *once*, and the levels against it: the
  bottom one with [alerus_names_alloc], which brings the shared half with
  it, and the rest with [alerus_names_alloc_more], which does not. *)
Section alloc_family.
  Context `{!typingC CON} {JUDG Σ}
    `{!alerusGpreS (cifOF CON) Σ, !invGS_gen HasNoLc Σ,
      !typingJ CON JUDG Σ}.
  Context (hGS : heapGS (cifOF CON) Σ) (hP : prophG Σ) (hU : uniqG Σ).

  (** [L] further levels against one lifetime logic.  The induction is
    on [L] alone, with [hLlft] and its witnesses fixed outside it -
    inducting with them inside would allocate a fresh lifetime logic at
    every step, which is the very thing being removed. *)
  Lemma alerus_names_more_list_alloc (hLlft : llft_logicGS Σ) L :
    llft_shared_wits -∗ |==> ∃ ns : list alerusNames, ⌜length ns = L⌝ ∗
      [∗ list] n ∈ ns, names_wsat_lvl hLlft hGS hP hU n.
  Proof.
    induction L as [|L IH].
    { iIntros "_ !>". iExists []. iSplitR; [done|]. by rewrite big_sepL_nil. }
    iIntros "#Wits".
    iMod (IH with "Wits") as (ns Hlen) "Wns".
    iMod (alerus_names_alloc_more hLlft with "Wits") as (n) "Wn".
    iModIntro. iExists (n :: ns). iSplitR; [iPureIntro; by rewrite /= Hlen|].
    rewrite big_sepL_cons. iSplitR "Wns"; [|iExact "Wns"].
    rewrite /names_wsat_lvl. iIntros (Cs Js CS). by iApply "Wn".
  Qed.

  Lemma alerus_names_list_alloc L :
    ⊢ |==> ∃ (hLlft : llft_logicGS Σ) (n0 : alerusNames)
      (ns : list alerusNames), ⌜length ns = L⌝ ∗
      names_wsat hLlft hGS hP hU n0 ∗
      [∗ list] n ∈ ns, names_wsat_lvl hLlft hGS hP hU n.
  Proof.
    iMod alerus_names_alloc as (hLlft n0) "[#Wits W0]".
    iMod (alerus_names_more_list_alloc hLlft L with "Wits")
      as (ns Hlen) "Wns".
    iModIntro. iExists hLlft, n0, ns. iSplitR; [done|]. iFrame "Wns".
    rewrite /names_wsat. iIntros (Cs Js CS). by iApply "W0".
  Qed.

  Lemma alerus_wsats_alloc L :
    ⊢ |==> ∃ (hLlft : llft_logicGS Σ) (ns : list alerusNames),
      ⌜length ns = S L⌝ ∗
      ∀ P : ∀ k n, LvlAt hLlft hGS hP hU n,
        alerus_wsats hLlft hGS hP hU P ns.
  Proof.
    iMod (alerus_names_list_alloc L) as (hLlft n0 ns Hlen) "[W0 Wns]".
    iModIntro. iExists hLlft, (n0 :: ns).
    iSplitR; [iPureIntro; by rewrite /= Hlen|]. iIntros (P).
    rewrite /alerus_wsats /alerus_shared big_sepL_cons.
    iDestruct (names_wsat_split hLlft hGS hP hU (P 0 n0) with "W0")
      as "[$ $]".
    iApply (big_sepL_impl with "Wns"). iIntros "!>" (k n _) "W".
    by iApply names_wsat_lvl_of.
  Qed.
End alloc_family.

(** ** [ty-lev] at the port's world satisfaction

  Raising a body's execution level is [twpw_incl_fupd] along
  [wsat_incl_alerus_below], exactly as [typing/levels.v]'s [twpw_lvs_le]
  is - and for the same reason, that a level is a ghost name and no camera
  is indexed by it.

  The program logic is a *parameter* here, not [alerus_lrustGS] at one of
  the levels, and that is deliberate.  [alerus_lrustGS] bundles the heap
  (shared) with [alerus_NaSem], whose [na_wsat] is [alerus_WGuard] and so
  is per level; a weakest precondition at level [i]'s [lrustGS_gen] is a
  different proposition from one at level [j]'s, and raising a level must
  change only the world satisfaction.  *Which* [lrustGS_gen] the typing
  judgment is stated at - and hence at which level the heap's read and
  write banks hand out their guards - is a question the next step has to
  answer, and the answer is forced: the level the judgment itself is at,
  since a guard handed out by a read has to be opened by the body that
  reads. *)
Section lv_wp.
  (** The [invGS_gen] is the program logic's own, not a second one: a [fupd]
    at another [invGS_gen] is a different proposition, and the world
    satisfactions here and the weakest precondition have to agree on it. *)
  Context `{!typingC CON} {JUDG Σ}
    `{!alerusGpreS (cifOF CON) Σ, !iris'GS_gen HasNoLc Λ Σ,
      !typingJ CON JUDG Σ}.
  Context {hLlft : llft_logicGS Σ}
    {hGS : heapGS (cifOF CON) Σ} {hP : prophG Σ} {hU : uniqG Σ}.
  Implicit Type j : nat.

  Lemma alerus_wsat_below_acsr {P ns j j'} (Hle : (j ≤ j')%nat) {E} :
    ⊢ □ (alerus_wsat_below hLlft hGS hP hU P ns j' ={E}=∗
         alerus_wsat_below hLlft hGS hP hU P ns j ∗
         (alerus_wsat_below hLlft hGS hP hU P ns j ={E}=∗
            alerus_wsat_below hLlft hGS hP hU P ns j')).
  Proof.
    iIntros "!>". rewrite (alerus_wsat_below_le hLlft hGS hP hU (P:=P) (ns:=ns) Hle).
    iIntros "[W Wr]". iModIntro. iFrame "W". iIntros "W !>". iFrame.
  Qed.

  Lemma twpw_alerus_le {P ns j j'} (Hle : (j ≤ j')%nat) {s E e Φ} :
    WP[alerus_wsat_below hLlft hGS hP hU P ns j] e @ s; E [{ Φ }] ⊢
    WP[alerus_wsat_below hLlft hGS hP hU P ns j'] e @ s; E [{ Φ }].
  Proof.
    iIntros "twp". iApply (twpw_incl_fupd (E:=E) with "[] twp"); [done|].
    iApply (alerus_wsat_below_acsr Hle).
  Qed.

  Lemma wpw_alerus_le {P ns j j'} (Hle : (j ≤ j')%nat) {s E e Φ} :
    WP[alerus_wsat_below hLlft hGS hP hU P ns j] e @ s; E {{ Φ }} ⊢
    WP[alerus_wsat_below hLlft hGS hP hU P ns j'] e @ s; E {{ Φ }}.
  Proof.
    iIntros "wp". iApply (wpw_incl_fupd (E:=E) with "[] wp"); [done|].
    iApply (alerus_wsat_below_acsr Hle).
  Qed.
End lv_wp.

(** ** [ty-lev] for the *judgment*

  [typed_body] at execution level [j] is [typed_body_at] over
  [∗_{k<j} Winv_k], and raising the level is [typed_body_at_wsat] over
  [alerus_wsat_below_le] - [twpw_incl_fupd] and nothing else, which is
  what PLAN.md item 2's step 5 asks for and what [typing/strat.v] proves
  abstractly.

  Note what is *not* needed: no induction on the level, no condition on
  the types in the context, and nothing about the interpretation.  The
  whole content of [≤-→] is that a body proved over a smaller world
  satisfaction holds over a bigger one, and the family of levels is
  built so that [below j] is literally a conjunct of [below j']. *)
Section lv_body.
  Context `{!typingC CON} {JUDG Σ}
    `{!alerusGpreS (cifOF CON) Σ, !typingJ CON JUDG Σ}.
  Context `{!typeG (cifOF CON) Σ}.
  Context {hLlft : llft_logicGS Σ} {hGS : heapGS (cifOF CON) Σ}
    {hP : prophG Σ} {hU : uniqG Σ}.

  (** The judgment at execution level [j]: its world satisfaction
    mentions only the levels below [j], which is the whole point - it is
    what lets [fn]'s interpretation be given without a cycle. *)
  Definition typed_body_lv {𝔄l 𝔅} (P : ∀ k n, LvlAt hLlft hGS hP hU n)
      (ns : list alerusNames) (j : nat) :=
    typed_body_at (𝔄l:=𝔄l) (𝔅:=𝔅)
      (alerus_wsat_below hLlft hGS hP hU P ns j ∗ send_wsat).

  Lemma typed_body_lv_le {𝔄l 𝔅} {P ns j j'} (Hle : (j ≤ j')%nat)
      E L I C T e tr :
    typed_body_lv (𝔄l:=𝔄l) (𝔅:=𝔅) P ns j E L I C T e tr ⊢
    typed_body_lv (𝔄l:=𝔄l) (𝔅:=𝔅) P ns j' E L I C T e tr.
  Proof.
    rewrite /typed_body_lv. iApply typed_body_at_wsat. iIntros "!> [W $]".
    rewrite (alerus_wsat_below_le hLlft hGS hP hU (P:=P) (ns:=ns) Hle).
    iDestruct "W" as "[W Wr]". iFrame "W". iIntros "!> [W $] !>". iFrame.
  Qed.
End lv_body.

(** [Eq_rect_eq] and nothing else, as the rest of the port. *)
Print Assumptions alerus_names_alloc.
Print Assumptions typed_body_lv_le.
Print Assumptions alerus_wsats_alloc.
Print Assumptions twpw_alerus_le.
