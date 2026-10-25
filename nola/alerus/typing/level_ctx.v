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

  **One thing this file gets wrong on purpose, because the right version
  is not expressible yet.**  [alerusNames] carries a whole
  [llft_logicGS], so each level here has its own *lifetime tokens* as
  well as its own borrows: [@[κ]] at level [k] is a different proposition
  from [@[κ]] at level [j], and nothing transfers between them.  That is
  the tower of lifetime logics PLAN.md calls prohibitive, and it is not
  the design.

  (As of the [lifetime_full.v] decoupling this is the only thing left:
  the borrow bookkeeping no longer shares the lifetime tokens' view of
  the world, so what is still wrong here is only that each level gets a
  whole [llft_logicGS] rather than its own borrow names.)

  What the design wants is [llft_name], [o_name] and [d_name] shared for
  the whole run and only [bor_name] - and with it the box and the
  shared-borrow family - varying with the level.  [lifetime/ra.v]'s split
  has made that *nameable*; it is not yet *buildable*, because
  [llft_wsat] at level [k] still needs [llft_inv_main], which is
  [outer_inv], which is [inner_inv], which is indexed by the dead set and
  so cannot simply be duplicated across levels.  Giving each level its
  own view of the dead set is the open piece of work; PLAN.md item 2 has
  its shape, and [lifetime/inv.v]'s [boxmap_alive_free] and its two
  siblings are the part of it that is already checked.

  So what is sound here is the *shape*: [L] packages out of one [Σ],
  [∗_{k<j} Winv_k], and [ty-lev].  Which ghost state each package may
  vary is the thing being fixed next. *)

From iris.algebra Require Import gmap_view agree auth gset.
From iris.proofmode Require Import proofmode.
From nola.alerus.lang Require Import adequacy proofmode notation.
From nola.alerus.typing Require Export model_inst.
From nola.alerus.typing Require Import type_context.
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
}.

Definition alerusΣ FML `{!oFunctorContractive FML} : gFunctors :=
  #[lrustΣ FML; llft_logicΣ; sinvΣ FML; prophΣ; uniqΣ; cnaΣ FML;
    fracGuardΣ FML; GFunctor (constRF (authUR (gsetUR lft)));
    fracKeyΣ llctx; fracKeyΣ (gmultiset lft)].

#[export] Instance subG_alerusGpreS {FML Σ} `{!oFunctorContractive FML} :
  subG (alerusΣ FML) Σ → alerusGpreS FML Σ.
Proof. solve_inG. Qed.

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
    an_llft : llft_logicGS Σ;
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
  Definition alerusGS_of (hGS : heapGS (cifOF CON) Σ)
      (hP : prophG Σ) (hU : uniqG Σ) (n : alerusNames)
    : alerusGS (cifOF CON) Σ :=
    AlerusGS (cifOF CON) Σ _ (an_llft n) (an_sinv n) hGS
      (NaInvGS (cifOF CON) Σ (@sinvGS_pre _ _ (an_sinv n)) _ (an_naInv n))
      _ hP hU (an_cna n) (an_frac n) _ (an_llctx n) (an_lfts n)
      (an_shr n) (an_eternal n) (an_store n).

  (** *** Allocating one level

    The names come out first and the interpretation goes in afterwards, for
    the reason the rest of this port records: [bor_sem] is [⟦⟧ᶜ(der)] and
    its [Csem] mentions the very ghost state being allocated. *)
  Lemma alerus_names_alloc :
    ⊢ |==> ∃ n : alerusNames, ∀ (hGS : heapGS (cifOF CON) Σ)
      (hP : prophG Σ) (hU : uniqG Σ) (Cs : Csem CON JUDG Σ)
      (Js : Jsem JUDG (iProp Σ))
      (CS : @typingCS CON JUDG Σ _ (alerusGS_of hGS hP hU n) _ Cs Js),
      @alerus_wsat_core_at CON _ JUDG Σ (alerusGS_of hGS hP hU n) _ Cs Js CS.
  Proof.
    iMod (frac_key_wsat_alloc (K:=llctx)) as (Hllctx) "Wllctx".
    iMod (frac_key_wsat_alloc (K:=gmultiset lft)) as (Hlfts) "Wlfts".
    iMod eternal_wsat_alloc as (γe) "We".
    iMod (frac_wsat_alloc (FML:=cifOF CON)) as (Hfrac) "Wfrac".
    iMod (llft_wsat_alloc (FML:=cifOF CON)) as (Hllft Hsinv shr) "Wllft".
    iMod (na_inv_wsat_alloc_name (FML:=cifOF CON)) as (γna) "Wna".
    iMod (cna_wsat_alloc (FML:=cifOF CON)) as (Hcna) "Wcna".
    iMod (sinv_wsat_alloc_name (FML:=cifOF CON) (sinvGS0 := Hsinv))
      as (γst) "Wstore".
    iModIntro.
    iExists (AlerusNames Hllft Hsinv γna Hcna Hfrac Hllctx Hlfts shr γe γst).
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
End level.

(** ** The family, and the thesis's [∗_{k<j} Winv_k]

  A level is a package: its ghost names, and the semantics of the formula
  language *at* them.  The semantics has to be part of it because
  [typingCS]/[typingJS] are stated about the ghost state - the point of
  [AlerusSem] being split off [alerusGS] ([typing/ctx.v]) is that one ghost
  state can carry several interpretations, and here several ghost states
  carry one interpretation.

  The semantics is taken *uniformly*, as [∀ n, LvlAt n], and that is not a
  simplification: [Csem] is built from the constructors and the
  constructors are built from the ghost state, so a level's interpretation
  is a function of its names and nothing else.  (Making it a function of
  the *level* as well is the next step - that is what [fn_fml]'s execution
  level is for.) *)
Section family.
  Context `{!typingC CON} {JUDG Σ}
    `{!alerusGpreS (cifOF CON) Σ, !invGS_gen HasNoLc Σ,
      !typingJ CON JUDG Σ}.
  Context (hGS : heapGS (cifOF CON) Σ) (hP : prophG Σ) (hU : uniqG Σ).
  Implicit Type (j k L : nat).

  (** The semantic half of a level, at given names *)
  Record LvlAt n : Type := MkLvlAt {
    lvl_Cs : Csem CON JUDG Σ;
    lvl_Js : Jsem JUDG (iProp Σ);
    lvl_CS :
      @typingCS CON JUDG Σ _ (alerusGS_of hGS hP hU n) _ lvl_Cs lvl_Js;
    lvl_JS :
      @typingJS CON JUDG Σ _ (alerusGS_of hGS hP hU n) _ lvl_Cs lvl_Js lvl_CS;
  }.
  Arguments lvl_Cs {_} _. Arguments lvl_Js {_} _.
  Arguments lvl_CS {_} _. Arguments lvl_JS {_} _.

  (** One level's world satisfaction, [send_wsat] excluded: that one is
    literally the same proposition at every level (see the note at the top
    of this file), so it sits beside the family rather than in it. *)
  Definition lvl_wsat_core {n} (p : LvlAt n) : iProp Σ :=
    @alerus_wsat_core_at CON _ JUDG Σ (alerusGS_of hGS hP hU n) _
      (lvl_Cs p) (lvl_Js p) (lvl_CS p).

  (** The whole family *)
  Definition alerus_wsats (P : ∀ n, LvlAt n) ns : iProp Σ :=
    [∗ list] n ∈ ns, lvl_wsat_core (P n).

  (** [alerus_wsat_below P ns j]: the thesis's [∗_{k<j} Winv_k], with
    [alerus_wsat_core] in place of [Winv].  This is PLAN.md item 2's
    step 1, at the port's own world satisfaction. *)
  Definition alerus_wsat_below (P : ∀ n, LvlAt n) ns j : iProp Σ :=
    alerus_wsats P (take j ns).

  Lemma alerus_wsat_below_0 {P ns} : alerus_wsat_below P ns 0 ⊣⊢ emp.
  Proof. by rewrite /alerus_wsat_below /alerus_wsats. Qed.

  Lemma alerus_wsats_split {P ns} j :
    alerus_wsats P ns ⊣⊢
      alerus_wsats P (take j ns) ∗ alerus_wsats P (drop j ns).
  Proof.
    by rewrite /alerus_wsats -{1}(take_drop j ns) big_sepL_app.
  Qed.

  (** A lower execution level's world satisfaction sits inside a higher
    one's - the thesis's [ty-lev], as a world-satisfaction inclusion. *)
  Lemma alerus_wsat_below_le {P ns j j'} : (j ≤ j')%nat →
    alerus_wsat_below P ns j' ⊣⊢
      alerus_wsat_below P ns j ∗ alerus_wsats P (drop j (take j' ns)).
  Proof.
    move=> Hle. rewrite /alerus_wsat_below (alerus_wsats_split (ns:=take j' ns) j).
    by rewrite take_take Nat.min_l.
  Qed.

  #[export] Instance wsat_incl_alerus_below {P ns j j'} (Hle : (j ≤ j')%nat) :
    WsatIncl (alerus_wsat_below P ns j') (alerus_wsat_below P ns j)
      (alerus_wsats P (drop j (take j' ns))) :=
    alerus_wsat_below_le Hle.

  (** *** Allocating the family

    As many levels as asked for, out of one [Σ]: every per-level component
    is a ghost name beside a [_pre] class, so nothing is added to the
    global camera and there is no maximum level - the point
    [typing/levels.v] makes abstractly, now at the port's own state. *)
  Definition names_wsat n : iProp Σ :=
    ∀ (Cs : Csem CON JUDG Σ) (Js : Jsem JUDG (iProp Σ))
      (CS : @typingCS CON JUDG Σ _ (alerusGS_of hGS hP hU n) _ Cs Js),
      @alerus_wsat_core_at CON _ JUDG Σ (alerusGS_of hGS hP hU n) _ Cs Js CS.

  Lemma names_wsat_lvl {n} (p : LvlAt n) :
    names_wsat n ⊢ lvl_wsat_core p.
  Proof. rewrite /names_wsat /lvl_wsat_core. iIntros "W". by iApply "W". Qed.

  Lemma alerus_names_list_alloc L :
    ⊢ |==> ∃ ns, ⌜length ns = L⌝ ∗ [∗ list] n ∈ ns, names_wsat n.
  Proof.
    induction L as [|L IH].
    { iModIntro. iExists []. iSplitR; [done|]. by rewrite big_sepL_nil. }
    iMod IH as (ns Hlen) "W". iMod alerus_names_alloc as (n) "Wn".
    iModIntro. iExists (n :: ns). iSplitR; [iPureIntro; by rewrite /= Hlen|].
    rewrite big_sepL_cons. iSplitR "W"; [|iExact "W"].
    rewrite /names_wsat. iIntros (Cs Js CS). by iApply "Wn".
  Qed.

  (** The family's world satisfaction, with the semantics handed in last.
    The order is the one this port has had to learn everywhere: the ghost
    *names* come out first, because the interpretation mentions them. *)
  Lemma alerus_wsats_alloc L :
    ⊢ |==> ∃ ns, ⌜length ns = L⌝ ∗
      ∀ P : ∀ n, LvlAt n, alerus_wsats P ns.
  Proof.
    iMod (alerus_names_list_alloc L) as (ns Hlen) "W". iModIntro.
    iExists ns. iSplitR; [done|]. iIntros (P). rewrite /alerus_wsats.
    iApply (big_sepL_impl with "W"). iIntros "!>" (k n _) "W".
    by iApply names_wsat_lvl.
  Qed.

  (** A full run of top level [L] is [alerus_wsat_below P ns L] *)
  Lemma alerus_wsat_below_full {P ns} :
    alerus_wsat_below P ns (length ns) ⊣⊢ alerus_wsats P ns.
  Proof. by rewrite /alerus_wsat_below take_ge. Qed.
End family.

Arguments LvlAt {_ _ _ _ _ _ _} _ _ _ _.
Arguments MkLvlAt {_ _ _ _ _ _ _} _ _ _ _ _ _ _ _.
Arguments lvl_Cs {_ _ _ _ _ _ _ _ _ _ _} _.
Arguments lvl_Js {_ _ _ _ _ _ _ _ _ _ _} _.
Arguments lvl_CS {_ _ _ _ _ _ _ _ _ _ _} _.
Arguments lvl_JS {_ _ _ _ _ _ _ _ _ _ _} _.
Arguments lvl_wsat_core {_ _ _ _ _ _ _ _ _ _ _} _.

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
  Context {hGS : heapGS (cifOF CON) Σ} {hP : prophG Σ} {hU : uniqG Σ}.
  Implicit Type j : nat.

  Lemma alerus_wsat_below_acsr {P ns j j'} (Hle : (j ≤ j')%nat) {E} :
    ⊢ □ (alerus_wsat_below hGS hP hU P ns j' ={E}=∗
         alerus_wsat_below hGS hP hU P ns j ∗
         (alerus_wsat_below hGS hP hU P ns j ={E}=∗
            alerus_wsat_below hGS hP hU P ns j')).
  Proof.
    iIntros "!>". rewrite (alerus_wsat_below_le hGS hP hU (P:=P) (ns:=ns) Hle).
    iIntros "[W Wr]". iModIntro. iFrame "W". iIntros "W !>". iFrame.
  Qed.

  Lemma twpw_alerus_le {P ns j j'} (Hle : (j ≤ j')%nat) {s E e Φ} :
    WP[alerus_wsat_below hGS hP hU P ns j] e @ s; E [{ Φ }] ⊢
    WP[alerus_wsat_below hGS hP hU P ns j'] e @ s; E [{ Φ }].
  Proof.
    iIntros "twp". iApply (twpw_incl_fupd (E:=E) with "[] twp"); [done|].
    iApply (alerus_wsat_below_acsr Hle).
  Qed.

  Lemma wpw_alerus_le {P ns j j'} (Hle : (j ≤ j')%nat) {s E e Φ} :
    WP[alerus_wsat_below hGS hP hU P ns j] e @ s; E {{ Φ }} ⊢
    WP[alerus_wsat_below hGS hP hU P ns j'] e @ s; E {{ Φ }}.
  Proof.
    iIntros "wp". iApply (wpw_incl_fupd (E:=E) with "[] wp"); [done|].
    iApply (alerus_wsat_below_acsr Hle).
  Qed.
End lv_wp.

(** [Eq_rect_eq] and nothing else, as the rest of the port. *)
Print Assumptions alerus_names_alloc.
Print Assumptions alerus_wsats_alloc.
Print Assumptions twpw_alerus_le.
