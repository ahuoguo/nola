(** * The formula language, concretely: a [cif]

  Everything above this file is parametric in [FML] and in what a formula
  means.  This file gives one concrete choice: [FML := cifOF CON] for a
  constructor signature [CON] containing the constructors below, with
  [bor_sem := ⟦⟧ᶜ(der)].

  The shape follows [nola/examples/rust_halt/base.v] and
  [nola/iris/inv_deriv.v].  Constructors come in three kinds:

  - *leaves*, whose meaning is a token - ghost ownership that mentions no
    interpretation at all.  Most of the language is of this kind.
  - *structural* ones - separating conjunction, disjunction, existential,
    pure - which [nola/iris/cif.v] already provides.
  - *judgments*, whose meaning quantifies the world satisfaction and so
    cannot be given by recursion on the formula.  Those are [guard_fml] and
    [idxbor_fml]; see [AltSem] in [typing/ctx.v] and the thesis, § 6.4. *)

From iris.algebra Require Import excl.
From nola.util Require Import tagged.
From nola.bi Require Import deriv.
From nola.iris Require Export cif.
From nola.alerus.typing Require Export ctx.
From nola.alerus Require Import na_inv_fork.
From nola.alerus.util Require Import cancellable_na_invariants
  atomic_lock_counter.
Import iPropAppNotation ModwNotation CsemNotation GuardNotation
  DsemNotation.

Implicit Type (Σ : gFunctors) (CON : cifcon).

(** ** Leaf constructors

  The selector carries all the data; there are no sub-formulas, so both
  domains are empty and the data [oFunctor] is [unitO]. *)
Variant alerusCT_id := .
Variant alerusCT_sel : Type :=
| (** Lifetime token *) as_alive (κ : lft)
| (** Dead lifetime *) as_dead (κ : lft)
| (** Cell-indexed points-to *)
    as_cells (l : loc) (cs : list (list cell_id)) (fv : list fancy_val)
| (** Complete points-to *) as_ccells (l : cloc) (fv : list fancy_val)
| (** Allocatedness *) as_cmapstoany (l : cloc)
| (** Deallocation permission *) as_freeable (n sz : nat) (l : loc)
| (** Value observer *)
    as_vo (ξ : proph_var) (x : ~~ (`ξ.(pv_ty))) (d : nat * nat)
| (** Prophecy controller *)
    as_pc (ξ : proph_var) (x : ~~ (`ξ.(pv_ty))) (xp : proph ξ.(pv_ty))
      (d : nat * nat)
| (** Guard source *) as_gsrc (s : gsrc)
| (** Borrow-state ownership *)
    as_bor_state (sn : ra.slice_name) (bs : ra.BorState)
| (** A heap cell's contents *)
    as_heap (lc : loc + cell_id) (cells : list cell_id) (cv : cell_id + val)
| (** Points-to over a vector of cells *)
    as_cellsvec (cs : list cell_id) (fv : list fancy_val)
| (** An atomic invariant's "not yet opened" token *) as_active (γ : gname)
| (** A cancellable non-atomic invariant's version of it *)
    as_cna_active (γ : gname)
| (** A prophecy observation *) as_obs (φ : proph_asn → Prop)
| (** The atomic lock counter's handle *) as_handle (c : coPset)
| (** A dead lifetime atom, for the shared-borrow formula *)
    as_dead_atom (k : ra.lt_atom)
| (** The cancellation token of a shared borrow *) as_ccancel (γ : gname).

Definition alerusCT : cifcon :=
  Cifcon alerusCT_id alerusCT_sel (λ _, Empty_set) (λ _, Empty_set)
    (λ _, unitO) _.

Notation alerusC := (inC alerusCT).

Section alerusC.
  Context `{!alerusC CON} {Σ}.
  (** Each leaf as a formula *)
  Definition cif_alive κ : cif CON Σ :=
    cif_in alerusCT (as_alive κ) nullary nullary ().
  Definition cif_dead κ : cif CON Σ :=
    cif_in alerusCT (as_dead κ) nullary nullary ().
  Definition cif_cells l cs fv : cif CON Σ :=
    cif_in alerusCT (as_cells l cs fv) nullary nullary ().
  Definition cif_ccells l fv : cif CON Σ :=
    cif_in alerusCT (as_ccells l fv) nullary nullary ().
  Definition cif_cmapstoany l : cif CON Σ :=
    cif_in alerusCT (as_cmapstoany l) nullary nullary ().
  Definition cif_freeable n sz l : cif CON Σ :=
    cif_in alerusCT (as_freeable n sz l) nullary nullary ().
  Definition cif_vo ξ x d : cif CON Σ :=
    cif_in alerusCT (as_vo ξ x d) nullary nullary ().
  Definition cif_pc ξ x xp d : cif CON Σ :=
    cif_in alerusCT (as_pc ξ x xp d) nullary nullary ().
  Definition cif_gsrc s : cif CON Σ :=
    cif_in alerusCT (as_gsrc s) nullary nullary ().
  Definition cif_bor_state sn bs : cif CON Σ :=
    cif_in alerusCT (as_bor_state sn bs) nullary nullary ().
  Definition cif_heap lc cells cv : cif CON Σ :=
    cif_in alerusCT (as_heap lc cells cv) nullary nullary ().
  Definition cif_cellsvec cs fv : cif CON Σ :=
    cif_in alerusCT (as_cellsvec cs fv) nullary nullary ().
  Definition cif_active γ : cif CON Σ :=
    cif_in alerusCT (as_active γ) nullary nullary ().
  Definition cif_cna_active γ : cif CON Σ :=
    cif_in alerusCT (as_cna_active γ) nullary nullary ().
  Definition cif_obs φ : cif CON Σ :=
    cif_in alerusCT (as_obs φ) nullary nullary ().
  Definition cif_handle c : cif CON Σ :=
    cif_in alerusCT (as_handle c) nullary nullary ().
  Definition cif_dead_atom k : cif CON Σ :=
    cif_in alerusCT (as_dead_atom k) nullary nullary ().
  Definition cif_ccancel γ : cif CON Σ :=
    cif_in alerusCT (as_ccancel γ) nullary nullary ().

  (** The shared-borrow formula is not a constructor of its own: it is
    built out of the structural connectives and the two leaves above. *)
  Definition cif_shr (κ : gset ra.lt_atom) (γc : gname) (Px : cif CON Σ)
    : cif CON Σ :=
    (Px ∨ ((∃ k, ⌜k ∈ κ⌝ ∗ cif_dead_atom k) ∗ cif_ccancel γc))%cif.

  Context `{!alerusGS (cifOF CON) Σ}.
  (** The heap assertions do not mention the interpretation - they are
    [points_to_seq] tokens - but their [FML] parameter is not determined by
    their arguments, so it is pinned here. *)
  Local Notation FMLC := (cifOF CON).
  (** Semantics of the leaves.  Every one of them is a *token*: ghost
    ownership that mentions no interpretation, which is what makes them
    ordinary constructors rather than judgments. *)
  Definition alerusCT_sem (s : alerusCT_sel) : iProp Σ :=
    match s with
    | as_alive κ => @[κ]
    | as_dead κ => [†κ]
    | as_cells l cs fv => heap_mapsto_cells_fancy_vec (FML:=FMLC) l cs fv
    | as_ccells l fv => heap_complete_mapsto_fancy_vec (FML:=FMLC) l fv
    | as_cmapstoany l => heap_complete_mapsto_vec (FML:=FMLC) l
    | as_freeable n sz l => freeable_sz (FML:=FMLC) n sz l
    | as_vo ξ x d => .VO[ξ] x d
    | as_pc ξ x xp d => .PC[ξ] x xp d
    | as_gsrc s => gsrc_interp (FML:=FMLC) s
    | as_bor_state sn bs => ra.OwnBorState llft_name sn bs
    | as_heap lc cells cv =>
        points_to_seq (FML:=FMLC) heap_name lc cells cv
    | as_cellsvec cs fv => cells_points_to_fancy_value_vec (FML:=FMLC) cs fv
    | as_active γ => own γ (Excl ())
    | as_cna_active γ => cna_active (FML:=FMLC) γ
    | as_obs φ => ⟨π, φ π⟩
    | as_handle c => atomic_lock_handle atomic_lock_ctr_name c
    | as_dead_atom k => ra.Dead llft_name k
    | as_ccancel γ => ra.CCancel γ
    end%I.
  #[export] Program Instance alerusCT_ecsem {JUDG}
    : Ecsem alerusCT CON JUDG Σ :=
    ECSEM (λ _ _ s _ _ _, alerusCT_sem s) _.
  Next Obligation. done. Qed.
End alerusC.

(** [alerusC] semantics registered *)
Notation alerusCS := (inCS alerusCT).

(** ** Constructors holding a *syntactic* sub-formula

  An invariant token stores a formula and hands it back unchanged; its
  meaning does not interpret it.  So the sub-formula lives in [cifc_cdom] -
  the coinductive domain - exactly as [cif_inv] in [nola/iris/inv_deriv.v].
  That is also what makes these constructors productive, so a type former
  may nest them. *)
Variant naInvCT_id := .
Variant naInvCT_sel : Type :=
| (** An atomic invariant *) nis_na_inv (N : namespace)
| (** ... opened *) nis_na_otok (N : namespace)
| (** A cancellable non-atomic invariant *)
    nis_cna_inv (γ : gname) (p : cna_pool_name) (N : namespace)
| (** ... opened *)
    nis_cna_otok (γ : gname) (p : cna_pool_name) (N : namespace) (κ : lft).

Definition naInvCT : cifcon :=
  Cifcon naInvCT_id naInvCT_sel (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.

Notation naInvC := (inC naInvCT).

Section naInvC.
  Context `{!naInvC CON} {Σ}.
  Definition cif_na_inv N (Px : cif CON Σ) : cif CON Σ :=
    cif_in naInvCT (nis_na_inv N) nullary (unary Px) ().
  Definition cif_na_otok N (Px : cif CON Σ) : cif CON Σ :=
    cif_in naInvCT (nis_na_otok N) nullary (unary Px) ().
  Definition cif_cna_inv γ p N (Px : cif CON Σ) : cif CON Σ :=
    cif_in naInvCT (nis_cna_inv γ p N) nullary (unary Px) ().
  Definition cif_cna_otok γ p N κ (Px : cif CON Σ) : cif CON Σ :=
    cif_in naInvCT (nis_cna_otok γ p N κ) nullary (unary Px) ().

  (** All four are productive, so they may be nested *)
  #[export] Instance cif_na_inv_productive {N} : Productive (cif_na_inv N).
  Proof.
    move=> ????. apply cif_in_preserv_productive=>//. by apply fun_proeqv_later.
  Qed.
  #[export] Instance cif_cna_inv_productive {γ p N} :
    Productive (cif_cna_inv γ p N).
  Proof.
    move=> ????. apply cif_in_preserv_productive=>//. by apply fun_proeqv_later.
  Qed.

  Context `{!alerusGS (cifOF CON) Σ}.
  Local Notation FMLC := (cifOF CON).
  Definition naInvCT_sem (s : naInvCT_sel) (Ψx : unit -d> cif CON Σ)
    : iProp Σ :=
    match s with
    | nis_na_inv N => na_inv_tok (FML:=FMLC) atomic_threadpool N (Ψx ())
    | nis_na_otok N => na_otok (FML:=FMLC) atomic_threadpool N (Ψx ())
    | nis_cna_inv γ p N => cna_inv (FML:=FMLC) γ p N (Ψx ())
    | nis_cna_otok γ p N κ => cna_otok (FML:=FMLC) γ p N κ (Ψx ())
    end.
  #[export] Instance naInvCT_sem_ne {s n} :
    Proper ((≡{n}≡) ==> (≡{n}≡)) (naInvCT_sem s).
  Proof. move=> ?? eq. case s=>/=*; f_equiv; apply eq. Qed.
  #[export] Program Instance naInvCT_ecsem {JUDG}
    : Ecsem naInvCT CON JUDG Σ :=
    ECSEM (λ _ _ s _ Ψx _, naInvCT_sem s Ψx) _.
  Next Obligation. solve_proper. Qed.
End naInvC.

Notation naInvCS := (inCS naInvCT).



(** ** The interpretation at a derivability candidate

  [bor_sem] is [⟦⟧ᶜ(δ)].  Everything the lifetime logic and the typing layer
  need of an interpretation - [BorSem], [BorStateFml], [ShrBorSem],
  [EmptySem], i.e. [AlerusSem] - can therefore be assembled from a [δ],
  which is exactly what the two judgments below need in order to speak about
  the guarding world satisfaction at a candidate.  This is Nola's
  [inv_wsat ⟦⟧(δ)] ([nola/iris/inv_deriv.v]) one level up. *)
Section sem_at.
  Context `{!alerusC CON, !naInvC CON} {JUDG Σ}
    `{!alerusGS (cifOF CON) Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
      !alerusCS CON JUDG Σ, !naInvCS CON JUDG Σ}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** The semantics of the separating conjunction *)
  Lemma cif_sem_sep {δ} {Px Qx : cif CON Σ} :
    ⟦ Px ∗ Qx ⟧ᶜ(δ) ⊣⊢ ⟦ Px ⟧ᶜ(δ) ∗ ⟦ Qx ⟧ᶜ(δ).
  Proof. done. Qed.

  (** [BorSem] at a candidate *)
  #[export] Instance cif_sem_ne' {δ} :
    NonExpansive (λ Px : cifOF CON $oi Σ, ⟦ Px ⟧ᶜ(δ)) := cif_sem_ne.
  Definition BorSem_at δ : BorSem (cifOF CON) Σ :=
    {| bor_sem := (λ Px : cifOF CON $oi Σ, ⟦ Px ⟧ᶜ(δ)); bor_sem_ne := _;
       bor_sem_inhabited := populate (cif_pure True);
       bor_sep := cif_sep; bor_sep_sem := λ _ _, cif_sem_sep |}.

  (** The semantics of the custom constructors, computed *)
  Lemma cif_bor_state_sem {δ sn bs} :
    ⟦ cif_bor_state sn bs ⟧ᶜ(δ) ⊣⊢ ra.OwnBorState llft_name sn bs.
  Proof. by rewrite /cif_bor_state sem_cif_in. Qed.
  Lemma cif_dead_atom_sem {δ k} :
    ⟦ cif_dead_atom k ⟧ᶜ(δ) ⊣⊢ ra.Dead llft_name k.
  Proof. by rewrite /cif_dead_atom sem_cif_in. Qed.
  Lemma cif_ccancel_sem {δ γ} : ⟦ cif_ccancel γ ⟧ᶜ(δ) ⊣⊢ ra.CCancel γ.
  Proof. by rewrite /cif_ccancel sem_cif_in. Qed.
  Lemma cif_shr_sem {δ} {κ : gset ra.lt_atom} {γc} {Px : cif CON Σ} :
    ⟦ cif_shr κ γc Px ⟧ᶜ(δ) ⊣⊢
      ⟦ Px ⟧ᶜ(δ) ∨ ((∃ k, ⌜k ∈ κ⌝ ∗ ra.Dead llft_name k) ∗ ra.CCancel γc).
  Proof.
    rewrite /cif_shr /=. setoid_rewrite cif_dead_atom_sem.
    by rewrite cif_ccancel_sem.
  Qed.

  (** The borrow-state constructor means borrow-state ownership *)
  Program Definition BorStateFml_at δ
    : @BorStateFml Σ _ (cifOF CON) (BorSem_at δ) llft_name :=
    {| bor_state_fml := (λ sn bs, cif_bor_state sn bs : cifOF CON $oi Σ) |}.
  Next Obligation. move=> *. exact cif_bor_state_sem. Qed.

  (** The shared-borrow constructor *)
  Program Definition ShrBorSem_at δ
    : @ShrBorSem (cifOF CON) Σ _ (BorSem_at δ) :=
    {| shr_fml := (λ κ γc Px, cif_shr κ γc Px : cifOF CON $oi Σ) |}.
  Next Obligation. move=> *. exact cif_shr_sem. Qed.

  (** [True] as a formula *)
  Lemma cif_pure_True_sem {δ} :
    ⟦ cif_pure True : cif CON Σ ⟧ᶜ(δ) ⊣⊢ (True : iProp Σ).
  Proof. done. Qed.
  Program Definition EmptySem_at δ : @EmptySem (cifOF CON) Σ (BorSem_at δ) :=
    {| empty_fml := (cif_pure True : cifOF CON $oi Σ) |}.
  Next Obligation. move=> ?. exact cif_pure_True_sem. Qed.

  (** Hence everything the development needs of an interpretation *)
  Definition AlerusSem_at δ : AlerusSem (cifOF CON) Σ :=
    {| alerus_borSem := BorSem_at δ;
       alerus_borStateFml := BorStateFml_at δ;
       alerus_shrBorSem := ShrBorSem_at δ;
       alerus_emptySem := EmptySem_at δ |}.

  (** And in particular the guarding world satisfaction at a candidate,
    which is what the two judgments below quantify over.  This is the whole
    point of separating [AlerusSem] from [alerusGS]. *)
  Definition alerus_WGuard_at δ : iProp Σ :=
    @alerus_WGuard (cifOF CON) Σ _ (AlerusSem_at δ).
End sem_at.

(** ** The two judgments

  A guard [Px &&{W}&&> Qx] and an indexed borrow [&{κ,idx} Px] both quantify
  the world satisfaction, so neither can be given by recursion on the
  formula; both are judgments, interpreted at a derivability candidate.
  This is [inv_jacsr] in [nola/iris/inv_deriv.v], and the thesis's § 6.4,
  where Nola's own borrow connectives are built the same way. *)

(** [guardJT]: a guard, as a judgment *)
Variant guardJT_id := .
Definition guardJT (FM : ofe) : ofe := tagged guardJT_id (FM * FM).
Notation guardJ FM := (inJ (guardJT FM)).

(** [idxborJT]: an indexed borrow, as a judgment *)
Variant idxborJT_id := .
Definition idxborJT (FM : ofe) : ofe :=
  tagged idxborJT_id (leibnizO lft * leibnizO Idx * FM).
Notation idxborJ FM := (inJ (idxborJT FM)).

Section judg.
  Context `{!alerusC CON, !naInvC CON} {JUDG Σ}
    `{!alerusGS (cifOF CON) Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
      !alerusCS CON JUDG Σ, !naInvCS CON JUDG Σ}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** Semantics of the guard judgment: the guard at the candidate's own
    guarding world satisfaction *)
  Definition guardJT_sem δ (J : guardJT (cifO CON Σ)) : iProp Σ :=
    ⟦ J.(untag).1 ⟧ᶜ(δ) &&{alerus_WGuard_at δ}&&> ⟦ J.(untag).2 ⟧ᶜ(δ).
  #[export] Instance guardJT_sem_ne {δ} : NonExpansive (guardJT_sem δ).
  Proof. move=> ?[[??]][[??]][/=??]. solve_proper. Qed.
  #[export] Instance guardJT_dsem
    : Dsem JUDG (guardJT (cifO CON Σ)) (iProp Σ) := DSEM guardJT_sem _.

End judg.

(** Semantics of the indexed-borrow judgment.  [idx_bor] needs the whole of
  [AlerusSem] - a borrow is indexed by a lifetime, and the lifetime logic's
  parameters come with it - so the candidate's interpretation is installed
  as the ambient one for the length of this section. *)
Section idxbor_judg.
  Context `{!alerusC CON, !naInvC CON} {JUDG Σ}
    `{!alerusGS (cifOF CON) Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
      !alerusCS CON JUDG Σ, !naInvCS CON JUDG Σ}.
  Context (δ : JUDG -n> iProp Σ).
  Local Instance AlerusSem_δ : AlerusSem (cifOF CON) Σ := AlerusSem_at δ.

  Definition idxborJT_sem_at (J : idxborJT (cifO CON Σ)) : iProp Σ :=
    idx_bor (FML:=cifOF CON) J.(untag).1.1 J.(untag).1.2 J.(untag).2.
  #[export] Instance idxborJT_sem_at_ne : NonExpansive idxborJT_sem_at.
  Proof. move=> ?[[[??]?]][[[??]?]][[/=/leibniz_equiv_iff<-?]?]. solve_proper. Qed.
End idxbor_judg.

Section judg2.
  Context `{!alerusC CON, !naInvC CON} {JUDG Σ}
    `{!alerusGS (cifOF CON) Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
      !alerusCS CON JUDG Σ, !naInvCS CON JUDG Σ}.
  #[export] Instance idxborJT_dsem
    : Dsem JUDG (idxborJT (cifO CON Σ)) (iProp Σ) :=
    DSEM idxborJT_sem_at _.
End judg2.

(** Semantics of the two judgment types registered *)
Notation guardJS CON JUDG Σ := (inJS (guardJT (cifO CON Σ)) JUDG (iProp Σ)).
Notation idxborJS CON JUDG Σ := (inJS (idxborJT (cifO CON Σ)) JUDG (iProp Σ)).

(** ** The judgment constructors

  [guard_fml] and [idxbor_fml] as formulas: each holds its sub-formulas
  *syntactically* and means "the judgment is derivable at [δ]", under a [□]
  so that the formula is persistent.  This is [inv'] in
  [nola/iris/inv_deriv.v]. *)
Variant guardCT_id := .
Definition guardCT : cifcon :=
  Cifcon guardCT_id unit (λ _, Empty_set) (λ _, bool) (λ _, unitO) _.
Notation guardC := (inC guardCT).

Variant idxborCT_id := .
Definition idxborCT : cifcon :=
  Cifcon idxborCT_id (lft * Idx)%type (λ _, Empty_set) (λ _, unit)
    (λ _, unitO) _.
Notation idxborC := (inC idxborCT).

Section judgC.
  Context `{!guardC CON, !idxborC CON} {Σ}.
  Definition cif_guard (Px Qx : cif CON Σ) : cif CON Σ :=
    cif_in guardCT () nullary (binary Px Qx) ().
  Definition cif_idxbor κ idx (Px : cif CON Σ) : cif CON Σ :=
    cif_in idxborCT (κ, idx) nullary (unary Px) ().

  (** Both are productive, so a type former may nest them *)
  #[export] Instance cif_idxbor_productive {κ idx} :
    Productive (cif_idxbor κ idx).
  Proof.
    move=> ????. apply cif_in_preserv_productive=>//. by apply fun_proeqv_later.
  Qed.

  Context {JUDG} `{guard_j0 : !guardJ (cifO CON Σ) JUDG,
    idxbor_j0 : !idxborJ (cifO CON Σ) JUDG}.
  (** The judgments as elements of [JUDG] *)
  Definition guard_j (Px Qx : cif CON Σ) : JUDG :=
    guard_j0 (Tagged (Px, Qx)).
  Definition idxbor_j κ idx (Px : cif CON Σ) : JUDG :=
    idxbor_j0 (Tagged (κ, idx, Px)).
  #[export] Instance guard_j_ne : NonExpansive2 guard_j.
  Proof. unfold guard_j=> ???????. f_equiv. by split. Qed.
  #[export] Instance idxbor_j_ne {κ idx} : NonExpansive (idxbor_j κ idx).
  Proof. unfold idxbor_j=> ????. f_equiv. by split; [split|]. Qed.

  #[export] Program Instance guardCT_ecsem : Ecsem guardCT CON JUDG Σ :=
    ECSEM (λ _ δ _ _ Ψx _, □ δ (guard_j (Ψx true) (Ψx false)))%I _.
  Next Obligation. solve_proper. Qed.
  #[export] Program Instance idxborCT_ecsem : Ecsem idxborCT CON JUDG Σ :=
    ECSEM (λ _ δ s _ Ψx _, □ δ (idxbor_j s.1 s.2 (Ψx ())))%I _.
  Next Obligation. solve_proper. Qed.
End judgC.

Notation guardCS := (inCS guardCT).
Notation idxborCS := (inCS idxborCT).

(** ** Constructor and judgment constraints

  As in [rust_halt/base.v], the development is parametric in a constructor
  signature [CON] and a judgment type [JUDG] that *contain* the ones above;
  these classes say so. *)
Class typingC CON : Type := TYPING_C {
  typingC_alerus :: alerusC CON;
  typingC_naInv :: naInvC CON;
  typingC_guard :: guardC CON;
  typingC_idxbor :: idxborC CON;
}.
Class typingJ CON JUDG Σ : Type := TYPING_J {
  typingJ_guard :: guardJ (cifO CON Σ) JUDG;
  typingJ_idxbor :: idxborJ (cifO CON Σ) JUDG;
}.
Class typingCS CON JUDG Σ `{!typingC CON, !alerusGS (cifOF CON) Σ}
  `{!typingJ CON JUDG Σ, !Csem CON JUDG Σ} : Prop := TYPING_CS {
  typingCS_alerus :: alerusCS CON JUDG Σ;
  typingCS_naInv :: naInvCS CON JUDG Σ;
  typingCS_guard :: guardCS CON JUDG Σ;
  typingCS_idxbor :: idxborCS CON JUDG Σ;
}.
Class typingJS CON JUDG Σ `{!typingC CON, !alerusGS (cifOF CON) Σ}
  `{!typingJ CON JUDG Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
    !typingCS CON JUDG Σ} : Prop := TYPING_JS {
  typingJS_guard :: guardJS CON JUDG Σ;
  typingJS_idxbor :: idxborJS CON JUDG Σ;
}.

(** ** The ambient interpretation and the [TypeFml] instance

  The ambient interpretation is [⟦⟧ᶜ(der)]: [der] is Nola's best derivability
  predicate ([nola/bi/deriv.v], thesis Definition 4.1), whose soundness
  [der_sound] gives [der J ⊢ ⟦J⟧(der)] - the elimination of a judgment - and
  whose introduction is [Deriv_factor'], which asks for the judgment's
  semantics at *every* good candidate. *)
Section model.
  Context `{!typingC CON} {JUDG Σ} `{!alerusGS (cifOF CON) Σ,
    !typingJ CON JUDG Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
    !typingCS CON JUDG Σ, !typingJS CON JUDG Σ}.

  (** The ambient interpretation *)
  #[export] Instance alerusSem_der : AlerusSem (cifOF CON) Σ :=
    AlerusSem_at der.

  (** Unfolding the leaves at the ambient interpretation *)
  Lemma cif_alive_sem {κ} : bor_sem (cif_alive κ : cifOF CON $oi Σ) ⊣⊢ @[κ].
  Proof. by rewrite /bor_sem /= /cif_alive sem_cif_in. Qed.
  Lemma cif_dead_sem {κ} : bor_sem (cif_dead κ : cifOF CON $oi Σ) ⊣⊢ [†κ].
  Proof. by rewrite /bor_sem /= /cif_dead sem_cif_in. Qed.
  Lemma cif_cells_sem {l cs fv} :
    bor_sem (cif_cells l cs fv : cifOF CON $oi Σ) ⊣⊢ l ↦[^ cs ]!∗ fv.
  Proof. by rewrite /bor_sem /= /cif_cells sem_cif_in. Qed.
  Lemma cif_ccells_sem {l fv} :
    bor_sem (cif_ccells l fv : cifOF CON $oi Σ) ⊣⊢ l #↦!∗ fv.
  Proof. by rewrite /bor_sem /= /cif_ccells sem_cif_in. Qed.
  Lemma cif_cmapstoany_sem {l} :
    bor_sem (cif_cmapstoany l : cifOF CON $oi Σ) ⊣⊢ l #↦∗_.
  Proof. by rewrite /bor_sem /= /cif_cmapstoany sem_cif_in. Qed.
  Lemma cif_freeable_sem {n sz l} :
    bor_sem (cif_freeable n sz l : cifOF CON $oi Σ) ⊣⊢ freeable_sz n sz l.
  Proof. by rewrite /bor_sem /= /cif_freeable sem_cif_in. Qed.
  Lemma cif_vo_sem {ξ x d} :
    bor_sem (cif_vo ξ x d : cifOF CON $oi Σ) ⊣⊢ .VO[ξ] x d.
  Proof. by rewrite /bor_sem /= /cif_vo sem_cif_in. Qed.
  Lemma cif_pc_sem {ξ x xp d} :
    bor_sem (cif_pc ξ x xp d : cifOF CON $oi Σ) ⊣⊢ .PC[ξ] x xp d.
  Proof. by rewrite /bor_sem /= /cif_pc sem_cif_in. Qed.
  Lemma cif_gsrc_sem {s} :
    bor_sem (cif_gsrc s : cifOF CON $oi Σ) ⊣⊢ gsrc_interp s.
  Proof. by rewrite /bor_sem /= /cif_gsrc sem_cif_in. Qed.
  Lemma cif_cellsvec_sem {cs fv} :
    bor_sem (cif_cellsvec cs fv : cifOF CON $oi Σ) ⊣⊢ cs ^↦!∗ fv.
  Proof. by rewrite /bor_sem /= /cif_cellsvec sem_cif_in. Qed.
  Lemma cif_pure_sem {φ} :
    bor_sem (cif_pure φ : cifOF CON $oi Σ) ⊣⊢ ⌜φ⌝.
  Proof. done. Qed.
  Lemma cif_or_sem {Px Qx : cifOF CON $oi Σ} :
    bor_sem (cif_or Px Qx) ⊣⊢ bor_sem Px ∨ bor_sem Qx.
  Proof. done. Qed.
  Lemma cif_ex_sem {A} {Φ : A → cifOF CON $oi Σ} :
    bor_sem (cif_ex Φ) ⊣⊢ ∃ a, bor_sem (Φ a).
  Proof. done. Qed.
End model.

(** ** What is left, and the one thing in the way

  With the constructors and the two judgments in place, the remaining
  instances - [TypeFml], [GsrcSem], [HeapSem], [PcellFml], [AtomicInvFml],
  [LocalInvFml], [AltSem] and hence [typeG] - are mostly mechanical: every
  non-judgment equation is [sem_cif_in] on the leaf lemmas above, and the
  [AltSem] fields are [Deriv_factor'] / [der_sound] / [Deriv_map] on the two
  judgments, following [nola/iris/inv_deriv.v].

  One thing blocks [TypeFml]: its field [fml_cofe :: Cofe (FML $oi Σ)].  A
  [cif] is *not* a COFE.  Nola's [cit] is complete as a [prost] - a
  productivity structure - not as an OFE ([nola/util/cit.v]'s
  [cit_prolimit], "[cit] is complete"), and recursive definitions over it go
  through [profix] with [Productive], not through Banach's fixed point:
  [nola/examples/rust_halt/rec.v] defines [ty_rec F := profix F].

  [typing/fixpoint.v] builds a recursive type as the COFE limit [compl] of a
  chain of ghost assertions, which is the step-indexed idiom.  Moving it to
  [profix]/[Productive] - and dropping [fml_cofe] from [TypeFml] - is the
  next piece of work, and it is the last structural obstacle between here
  and [bor_sem := ⟦⟧ᶜ(der)]. *)
