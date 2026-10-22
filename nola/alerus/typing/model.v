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

(** ** An existential over a syntactic type's values

  [cif]'s own existential [cif_ex] stores the index *type* in the formula's
  selector, which caps it at [cif_sel]'s universe - strictly below the one
  [indep_interp_of_syn_type] lives in, so [cif_ex] cannot quantify over
  [~~𝔄].  This constructor stores the *syntactic* type instead and takes its
  interpretation as the inductive domain, which is not capped. *)
Variant exsCT_id := .
Definition exsCT : cifcon :=
  Cifcon exsCT_id syn_type indep_interp_of_syn_type (λ _, Empty_set)
    (λ _, unitO) _.

Notation exsC := (inC exsCT).

Section exsC.
  Context `{!exsC CON} {Σ}.
  Definition cif_exs {𝔄} (Φx : (~~𝔄) → cif CON Σ) : cif CON Σ :=
    cif_in exsCT 𝔄 Φx nullary ().

  #[export] Instance cif_exs_ne {𝔄} n :
    Proper (pointwise_relation (~~𝔄) (dist n) ==> dist n) (@cif_exs 𝔄).
  Proof. move=> ???. rewrite /cif_exs. solve_proper. Qed.

  #[export] Program Instance exsCT_ecsem {JUDG} : Ecsem exsCT CON JUDG Σ :=
    ECSEM (λ _ _ _ Φx _ _, ∃ a, Φx a)%I _.
  Next Obligation. solve_proper. Qed.
End exsC.

Notation exsCS := (inCS exsCT).

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
  Context `{!alerusC CON, !naInvC CON, !exsC CON} {JUDG Σ}
    `{!alerusGS (cifOF CON) Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
      !alerusCS CON JUDG Σ, !naInvCS CON JUDG Σ, !exsCS CON JUDG Σ}.
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

  (** The leaf equations at an arbitrary candidate.  Each is [sem_cif_in] on
    the token semantics, which does not mention [δ]. *)
  Lemma cif_alive_sem_at {δ κ} : ⟦ cif_alive κ : cif CON Σ ⟧ᶜ(δ) ⊣⊢ @[κ].
  Proof. by rewrite /cif_alive sem_cif_in. Qed.
  Lemma cif_dead_sem_at {δ κ} : ⟦ cif_dead κ : cif CON Σ ⟧ᶜ(δ) ⊣⊢ [†κ].
  Proof. by rewrite /cif_dead sem_cif_in. Qed.
  Lemma cif_cells_sem_at {δ l cs fv} :
    ⟦ cif_cells l cs fv : cif CON Σ ⟧ᶜ(δ) ⊣⊢ l ↦[^ cs ]!∗ fv.
  Proof. by rewrite /cif_cells sem_cif_in. Qed.
  Lemma cif_ccells_sem_at {δ l fv} :
    ⟦ cif_ccells l fv : cif CON Σ ⟧ᶜ(δ) ⊣⊢ l #↦!∗ fv.
  Proof. by rewrite /cif_ccells sem_cif_in. Qed.
  Lemma cif_cmapstoany_sem_at {δ l} :
    ⟦ cif_cmapstoany l : cif CON Σ ⟧ᶜ(δ) ⊣⊢ l #↦∗_.
  Proof. by rewrite /cif_cmapstoany sem_cif_in. Qed.
  Lemma cif_freeable_sem_at {δ n sz l} :
    ⟦ cif_freeable n sz l : cif CON Σ ⟧ᶜ(δ) ⊣⊢ freeable_sz n sz l.
  Proof. by rewrite /cif_freeable sem_cif_in. Qed.
  Lemma cif_vo_sem_at {δ ξ x d} :
    ⟦ cif_vo ξ x d : cif CON Σ ⟧ᶜ(δ) ⊣⊢ .VO[ξ] x d.
  Proof. by rewrite /cif_vo sem_cif_in. Qed.
  Lemma cif_pc_sem_at {δ ξ x xp d} :
    ⟦ cif_pc ξ x xp d : cif CON Σ ⟧ᶜ(δ) ⊣⊢ .PC[ξ] x xp d.
  Proof. by rewrite /cif_pc sem_cif_in. Qed.
  Lemma cif_gsrc_sem_at {δ s} :
    ⟦ cif_gsrc s : cif CON Σ ⟧ᶜ(δ) ⊣⊢ gsrc_interp s.
  Proof. by rewrite /cif_gsrc sem_cif_in. Qed.
  Lemma cif_exs_sem_at {δ 𝔄} {Φ : (~~𝔄) → cif CON Σ} :
    ⟦ cif_exs Φ ⟧ᶜ(δ) ⊣⊢ ∃ a : ~~𝔄, ⟦ Φ a ⟧ᶜ(δ).
  Proof. by rewrite /cif_exs sem_cif_in. Qed.
  Lemma cif_cellsvec_sem_at {δ cs fv} :
    ⟦ cif_cellsvec cs fv : cif CON Σ ⟧ᶜ(δ) ⊣⊢ cs ^↦!∗ fv.
  Proof. by rewrite /cif_cellsvec sem_cif_in. Qed.

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
    point of separating [AlerusSem] from [alerusGS].

    Note it is also [alerus_WGuard_of] applied to the candidate's
    interpretation - definitionally so - which is what [AltSem]'s
    [alt_WGuard] needs, since a candidate there is just a function. *)
  Definition alerus_WGuard_at δ : iProp Σ :=
    @alerus_WGuard (cifOF CON) Σ _ (AlerusSem_at δ).
  Lemma alerus_WGuard_at_of δ :
    alerus_WGuard_at δ =
      @alerus_WGuard_of (cifOF CON) Σ _ (AlerusSem_at δ)
        (λ Px : cifOF CON $oi Σ, ⟦ Px ⟧ᶜ(δ)).
  Proof. done. Qed.
End sem_at.

(** ** The storable lifetime inclusion and the storable alteration

  [StBor] in [nola/alerus/lifetime/lifetime_full.v] abstracts the two places
  where a full borrow mentions the interpretation.  Here both become the
  *family*: the inclusion holds at every good interpretation's guarding world
  satisfaction, and the alteration holds at every good interpretation.  Both
  are plain [iProp]s - [idx_bor] is not a formula - so no judgment, and hence
  no family rule, is involved: each eliminates at *every* good [δ], which is
  exactly what makes a full borrow storable. *)
Section stbor_at.
  Context `{!alerusC CON, !naInvC CON, !exsC CON} {JUDG Σ}
    `{!alerusGS (cifOF CON) Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
      !alerusCS CON JUDG Σ, !naInvCS CON JUDG Σ, !exsCS CON JUDG Σ}.
  Context (δ : JUDG -n> iProp Σ).
  Local Instance AlerusSem_δ0 : AlerusSem (cifOF CON) Σ := AlerusSem_at δ.

  Lemma st_refl_at {κ} : ⊢ @[κ] &&{alerus_WGuard_at δ}&&> @[κ].
  Proof. exact: guard_refl. Qed.
  Lemma st_meet_l_at {κ κ'} : ⊢ @[κ ⊓ κ'] &&{alerus_WGuard_at δ}&&> @[κ].
  Proof. exact: llftl_intersect_incl_l. Qed.
  Lemma st_meet_r_at {κ κ'} : ⊢ @[κ' ⊓ κ] &&{alerus_WGuard_at δ}&&> @[κ].
  Proof. exact: llftl_intersect_incl_r. Qed.
  Lemma st_sub_at {κ κ'} : κ' ⊆ κ → ⊢ @[κ] &&{alerus_WGuard_at δ}&&> @[κ'].
  Proof. exact (llftl_incl_sub κ κ'). Qed.
  Lemma eternal_incl_at {κ} :
    eternal_tok alerus_eternal_name κ ⊢
      @[static] &&{alerus_WGuard_at δ}&&> @[κ].
  Proof.
    iIntros "#tok".
    iApply (guard_wsat_incl
      (W':=eternal_wsat alerus_eternal_name llft_alive)).
    iApply (eternal_tok_guard with "tok").
  Qed.

  Lemma st_glb_at {κ κ' κ''} :
    (@[κ] &&{alerus_WGuard_at δ}&&> @[κ']) -∗
    (@[κ] &&{alerus_WGuard_at δ}&&> @[κ'']) -∗
    @[κ] &&{alerus_WGuard_at δ}&&> @[κ' ⊓ κ''].
  Proof. exact: llftl_incl_glb. Qed.

  (** The same, with the meet given by an equation: [llftl_incl_glb] joins
    two lifetimes, and the caller usually knows the join by a set fact
    rather than syntactically. *)
  Lemma st_glb_eq_at {κ κ1 κ2 κ'} :
    κ1 ⊓ κ2 = κ' →
    (@[κ] &&{alerus_WGuard_at δ}&&> @[κ1]) -∗
    (@[κ] &&{alerus_WGuard_at δ}&&> @[κ2]) -∗
    @[κ] &&{alerus_WGuard_at δ}&&> @[κ'].
  Proof. move=> <-. exact: st_glb_at. Qed.
End stbor_at.

Section stbor.
  Context `{!alerusC CON, !naInvC CON, !exsC CON} {JUDG Σ}
    `{!alerusGS (cifOF CON) Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
      !alerusCS CON JUDG Σ, !naInvCS CON JUDG Σ, !exsCS CON JUDG Σ}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** The eternalized part of a storable inclusion.

    Nola's persistent lifetime inclusion
    [lft_sincl α β := [†α] ∨ [∞ lft_diff β α]] ([nola/iris/lft.v]) is plain
    ghost state, and that is what makes it readable at every candidate: it
    mentions no interpretation, so nothing has to quantify over
    interpretations to state it.  This is the counterpart here.  Every atom
    of [κ'] is either supplied by [κ] itself or covered by one of a finite
    set of eternalized lifetimes; the set is what makes the tokens compose
    under union, which is what transitivity needs. *)
  Definition eternal_lfts (S : gset lft) : iProp Σ :=
    □ ∀ κ0 : lft, ⌜κ0 ∈ S⌝ → eternal_tok alerus_eternal_name κ0.
  Definition covers (κ : lft) (S : gset lft) (κ' : lft) : Prop :=
    ∀ a, a ∈ κ' → a ∈ κ ∨ ∃ κ0, κ0 ∈ S ∧ a ∈ κ0.

  Definition st_incl_cif (κ κ' : lft) : iProp Σ :=
    ∃ S : gset lft, ⌜covers κ S κ'⌝ ∧ eternal_lfts S.
  (** The storable alteration: the equivalence at *every* interpretation,
    good or not.

    Dropping [⌜Deriv (λ _, True) δ⌝] is what takes [Deriv] - and with it
    [Jsem] - out of [idx_bor], which is [idxborJT_sem].  Nothing is lost on
    the elimination side, since a borrow is only ever opened at an
    interpretation that is a candidate anyway.  What it costs is that
    [AltSem]'s [idxbor_fml_iff_at] now asks for the alteration off the
    candidates too; see [typing/inst.v]. *)
  Definition st_iff_cif (Px Qx : cifOF CON $oi Σ) : iProp Σ :=
    □ ∀ δ, ⟦ Px ⟧ᶜ(δ) ↔ ⟦ Qx ⟧ᶜ(δ).

  #[export] Instance st_iff_cif_ne : NonExpansive2 st_iff_cif.
  Proof. solve_proper. Qed.

  (** [eternal_lfts] is persistent, monotone and union-closed *)
  #[export] Instance eternal_lfts_persistent {S} : Persistent (eternal_lfts S).
  Proof. exact _. Qed.
  Lemma eternal_lfts_empty : ⊢ eternal_lfts ∅.
  Proof. iIntros "!>" (κ0 ?). set_solver. Qed.
  Lemma eternal_lfts_union {S S'} :
    eternal_lfts S -∗ eternal_lfts S' -∗ eternal_lfts (S ∪ S').
  Proof.
    iIntros "#e #e' !>" (κ0 H).
    destruct (decide (κ0 ∈ S)) as [?|?]; [by iApply "e"|].
    iApply "e'". iPureIntro. set_solver.
  Qed.

  (** [covers] is reflexive, transitive and monotone in the obvious ways *)
  Local Lemma covers_sub {κ κ'} : κ' ⊆ κ → covers κ ∅ κ'.
  Proof. move=> Hsub a ?. left. exact: Hsub. Qed.
  Local Lemma covers_trans {κ κ' κ'' S S'} :
    covers κ S κ' → covers κ' S' κ'' → covers κ (S ∪ S') κ''.
  Proof.
    move=> H H' a /H'[/H[?|[κ0[??]]]|[κ0[??]]];
      [by left|right|right]; exists κ0; split=>//; set_solver.
  Qed.
  Local Lemma covers_union {κ κ' κ'' S S'} :
    covers κ S κ' → covers κ S' κ'' → covers κ (S ∪ S') (κ' ∪ κ'').
  Proof.
    move=> H H' a. rewrite elem_of_union=> -[/H|/H']-[?|[κ0[??]]];
      [by left|right|by left|right]; exists κ0; split=>//; set_solver.
  Qed.

  Lemma eternal_lfts_mono {S S'} :
    S' ⊆ S → eternal_lfts S ⊢ eternal_lfts S'.
  Proof.
    move=> ?. iIntros "#e !>" (κ0 ?). iApply "e". iPureIntro. set_solver.
  Qed.

  (** Two set facts [set_solver] does not get on [lft] *)
  Local Lemma lft_inter_diff_union (κ κ' : lft) : (κ' ∩ κ) ⊓ (κ' ∖ κ) = κ'.
  Proof.
    apply set_eq=> x. unfold meet, llft_intersect.
    rewrite elem_of_union elem_of_intersection elem_of_difference.
    destruct (decide (x ∈ κ)); tauto.
  Qed.
  Local Lemma lft_inter_subseteq (κ κ' : lft) : κ' ∩ κ ⊆ κ.
  Proof. move=> x. rewrite elem_of_intersection. tauto. Qed.

  (** The eternalized lifetimes are guarded by anything, at every candidate:
    [eternal_tok_guard] is a fact about ghost state, and [llftl_incl_glb]
    folds the covering lifetimes back together. *)
  Lemma eternal_lfts_guard_at δ {κ} S :
    ∀ B, covers ∅ S B → eternal_lfts S ⊢ @[κ] &&{alerus_WGuard_at δ}&&> @[B].
  Proof.
    move: S. apply: set_ind_L.
    { move=> B HB. iIntros "_". iApply st_sub_at.
      move=> a /HB[|[?[??]]]; set_solver. }
    move=> κ0 S Hκ0 IH B HB. iIntros "#e".
    iApply (st_glb_eq_at δ (lft_inter_diff_union κ0 B) with "[] []").
    - iApply (guard_trans with "[] []"); last first.
      { iApply st_sub_at. exact: lft_inter_subseteq. }
      iApply (guard_trans with "[] []"); last first.
      { iApply (eternal_incl_at δ). iApply "e". iPureIntro. set_solver. }
      iApply st_sub_at. unfold static, llft_empty. set_solver.
    - iApply IH; [|iApply (eternal_lfts_mono with "e"); set_solver].
      move=> a. rewrite elem_of_difference=> -[/HB[|[κ1[Hκ1 ?]]] ?];
        [set_solver|]. right. exists κ1. split=>//.
      move: Hκ1. rewrite elem_of_union elem_of_singleton=> -[?|?];
        [by subst|done].
  Qed.

  (** The elimination rule: a storable inclusion is a guard at every
    candidate.  [κ' ∩ κ] comes from the left-hand side by [llftl_incl_sub],
    [κ' ∖ κ] from the eternalized lifetimes, and [llftl_incl_glb] joins
    them. *)
  Lemma st_incl_cif_at δ {κ κ'} :
    st_incl_cif κ κ' ⊢ @[κ] &&{alerus_WGuard_at δ}&&> @[κ'].
  Proof.
    iIntros "(%S & %Hc & #e)".
    iApply (st_glb_eq_at δ (lft_inter_diff_union κ κ') with "[] []").
    { iApply st_sub_at. exact: lft_inter_subseteq. }
    iApply (eternal_lfts_guard_at δ S with "e").
    move=> a. rewrite elem_of_difference=> -[/Hc[?|?] ?]; [done|by right].
  Qed.

  Lemma st_incl_cif_of_sub {κ κ'} : κ' ⊆ κ → ⊢ st_incl_cif κ κ'.
  Proof.
    move=> ?. iExists ∅. iSplit; [iPureIntro; exact: covers_sub|].
    iApply eternal_lfts_empty.
  Qed.
  Lemma st_incl_cif_refl {κ} : ⊢ st_incl_cif κ κ.
  Proof. by iApply st_incl_cif_of_sub. Qed.
  Lemma st_incl_cif_trans {κ κ' κ''} :
    st_incl_cif κ κ' -∗ st_incl_cif κ' κ'' -∗ st_incl_cif κ κ''.
  Proof.
    iIntros "(%S & %H & #e) (%S' & %H' & #e')". iExists (S ∪ S').
    iSplit; [iPureIntro; exact: covers_trans|].
    iApply (eternal_lfts_union with "e e'").
  Qed.
  Lemma st_incl_cif_meet_l {κ κ'} : ⊢ st_incl_cif (κ ⊓ κ') κ.
  Proof.
    apply st_incl_cif_of_sub. unfold meet, llft_intersect. set_solver.
  Qed.
  Lemma st_incl_cif_meet_r {κ κ'} : ⊢ st_incl_cif (κ' ⊓ κ) κ.
  Proof.
    apply st_incl_cif_of_sub. unfold meet, llft_intersect. set_solver.
  Qed.
  Lemma st_incl_cif_glb {κ κ' κ''} :
    st_incl_cif κ κ' -∗ st_incl_cif κ κ'' -∗ st_incl_cif κ (κ' ⊓ κ'').
  Proof.
    iIntros "(%S & %H & #e) (%S' & %H' & #e')". iExists (S ∪ S').
    iSplit; [iPureIntro; exact: covers_union|].
    iApply (eternal_lfts_union with "e e'").
  Qed.

  (** Eternalizing a lifetime gives a storable inclusion from [static] *)
  Lemma st_incl_cif_eternalize {κ} :
    eternal_tok alerus_eternal_name κ ⊢ st_incl_cif static κ.
  Proof.
    iIntros "#tok". iExists {[κ]}. iSplit.
    { iPureIntro=> a ?. right. exists κ. split=>//. set_solver. }
    iIntros "!>" (κ0 Hκ0). move: Hκ0=> /elem_of_singleton->. iApply "tok".
  Qed.
  Lemma st_iff_cif_refl {Px} : ⊢ st_iff_cif Px Px.
  Proof. iIntros "!>" (δ). by iSplit; iIntros "$". Qed.
  Lemma st_iff_cif_sym {Px Qx} : st_iff_cif Px Qx -∗ st_iff_cif Qx Px.
  Proof.
    iIntros "#g !>" (δ). iSplit; iIntros "P".
    - by iApply "g". - by iApply "g".
  Qed.
  Lemma st_iff_cif_trans {Px Qx Rx} :
    st_iff_cif Px Qx -∗ st_iff_cif Qx Rx -∗ st_iff_cif Px Rx.
  Proof.
    iIntros "#g #g' !>" (δ). iSplit; iIntros "P".
    - iApply "g'". by iApply "g". - iApply "g". by iApply "g'".
  Qed.

  Lemma st_iff_cif_sep {Px Px' Qx Qx'} :
    st_iff_cif Px Px' -∗ st_iff_cif Qx Qx' -∗
      st_iff_cif (cif_sep Px Qx) (cif_sep Px' Qx').
  Proof.
    iIntros "#g #g' !>" (δ). iSplit; iIntros "[P Q]".
    - iSplitL "P"; [by iApply "g"|by iApply "g'"].
    - iSplitL "P"; [by iApply "g"|by iApply "g'"].
  Qed.

  Definition stBor_cif : StBor (cifOF CON) Σ := {|
    st_incl := st_incl_cif; st_iff := st_iff_cif;
    st_incl_persistent := (λ _ _, _); st_iff_persistent := (λ _ _, _);
    st_iff_ne := st_iff_cif_ne;
    st_incl_refl := @st_incl_cif_refl;
    st_incl_trans := @st_incl_cif_trans;
    st_incl_meet_l := @st_incl_cif_meet_l;
    st_incl_meet_r := @st_incl_cif_meet_r;
    st_incl_glb := @st_incl_cif_glb;
    st_iff_refl := @st_iff_cif_refl;
    st_iff_sym := @st_iff_cif_sym;
    st_iff_trans := @st_iff_cif_trans;
  |}.
End stbor.

(** The two elimination rules, at a good interpretation: each is the family
  instantiated at that interpretation. *)
Section stbor_sem.
  Context `{!alerusC CON, !naInvC CON, !exsC CON} {JUDG Σ}
    `{!alerusGS (cifOF CON) Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
      !alerusCS CON JUDG Σ, !naInvCS CON JUDG Σ, !exsCS CON JUDG Σ}.
  Context (δ : JUDG -n> iProp Σ).
  Local Instance AlerusSem_δ1 : AlerusSem (cifOF CON) Σ := AlerusSem_at δ.
  Local Instance stBor_δ : StBor (cifOF CON) Σ := stBor_cif (JUDG:=JUDG).

  Lemma stBorSem_at (Hδ : Deriv (λ _, True) δ) : StBorSem.
  Proof.
    split.
    - iIntros (κ κ') "#g". iApply (st_incl_cif_at δ with "g").
    - iIntros (Px Qx) "#g !>". iApply ("g" $! δ).
    - iIntros (Px Px' Qx Qx') "g g'". iApply (st_iff_cif_sep with "g g'").
  Qed.

  (** The lifetime logic's facts, replayed at this interpretation *)
  Context (Hδ : Deriv (λ _, True) δ).
  Local Instance stBorSem_δ : StBorSem := stBorSem_at Hδ.

  Lemma idxbor_guard_at {κ idx} {Px : cif CON Σ} {G : iProp Σ} :
    idx_bor κ idx Px -∗ (G &&{alerus_WGuard_at δ}&&> @[κ]) -∗
    (G &&{alerus_WGuard_at δ}&&> idx_bor_tok idx) -∗
    G &&{alerus_WGuard_at δ}&&> (@[κ] ∗ ⟦ Px ⟧ᶜ(δ)).
  Proof. iIntros "#b". iApply (llftl_idx_bor_guard' with "[//] b"). Qed.

  Lemma Ltok_guard_frac_at' {γ L q} :
    frac_key_tok γ L ⊢ frac_tok γ q &&{alerus_WGuard_at δ}&&> llctx_interp L.
  Proof. exact Ltok_guard_frac. Qed.

  Lemma shr_tok_guard_at {κ γc sn} {Px : cif CON Σ} :
    sinv_tok (sinvGS0:=shrGS) sn (cif_shr (set_map ra.LtAtomSwell κ) γc Px) ⊢
      @[κ] &&{alerus_WGuard_at δ}&&> ⟦ Px ⟧ᶜ(δ).
  Proof. exact (llftl_shr_tok_guard_alive κ γc sn Px). Qed.
End stbor_sem.

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

(** [iffJT]: a semantic equivalence of two formulas, as a judgment.

  This is the alteration a stored borrow carries, exactly as
  [nola/iris/borrow_deriv.v]'s [bor δ α Px := ∃ Qx, □ δ (jbupd Px Qx) ∗
  □ δ (jbupd Qx Px) ∗ bor_tok α Qx] carries two [jbupd]s - the thesis's
  § 6.4.  Its semantics *applies* the interpretation, which is what lets
  [Deriv_map] change it and so what makes the alteration available at the
  candidates a stored borrow maps into rather than at every interpretation
  whatsoever. *)
Variant iffJT_id := .
Definition iffJT (FM : ofe) : ofe := tagged iffJT_id (FM * FM).
Notation iffJ FM := (inJ (iffJT FM)).

(** [inclJT]: a storable lifetime inclusion, as a judgment.

  [st_incl κ κ'] quantifies the guarding world satisfaction, so like a guard
  it cannot be written in an [Ecsem]: the body would have to apply the
  semantics to a sub-formula, which is only allowed contractively, and a
  Leaf guard has no later.  It goes through a judgment for that reason
  alone - its *semantics* does not mention the interpretation. *)
Variant inclJT_id := .
Definition inclJT : ofe := tagged inclJT_id (leibnizO lft * leibnizO lft).
Notation inclJ := (inJ inclJT).

(** [idxborJT]: an indexed borrow, as a judgment *)
Variant idxborJT_id := .
Definition idxborJT (FM : ofe) : ofe :=
  tagged idxborJT_id (leibnizO lft * leibnizO Idx * FM).
Notation idxborJ FM := (inJ (idxborJT FM)).

Section judg.
  Context `{!alerusC CON, !naInvC CON, !exsC CON} {JUDG Σ}
    `{!alerusGS (cifOF CON) Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
      !alerusCS CON JUDG Σ, !naInvCS CON JUDG Σ, !exsCS CON JUDG Σ}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** Semantics of the guard judgment: the guard at the candidate's own
    guarding world satisfaction *)
  Definition guardJT_sem δ (J : guardJT (cifO CON Σ)) : iProp Σ :=
    ⟦ J.(untag).1 ⟧ᶜ(δ) &&{alerus_WGuard_at δ}&&> ⟦ J.(untag).2 ⟧ᶜ(δ).
  #[export] Instance guardJT_sem_ne {δ} : NonExpansive (guardJT_sem δ).
  Proof. move=> ?[[??]][[??]][/=??]. solve_proper. Qed.
  #[export] Instance guardJT_dsem
    : Dsem JUDG (guardJT (cifO CON Σ)) (iProp Σ) := DSEM guardJT_sem _.

  (** Semantics of the alteration judgment: the equivalence at the
    candidate's own interpretation *)
  Definition iffJT_sem δ (J : iffJT (cifO CON Σ)) : iProp Σ :=
    □ (⟦ J.(untag).1 ⟧ᶜ(δ) ↔ ⟦ J.(untag).2 ⟧ᶜ(δ)).
  #[export] Instance iffJT_sem_ne {δ} : NonExpansive (iffJT_sem δ).
  Proof. move=> ?[[??]][[??]][/=??]. solve_proper. Qed.
  #[export] Instance iffJT_dsem
    : Dsem JUDG (iffJT (cifO CON Σ)) (iProp Σ) := DSEM iffJT_sem _.

End judg.

(** Semantics of the indexed-borrow judgment.  [idx_bor] needs the whole of
  [AlerusSem] - a borrow is indexed by a lifetime, and the lifetime logic's
  parameters come with it - so the candidate's interpretation is installed
  as the ambient one for the length of this section. *)
Section idxbor_judg.
  Context `{!alerusC CON, !naInvC CON, !exsC CON} {JUDG Σ}
    `{!alerusGS (cifOF CON) Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
      !alerusCS CON JUDG Σ, !naInvCS CON JUDG Σ, !exsCS CON JUDG Σ}.
  Context (δ : JUDG -n> iProp Σ).
  Local Instance AlerusSem_δ : AlerusSem (cifOF CON) Σ := AlerusSem_at δ.
  Local Instance stBor_δ' : StBor (cifOF CON) Σ := stBor_cif (JUDG:=JUDG).

  Definition idxborJT_sem_at (J : idxborJT (cifO CON Σ)) : iProp Σ :=
    idx_bor (FML:=cifOF CON) J.(untag).1.1 J.(untag).1.2 J.(untag).2.
  #[export] Instance idxborJT_sem_at_ne : NonExpansive idxborJT_sem_at.
  Proof. move=> ?[[[??]?]][[[??]?]][[/=/leibniz_equiv_iff<-?]?]. solve_proper. Qed.
End idxbor_judg.

Section incl_judg.
  Context `{!alerusC CON, !naInvC CON, !exsC CON} {JUDG Σ}
    `{!alerusGS (cifOF CON) Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
      !alerusCS CON JUDG Σ, !naInvCS CON JUDG Σ, !exsCS CON JUDG Σ}.

  Definition inclJT_sem (J : inclJT) : iProp Σ :=
    st_incl_cif (CON:=CON) J.(untag).1 J.(untag).2.
  #[export] Instance inclJT_sem_ne : NonExpansive inclJT_sem.
  Proof. move=> ?[[??]][[??]][/=/leibniz_equiv_iff<-/leibniz_equiv_iff<-] //. Qed.
  #[export] Instance inclJT_dsem : Dsem JUDG inclJT (iProp Σ) :=
    DSEM (λ _, inclJT_sem) _.
End incl_judg.

Section judg2.
  Context `{!alerusC CON, !naInvC CON, !exsC CON} {JUDG Σ}
    `{!alerusGS (cifOF CON) Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
      !alerusCS CON JUDG Σ, !naInvCS CON JUDG Σ, !exsCS CON JUDG Σ}.
  (** [idx_bor] no longer mentions the interpretation at all: with [st_incl]
    and [st_iff] abstracted, an indexed borrow is [st_incl κ κ'], a family of
    alterations and a [sinv_tok], none of which is interpreted.  So the
    judgment's semantics is constant in [δ] - which is what lets a borrow be
    stored. *)
  #[export] Instance idxborJT_dsem
    : Dsem JUDG (idxborJT (cifO CON Σ)) (iProp Σ) :=
    DSEM (λ _, idxborJT_sem_at) _.
End judg2.

(** Semantics of the two judgment types registered *)
Notation guardJS CON JUDG Σ := (inJS (guardJT (cifO CON Σ)) JUDG (iProp Σ)).
Notation idxborJS CON JUDG Σ := (inJS (idxborJT (cifO CON Σ)) JUDG (iProp Σ)).
Notation inclJS CON JUDG Σ := (inJS inclJT JUDG (iProp Σ)).
Notation iffJS CON JUDG Σ := (inJS (iffJT (cifO CON Σ)) JUDG (iProp Σ)).

(** ** The judgment constructors

  [guard_fml] and [idxbor_fml] as formulas: each holds its sub-formulas
  *syntactically* and means "the judgment is derivable at [δ]", under a [□]
  so that the formula is persistent.  This is [inv'] in
  [nola/iris/inv_deriv.v]. *)
Variant guardCT_id := .
Definition guardCT : cifcon :=
  Cifcon guardCT_id unit (λ _, Empty_set) (λ _, bool) (λ _, unitO) _.
Notation guardC := (inC guardCT).

Variant inclCT_id := .
Definition inclCT : cifcon :=
  Cifcon inclCT_id (lft * lft)%type (λ _, Empty_set) (λ _, Empty_set)
    (λ _, unitO) _.
Notation inclC := (inC inclCT).

Variant idxborCT_id := .
Definition idxborCT : cifcon :=
  Cifcon idxborCT_id (lft * Idx)%type (λ _, Empty_set) (λ _, unit)
    (λ _, unitO) _.
Notation idxborC := (inC idxborCT).

Section judgC.
  Context `{!guardC CON, !idxborC CON, !inclC CON} {Σ}.
  Definition cif_incl (κ κ' : lft) : cif CON Σ :=
    cif_in inclCT (κ, κ') nullary nullary ().
  Definition cif_guard (Px Qx : cif CON Σ) : cif CON Σ :=
    cif_in guardCT () nullary (binary Px Qx) ().
  Definition cif_idxbor κ idx (Px : cif CON Σ) : cif CON Σ :=
    cif_in idxborCT (κ, idx) nullary (unary Px) ().

  (** Both are productive, so a type former may nest them *)
  #[export] Instance cif_guard_ne : NonExpansive2 cif_guard.
  Proof. move=> ???????. rewrite /cif_guard. solve_proper. Qed.
  #[export] Instance cif_idxbor_ne {κ idx} : NonExpansive (cif_idxbor κ idx).
  Proof. move=> ????. rewrite /cif_idxbor. solve_proper. Qed.
  #[export] Instance cif_idxbor_productive {κ idx} :
    Productive (cif_idxbor κ idx).
  Proof.
    move=> ????. apply cif_in_preserv_productive=>//. by apply fun_proeqv_later.
  Qed.

  Context {JUDG} `{guard_j0 : !guardJ (cifO CON Σ) JUDG,
    idxbor_j0 : !idxborJ (cifO CON Σ) JUDG, incl_j0 : !inclJ JUDG,
    iff_j0 : !iffJ (cifO CON Σ) JUDG, !Jsem JUDG (iProp Σ)}.
  Definition incl_j (κ κ' : lft) : JUDG := incl_j0 (Tagged (κ, κ')).
  (** The judgments as elements of [JUDG] *)
  Definition guard_j (Px Qx : cif CON Σ) : JUDG :=
    guard_j0 (Tagged (Px, Qx)).
  Definition idxbor_j κ idx (Px : cif CON Σ) : JUDG :=
    idxbor_j0 (Tagged (κ, idx, Px)).
  #[export] Instance guard_j_ne : NonExpansive2 guard_j.
  Proof. unfold guard_j=> ???????. f_equiv. by split. Qed.
  Definition iff_j (Px Qx : cif CON Σ) : JUDG := iff_j0 (Tagged (Px, Qx)).
  #[export] Instance idxbor_j_ne {κ idx} : NonExpansive (idxbor_j κ idx).
  Proof. unfold idxbor_j=> ????. f_equiv. by split; [split|]. Qed.
  #[export] Instance iff_j_ne : NonExpansive2 iff_j.
  Proof. unfold iff_j=> ???????. f_equiv. by split. Qed.

  #[export] Program Instance guardCT_ecsem : Ecsem guardCT CON JUDG Σ :=
    ECSEM (λ _ δ _ _ Ψx _, □ δ (guard_j (Ψx true) (Ψx false)))%I _.
  Next Obligation. solve_proper. Qed.
  (** The indexed borrow and the stored inclusion are ordinary judgments,
    [□ δ J] as in [nola/iris/inv_deriv.v]'s [inv'].  Nothing quantifies the
    interpretation *inside* a formula, which matters twice over:

    - [Deriv] mentions [Jsem], and [Jsem] mentions the semantics of the
      formulas, so a [Deriv] inside an [Ecsem] would make [Csem] and [Jsem]
      mutually dependent and the model unconstructible (see
      [typing/inst.v]);
    - it is not needed.  With [st_incl] and [st_iff] abstracted, [idx_bor]
      and [st_incl] do not mention the interpretation at all, so the two
      judgments' semantics is *constant* in [δ].  Reading one at another
      candidate is then [dinto δ δ'] followed by [Deriv_factor'] at [δ'],
      and transforming one is [Deriv_map]. *)
  (** A stored indexed borrow is the *relaxed* borrower: the token part is
    a judgment whose semantics mentions no interpretation, and the
    alteration is read at [δ].  This is [bor δ] over [bor_tok] in
    [nola/iris/borrow_deriv.v], and [cif_pbor]'s [Ecsem] over [pbor_tok] in
    [nola/iris/pborrow_deriv.v], which is what [rust_halt]'s [ty_mutref]
    stores. *)
  #[export] Program Instance idxborCT_ecsem : Ecsem idxborCT CON JUDG Σ :=
    ECSEM (λ _ δ s _ Ψx _, ∃ Px', □ δ (iff_j Px' (Ψx ())) ∗
      □ δ (idxbor_j s.1 s.2 Px'))%I _.
  Next Obligation. solve_proper. Qed.
  #[export] Program Instance inclCT_ecsem : Ecsem inclCT CON JUDG Σ :=
    ECSEM (λ _ δ s _ _ _, □ δ (incl_j s.1 s.2))%I _.
  Next Obligation. solve_proper. Qed.
End judgC.

Notation guardCS := (inCS guardCT).
Notation idxborCS := (inCS idxborCT).
Notation inclCS := (inCS inclCT).

(** ** Constructor and judgment constraints

  As in [rust_halt/base.v], the development is parametric in a constructor
  signature [CON] and a judgment type [JUDG] that *contain* the ones above;
  these classes say so. *)
Class typingC CON : Type := TYPING_C {
  typingC_alerus :: alerusC CON;
  typingC_naInv :: naInvC CON;
  typingC_guard :: guardC CON;
  typingC_idxbor :: idxborC CON;
  typingC_incl :: inclC CON;
  typingC_exs :: exsC CON;
}.
Class typingJ CON JUDG Σ : Type := TYPING_J {
  typingJ_guard :: guardJ (cifO CON Σ) JUDG;
  typingJ_idxbor :: idxborJ (cifO CON Σ) JUDG;
  typingJ_incl :: inclJ JUDG;
  typingJ_iff :: iffJ (cifO CON Σ) JUDG;
}.
Class typingCS CON JUDG Σ `{!typingC CON, !alerusGS (cifOF CON) Σ}
  `{!typingJ CON JUDG Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)} : Prop :=
  TYPING_CS {
  typingCS_alerus :: alerusCS CON JUDG Σ;
  typingCS_naInv :: naInvCS CON JUDG Σ;
  typingCS_guard :: guardCS CON JUDG Σ;
  typingCS_idxbor :: idxborCS CON JUDG Σ;
  typingCS_incl :: inclCS CON JUDG Σ;
  typingCS_exs :: exsCS CON JUDG Σ;
}.
Class typingJS CON JUDG Σ `{!typingC CON, !alerusGS (cifOF CON) Σ}
  `{!typingJ CON JUDG Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
    !typingCS CON JUDG Σ} : Prop := TYPING_JS {
  typingJS_guard :: guardJS CON JUDG Σ;
  typingJS_idxbor :: idxborJS CON JUDG Σ;
  typingJS_incl :: inclJS CON JUDG Σ;
  typingJS_iff :: iffJS CON JUDG Σ;
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
  Lemma cif_exs_sem {𝔄} {Φ : (~~𝔄) → cif CON Σ} :
    bor_sem (cif_exs Φ) ⊣⊢ ∃ a : ~~𝔄, bor_sem (Φ a).
  Proof. exact cif_exs_sem_at. Qed.
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

  Lemma cif_active_sem {γ} :
    bor_sem (cif_active γ : cifOF CON $oi Σ) ⊣⊢ own γ (Excl ()).
  Proof. by rewrite /bor_sem /= /cif_active sem_cif_in. Qed.
  Lemma cif_cna_active_sem {γ} :
    bor_sem (cif_cna_active γ : cifOF CON $oi Σ) ⊣⊢ cna_active γ.
  Proof. by rewrite /bor_sem /= /cif_cna_active sem_cif_in. Qed.
  Lemma cif_obs_sem {φ} :
    bor_sem (cif_obs φ : cifOF CON $oi Σ) ⊣⊢ ⟨π, φ π⟩.
  Proof. by rewrite /bor_sem /= /cif_obs sem_cif_in. Qed.
  Lemma cif_handle_sem {c} :
    bor_sem (cif_handle c : cifOF CON $oi Σ) ⊣⊢
      atomic_lock_handle atomic_lock_ctr_name c.
  Proof. by rewrite /bor_sem /= /cif_handle sem_cif_in. Qed.
  Lemma cif_na_inv_sem {N} {Px : cif CON Σ} :
    bor_sem (cif_na_inv N Px) ⊣⊢ na_inv_tok atomic_threadpool N Px.
  Proof. by rewrite /bor_sem /= /cif_na_inv sem_cif_in. Qed.
  Lemma cif_na_otok_sem {N} {Px : cif CON Σ} :
    bor_sem (cif_na_otok N Px) ⊣⊢ na_otok atomic_threadpool N Px.
  Proof. by rewrite /bor_sem /= /cif_na_otok sem_cif_in. Qed.
  Lemma cif_cna_inv_sem {γ p N} {Px : cif CON Σ} :
    bor_sem (cif_cna_inv γ p N Px) ⊣⊢ cna_inv γ p N Px.
  Proof. by rewrite /bor_sem /= /cif_cna_inv sem_cif_in. Qed.
  Lemma cif_cna_otok_sem {γ p N κ} {Px : cif CON Σ} :
    bor_sem (cif_cna_otok γ p N κ Px) ⊣⊢ cna_otok γ p N κ Px.
  Proof. by rewrite /bor_sem /= /cif_cna_otok sem_cif_in. Qed.

  (** Hence the formula language of [typing/ctx.v] *)
  #[export] Program Instance typeFml_cif : TypeFml (cifOF CON) Σ := {|
    false_fml := cif_pure False;
    pure_fml := (λ φ, cif_pure φ);
    ex_fml := (λ A Φ, cif_ex Φ);
    exs_fml := (λ 𝔄 Φ, cif_exs Φ);
    guard_fml := cif_guard;
    alive_fml := cif_alive;
    cells_fml := cif_cells;
    ccells_fml := cif_ccells;
    freeable_fml := cif_freeable;
    pc_fml := cif_pc;
    or_fml := cif_or;
    vo_fml := cif_vo;
    idxbor_fml := cif_idxbor;
    incl_fml := cif_incl;
    dead_fml := cif_dead;
    cmapstoany_fml := cif_cmapstoany;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. move=> ?. exact cif_pure_sem. Qed.
  Next Obligation. move=> *. exact cif_ex_sem. Qed.
  Next Obligation. move=> ?????. by apply cif_ex_ne. Qed.
  Next Obligation. move=> *. exact cif_exs_sem. Qed.
  Next Obligation. move=> ?????. by apply cif_exs_ne. Qed.
  Next Obligation. move=> ?. exact cif_alive_sem. Qed.
  Next Obligation. move=> *. exact cif_cells_sem. Qed.
  Next Obligation. move=> *. exact cif_ccells_sem. Qed.
  Next Obligation. move=> *. exact cif_freeable_sem. Qed.
  Next Obligation. move=> *. exact cif_pc_sem. Qed.
  Next Obligation. move=> *. exact cif_or_sem. Qed.
  Next Obligation. move=> *. exact cif_vo_sem. Qed.
  Next Obligation. move=> ?. exact cif_dead_sem. Qed.
  Next Obligation. move=> ?. exact cif_cmapstoany_sem. Qed.

  (** Guard sources *)
  #[export] Program Instance gsrcSem_cif : GsrcSem (cifOF CON) Σ :=
    {| gsrc_fml := cif_gsrc |}.
  Next Obligation. move=> ?. exact cif_gsrc_sem. Qed.

  (** The heap's cells *)
  Lemma cif_heap_sem {lc cells cv} :
    bor_sem (cif_heap lc cells cv : cifOF CON $oi Σ) ⊣⊢
      points_to_seq (FML:=cifOF CON) heap_name lc cells cv.
  Proof. by rewrite /bor_sem /= /cif_heap sem_cif_in. Qed.
  #[export] Program Instance heapSem_cif : HeapSem (cifOF CON) Σ :=
    {| heap_fml := cif_heap |}.
  Next Obligation. move=> *. exact cif_heap_sem. Qed.
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

(** ** The [AltSem] instance

  A *candidate* is an interpretation [⟦⟧ᶜ(δ)] for a good derivability
  predicate [δ].  Note what [alt_into] is defined as: in the model a
  candidate is a bare function, and nothing recovers the [δ] behind it, so
  [alt_into] cannot be [dinto δ δ'].  Both of its uses say "a guard stored
  at [sem] can be read at [sem']", which *is* a function of the two
  interpretations, so that is the definition - and [dinto δ δ'] discharges
  it. *)
Section altSem.
  Context `{!typingC CON} {JUDG Σ} `{!alerusGS (cifOF CON) Σ,
    !typingJ CON JUDG Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
    !typingCS CON JUDG Σ, !typingJS CON JUDG Σ}.
  Implicit Type S : Cand (cifOF CON) Σ.

  (** A candidate is an interpretation at a good derivability predicate *)
  Definition alt_sem_cif S : Prop :=
    ∃ δ : JUDG -n> iProp Σ, Deriv (λ _, True) δ ∧ cand_asem S = AlerusSem_at δ.
  (** An *interpretation*, good or not.  This is [alt_sem_cif] with the
    [Deriv] dropped, and it is what [st_iff] now quantifies over. *)
  Definition alt_any_cif S : Prop :=
    ∃ δ : JUDG -n> iProp Σ, cand_asem S = AlerusSem_at δ.
  Lemma alt_sem_any_cif {S} : alt_sem_cif S → alt_any_cif S.
  Proof. move=> [δ[_ ?]]. by exists δ. Qed.
  Lemma alt_any_cif_ne {S} : alt_any_cif S → NonExpansive S.
  Proof. move=> [δ Heq]. rewrite /cand_fun Heq. exact _. Qed.

  Local Instance stBor_alt : StBor (cifOF CON) Σ := stBor_cif (JUDG:=JUDG).
  Local Instance stBorSem_alt : StBorSem := stBorSem_at der der_Deriv.

  (** [alt_into] is defined by its three uses: in the model a candidate is a
    bare record and nothing recovers the [δ] behind it, but each use is a
    function of the two interpretations, and [dinto δ δ'] discharges all
    three. *)
  Definition alt_into_cif S S' : Prop :=
    (∀ Px Qx, S (cif_guard Px Qx) ⊢ S' Px &&{alt_WGuard S'}&&> S' Qx) ∧
    (∀ κ idx (Px : cif CON Σ),
      S (cif_idxbor κ idx Px) ⊢
        ∃ Px', □ (S' Px' ↔ S' Px) ∗ idx_bor κ idx Px') ∧
    (∀ κ κ', S (cif_incl κ κ') ⊢ S' (cif_incl κ κ')).

  (** The ambient interpretation is a candidate *)
  Lemma alt_sem_cif_here : alt_sem_cif alt_amb.
  Proof. exists der. split; [exact _|done]. Qed.


  (** *** The three judgments, unfolded *)

  Lemma guardJ_sem_at {δ} {Px Qx : cif CON Σ} :
    ⟦ guard_j Px Qx ⟧(δ) ⊣⊢
      (⟦ Px ⟧ᶜ(δ) &&{alerus_WGuard_at δ}&&> ⟦ Qx ⟧ᶜ(δ))%I.
  Proof. by rewrite in_js. Qed.

  (** A stored guard at the ambient interpretation is the guard *)
  Lemma guardJ_der {Px Qx : cif CON Σ} :
    □ der (guard_j Px Qx) ⊢
      ⟦ Px ⟧ᶜ(der) &&{alerus_WGuard_at der}&&> ⟦ Qx ⟧ᶜ(der).
  Proof.
    iIntros "#g". iDestruct (der_sound with "g") as "g'". by rewrite in_js.
  Qed.

  (** The two constant judgments, unfolded *)
  Lemma idxborJ_sem {δ κ idx} {Px : cif CON Σ} :
    ⟦ idxbor_j κ idx Px ⟧(δ) ⊣⊢ idx_bor κ idx Px.
  Proof. by rewrite in_js. Qed.
  Lemma inclJ_sem {δ κ κ'} : ⟦ incl_j κ κ' ⟧(δ) ⊣⊢ st_incl κ κ'.
  Proof. by rewrite in_js. Qed.

  Lemma cif_idxbor_sem {δ κ idx} {Px : cif CON Σ} :
    ⟦ cif_idxbor κ idx Px ⟧ᶜ(δ) ⊣⊢
      ∃ Px', □ δ (iff_j Px' Px) ∗ □ δ (idxbor_j κ idx Px').
  Proof. by rewrite /cif_idxbor sem_cif_in. Qed.

  (** The alteration judgment, unfolded *)
  Lemma iffJ_sem {δ} {Px Qx : cif CON Σ} :
    ⟦ iff_j Px Qx ⟧(δ) ⊣⊢ □ (⟦ Px ⟧ᶜ(δ) ↔ ⟦ Qx ⟧ᶜ(δ)).
  Proof. by rewrite in_js. Qed.
  Lemma cif_incl_sem {δ κ κ'} :
    ⟦ cif_incl κ κ' : cif CON Σ ⟧ᶜ(δ) ⊣⊢ □ δ (incl_j κ κ').
  Proof. by rewrite /cif_incl sem_cif_in. Qed.

  (** Since the two semantics are constant, storing one at a good [δ] is
    [Deriv_factor'] with nothing left to prove, and reading one at the
    ambient interpretation is [der_sound]. *)
  Lemma idxborJ_of {δ} `{!Deriv (λ _, True) δ} {κ idx} {Px : cif CON Σ} :
    idx_bor κ idx Px ⊢ δ (idxbor_j κ idx Px).
  Proof. iIntros "b". iApply Deriv_factor'. iIntros (δ' ? _ _). by rewrite in_js. Qed.
  Lemma inclJ_of {δ} `{!Deriv (λ _, True) δ} {κ κ'} :
    st_incl κ κ' ⊢ δ (incl_j κ κ').
  Proof. iIntros "b". iApply Deriv_factor'. iIntros (δ' ? _ _). by rewrite in_js. Qed.
  Lemma idxborJ_der {κ idx} {Px : cif CON Σ} :
    □ der (idxbor_j κ idx Px) ⊣⊢ idx_bor κ idx Px.
  Proof.
    destruct idx as [sn κ']. iSplit.
    - iIntros "#g". iDestruct (der_sound with "g") as "g'". by rewrite in_js.
    - iIntros "#b !>". by iApply idxborJ_of.
  Qed.
  Lemma inclJ_der {κ κ'} : □ der (incl_j κ κ') ⊣⊢ st_incl κ κ'.
  Proof.
    iSplit.
    - iIntros "#g". iDestruct (der_sound with "g") as "g'". by rewrite in_js.
    - iIntros "#b !>". by iApply inclJ_of.
  Qed.

  Lemma alt_into_cif_here : alt_into_cif alt_amb alt_amb.
  Proof.
    split; [|split]; [| |done].
    - move=> Px Qx. rewrite /cand_fun /= /cif_guard sem_cif_in /=.
      exact guardJ_der.
    - move=> κ idx Px. rewrite /cand_fun /= cif_idxbor_sem.
      iIntros "(%Px' & #i & #b)". iExists Px'. iSplitR.
      + iDestruct (der_sound with "i") as "i'". by rewrite in_js.
      + rewrite -idxborJ_der. iApply "b".
  Qed.


  (** Replace a candidate by the derivability predicate behind it *)
  Local Ltac alt_at H :=
    let d := fresh "δ" in let Hd := fresh "Hδ" in let Heq := fresh "Heq" in
    destruct H as (d & Hd & Heq); rewrite /cand_fun /alt_WGuard /= ?Heq.
  Local Tactic Notation "alt_any_at" hyp(H) :=
    destruct H as (dd & Heqq); rewrite /cand_fun /alt_WGuard /= ?Heqq.

  (** *** The non-judgment constructors mean the same at every candidate *)
  Lemma sep_sem_cif {S} (H : alt_any_cif S) Px Qx :
    S (cif_sep Px Qx) ⊣⊢ S Px ∗ S Qx.
  Proof. alt_any_at H. exact cif_sem_sep. Qed.
  Lemma false_sem_cif {S} (H : alt_any_cif S) :
    S (cif_pure False : cifOF CON $oi Σ) ⊣⊢ False.
  Proof. alt_any_at H. done. Qed.
  Lemma empty_sem_cif {S} (H : alt_any_cif S) :
    S (cif_pure True : cifOF CON $oi Σ) ⊣⊢ True.
  Proof. alt_any_at H. done. Qed.
  Lemma pure_sem_cif {S} (H : alt_any_cif S) φ :
    S (cif_pure φ : cifOF CON $oi Σ) ⊣⊢ ⌜φ⌝.
  Proof. alt_any_at H. done. Qed.
  Lemma ex_sem_cif {S} (H : alt_any_cif S) A (Φ : A → cifOF CON $oi Σ) :
    S (cif_ex Φ) ⊣⊢ ∃ a, S (Φ a).
  Proof. alt_any_at H. done. Qed.
  Lemma exs_sem_cif {S} (H : alt_any_cif S) 𝔄 (Φ : (~~𝔄) → cifOF CON $oi Σ) :
    S (cif_exs Φ) ⊣⊢ ∃ a : ~~𝔄, S (Φ a).
  Proof. alt_any_at H. exact cif_exs_sem_at. Qed.
  Lemma or_sem_cif {S} (H : alt_any_cif S) Px Qx :
    S (cif_or Px Qx) ⊣⊢ S Px ∨ S Qx.
  Proof. alt_any_at H. done. Qed.
  Lemma alive_sem_cif {S} (H : alt_any_cif S) κ : S (cif_alive κ) ⊣⊢ @[κ].
  Proof. alt_any_at H. exact cif_alive_sem_at. Qed.
  Lemma dead_sem_cif {S} (H : alt_any_cif S) κ : S (cif_dead κ) ⊣⊢ [†κ].
  Proof. alt_any_at H. exact cif_dead_sem_at. Qed.
  Lemma cells_sem_cif {S} (H : alt_any_cif S) l cs fv :
    S (cif_cells l cs fv) ⊣⊢ l ↦[^ cs ]!∗ fv.
  Proof. alt_any_at H. exact cif_cells_sem_at. Qed.
  Lemma ccells_sem_cif {S} (H : alt_any_cif S) l fv :
    S (cif_ccells l fv) ⊣⊢ l #↦!∗ fv.
  Proof. alt_any_at H. exact cif_ccells_sem_at. Qed.
  Lemma cmapstoany_sem_cif {S} (H : alt_any_cif S) l :
    S (cif_cmapstoany l) ⊣⊢ l #↦∗_.
  Proof. alt_any_at H. exact cif_cmapstoany_sem_at. Qed.
  Lemma freeable_sem_cif {S} (H : alt_any_cif S) n sz l :
    S (cif_freeable n sz l) ⊣⊢ freeable_sz n sz l.
  Proof. alt_any_at H. exact cif_freeable_sem_at. Qed.
  Lemma vo_sem_cif {S} (H : alt_any_cif S) ξ x d :
    S (cif_vo ξ x d) ⊣⊢ .VO[ξ] x d.
  Proof. alt_any_at H. exact cif_vo_sem_at. Qed.
  Lemma pc_sem_cif {S} (H : alt_any_cif S) ξ x vπ d :
    S (cif_pc ξ x vπ d) ⊣⊢ .PC[ξ] x vπ d.
  Proof. alt_any_at H. exact cif_pc_sem_at. Qed.
  Lemma cellsvec_sem_cif {S} (H : alt_sem_cif S) cs fv :
    S (cif_cellsvec cs fv) ⊣⊢ cs ^↦!∗ fv.
  Proof. alt_at H. exact cif_cellsvec_sem_at. Qed.
  Lemma gsrc_sem_cif {S} (H : alt_any_cif S) s :
    S (cif_gsrc s) ⊣⊢ gsrc_interp s.
  Proof. alt_any_at H. exact cif_gsrc_sem_at. Qed.
  Lemma bor_state_sem_cif {S} (H : alt_any_cif S) sn bs :
    S (cif_bor_state sn bs) ⊣⊢ bor_sem (cif_bor_state sn bs).
  Proof. alt_any_at H. rewrite /bor_sem /= !cif_bor_state_sem //. Qed.

  (** *** Storing a guard: [Deriv_factor'] at the candidate

    The obligation it leaves is the guard at every candidate [δ'] the
    candidate maps into, and the [dinto] it hands out is exactly
    [alt_into]. *)
  (** [dinto] between two good interpretations is [alt_into] between the
    candidates they are.  The guard clause is [in_js]; the borrow clause
    moves the alteration and the token judgment across and reads the first;
    the inclusion clause re-stores, its semantics being interpretation-free. *)
  Lemma alt_into_cif_of_dinto {S S' : Cand (cifOF CON) Σ} {δ δ'}
    (Hδ : Deriv (λ _, True) δ) (Hδ' : Deriv (λ _, True) δ')
    (HS : cand_asem S = AlerusSem_at δ) (HS' : cand_asem S' = AlerusSem_at δ')
    (Hinto : dinto δ δ') : alt_into_cif S S'.
  Proof.
    have ? : Deriv (λ _, True) δ' := Hδ'. split; [|split].
    - move=> Px' Qx'. rewrite /cand_fun /alt_WGuard /= HS HS' /=
        /cif_guard sem_cif_in /=.
      iIntros "#g". rewrite (Hinto (guard_j Px' Qx')) in_js //.
    - move=> κ idx Px'. rewrite /cand_fun /= HS HS' /= cif_idxbor_sem.
      iIntros "(%Px'' & #i & #b)". iExists Px''.
      rewrite (Hinto (iff_j Px'' Px')) (Hinto (idxbor_j κ idx Px''))
        !in_js /=. by iFrame "i b".
    - move=> κ κ'. rewrite /cand_fun /= HS HS' /= !cif_incl_sem.
      iIntros "#g !>". rewrite (Hinto (incl_j κ κ')) in_js.
      by iApply inclJ_of.
  Qed.

  Lemma guard_fml_sem_2_cif {S} (H : alt_sem_cif S) Px Qx :
    (∀ S', ⌜alt_sem_cif S'⌝ → ⌜alt_into_cif S S'⌝ →
      S' Px &&{alt_WGuard S'}&&> S' Qx) ⊢ S (cif_guard Px Qx).
  Proof.
    move: (H)=> [δ[Hδ Heq]]. have ? : Deriv (λ _, True) δ := Hδ.
    rewrite /cand_fun /= Heq /= /cif_guard sem_cif_in /=.
    iIntros "#big !>". iApply Deriv_factor'. iIntros (δ' Hδ' _ Hinto).
    rewrite in_js /=.
    iApply ("big" $! (MkCand (AlerusSem_at δ')) with "[%] [%]").
    { by exists δ'. }
    { eapply alt_into_cif_of_dinto;
        [exact Hδ|exact Hδ'|exact Heq|done|exact Hinto]. }
  Qed.

  (** *** Persistence *)
  Lemma guard_fml_pers_cif {S} (H : alt_any_cif S) Px Qx :
    Persistent (S (cif_guard Px Qx)).
  Proof.
    move: H=> [δ Heq].
    rewrite /cand_fun /= Heq /= /cif_guard sem_cif_in /=. exact _.
  Qed.
  Lemma idxbor_fml_pers_cif {S} (H : alt_any_cif S) κ idx Px :
    Persistent (S (cif_idxbor κ idx Px)).
  Proof.
    move: H=> [δ Heq]. rewrite /cand_fun /= Heq /= cif_idxbor_sem.
    exact _.
  Qed.

  (** *** The indexed borrow *)
  Lemma incl_fml_pers_cif {S} (H : alt_any_cif S) κ κ' :
    Persistent (S (cif_incl κ κ')).
  Proof.
    move: H=> [δ Heq]. rewrite /cand_fun /= Heq /= cif_incl_sem. exact _.
  Qed.

  (** *** The indexed borrow *)
  (** The alteration a stored borrow carries: the judgment itself, at the
    ambient interpretation, so that it can be read *and* re-stored. *)
  Definition dalter_cif (Px Qx : cif CON Σ) : iProp Σ :=
    □ der (iff_j Px Qx).
  #[export] Instance dalter_cif_persistent {Px Qx} :
    Persistent (dalter_cif Px Qx) := _.
  Lemma dalter_cif_refl {Px} : ⊢ dalter_cif Px Px.
  Proof.
    iIntros "!>". iApply Deriv_factor'. iIntros (δ' ? _ _).
    rewrite iffJ_sem. iIntros "!>". iSplit; by iIntros "$".
  Qed.
  Lemma dalter_cif_trans {Px Qx Rx} :
    dalter_cif Px Qx -∗ dalter_cif Qx Rx -∗ dalter_cif Px Rx.
  Proof.
    iIntros "#i #i' !>". iApply (Deriv_map2 with "[] i i'").
    iIntros (δ' ? _ _). rewrite !iffJ_sem. iIntros "#a #b !>".
    iSplit; iIntros "P"; [iApply "b"; by iApply "a"|iApply "a"; by iApply "b"].
  Qed.
  Lemma dalter_cif_sem {Px Qx} :
    dalter_cif Px Qx ⊢ □ (bor_sem Px ↔ bor_sem Qx).
  Proof.
    iIntros "#i". iDestruct (der_sound with "i") as "i'". by rewrite iffJ_sem.
  Qed.

  Lemma dalter_of_into_cif {Px Qx : cif CON Σ} :
    □ (∀ S, ⌜alt_sem_cif S⌝ → ⌜alt_into_cif alt_amb S⌝ → S Px ∗-∗ S Qx) ⊢
      dalter_cif Px Qx.
  Proof.
    iIntros "#eq !>". iApply Deriv_factor'. iIntros (δ' Hδ' _ Hinto).
    rewrite iffJ_sem.
    iDestruct ("eq" $! (MkCand (AlerusSem_at δ')) with "[%] [%]") as "[F B]".
    { by exists δ'. }
    { eapply alt_into_cif_of_dinto;
        [exact der_Deriv|exact Hδ'|done|done|exact Hinto]. }
    iIntros "!>". iSplit; iIntros "P"; by [iApply "F"|iApply "B"].
  Qed.

  (** *** The indexed borrow *)
  Lemma idxbor_fml_sem_1_cif {κ idx} {Px : cif CON Σ} :
    bor_sem (cif_idxbor κ idx Px) ⊢
      ∃ Px', dalter_cif Px' Px ∗ idx_bor κ idx Px'.
  Proof.
    rewrite /bor_sem /= cif_idxbor_sem. iIntros "(%Px' & #i & #b)".
    iExists Px'. iFrame "i". rewrite -idxborJ_der. iApply "b".
  Qed.
  Lemma idxbor_fml_alter_cif {κ idx} {Px Qx : cif CON Σ} :
    dalter_cif Px Qx -∗
    bor_sem (cif_idxbor κ idx Px) -∗ bor_sem (cif_idxbor κ idx Qx).
  Proof.
    rewrite /bor_sem /= !cif_idxbor_sem.
    iIntros "#i (%Px' & #i' & #b)". iExists Px'. iFrame "b".
    iApply (dalter_cif_trans with "i' i").
  Qed.
  Lemma idxbor_fml_iff_at_cif {S} (H : alt_sem_cif S) κ idx
    (Px Qx : cif CON Σ) :
    □ (∀ S' (_ : alt_sem_cif S') (_ : alt_into_cif S S'), S' Px ∗-∗ S' Qx) -∗
    S (cif_idxbor κ idx Px) -∗ S (cif_idxbor κ idx Qx).
  Proof.
    move: (H)=> [δ[Hδ Heq]]. have ? : Deriv (λ _, True) δ := Hδ.
    rewrite /cand_fun /= Heq /= !cif_idxbor_sem.
    iIntros "#eq (%Px' & #i & #b)". iExists Px'. iFrame "b". iModIntro.
    iApply (Deriv_map with "[] i"). iIntros (δ' Hδ' _ Hinto).
    rewrite !iffJ_sem. iIntros "#a !>".
    iDestruct ("eq" $! (MkCand (AlerusSem_at δ')) with "[%] [%]")
      as "[F B]"; [by exists δ'| |].
    { eapply alt_into_cif_of_dinto;
        [exact Hδ|exact Hδ'|exact Heq|done|exact Hinto]. }
    iSplit; iIntros "P".
    - iApply "F". by iApply "a".
    - iApply "a". by iApply "B".
  Qed.

  Lemma idxbor_fml_of_bor_cif {κ} {Px : cif CON Σ} :
    full_bor κ Px ⊢ ∃ idx, bor_sem (cif_idxbor κ idx Px) ∗ idx_bor_tok idx.
  Proof.
    rewrite (llftl_bor_idx (FML:=cifOF CON)).
    iIntros "(%idx & #b & tok)". iExists idx. iFrame "tok".
    rewrite /bor_sem /= cif_idxbor_sem. iExists Px.
    iSplitR; [iApply dalter_cif_refl|]. by rewrite idxborJ_der.
  Qed.
  (** *** The stored inclusion *)
  Lemma incl_fml_sem_1_cif {κ κ'} :
    bor_sem (cif_incl κ κ') ⊢ st_incl κ κ'.
  Proof. rewrite /bor_sem /= cif_incl_sem inclJ_der //. Qed.
  Lemma incl_fml_of_incl_cif {S} (H : alt_sem_cif S) κ κ' :
    st_incl κ κ' ⊢ S (cif_incl κ κ').
  Proof.
    move: H=> [δ[Hδ Heq]]. have ? : Deriv (λ _, True) δ := Hδ.
    rewrite /cand_fun /= Heq /= cif_incl_sem.
    iIntros "#b !>". by iApply inclJ_of.
  Qed.
  Lemma incl_fml_into_cif {S S'} (H : alt_sem_cif S) (H' : alt_sem_cif S')
    (Hi : alt_into_cif S S') κ κ' :
    S (cif_incl κ κ') ⊢ S' (cif_incl κ κ').
  Proof. apply Hi. Qed.
  Lemma incl_fml_mono_at_cif {S} (H : alt_sem_cif S) κ0 κ κ' κ1 :
    st_incl κ0 κ -∗ st_incl κ' κ1 -∗
    S (cif_incl κ κ') -∗ S (cif_incl κ0 κ1).
  Proof.
    move: (H)=> [δ[Hδ Heq]]. have ? : Deriv (λ _, True) δ := Hδ.
    rewrite /cand_fun /= Heq /= !cif_incl_sem.
    iIntros "#l #r #g !>". iApply (Deriv_map with "[] g").
    iIntros (δ' ? _ _). rewrite !inclJ_sem. iIntros "m".
    iApply (st_incl_trans with "[] [m]"); [iApply "l"|].
    iApply (st_incl_trans with "m []"). iApply "r".
  Qed.
  (** *** The lifetime logic at a candidate *)
  (** An indexed borrow stored at the *ambient* interpretation, opened at a
    candidate the ambient one maps into.  Reading it at the candidate itself
    would need soundness of that candidate, which only [der] has; going
    through [dinto] does not. *)
  Lemma idxbor_fml_guard_into_cif {S'} (H' : alt_sem_cif S')
    (Hi : alt_into_cif alt_amb S') κ idx
    (Px : cif CON Σ) (G : iProp Σ) :
    bor_sem (cif_idxbor κ idx Px) -∗
    (G &&{alt_WGuard S'}&&> @[κ]) -∗
    (G &&{alt_WGuard S'}&&> idx_bor_tok idx) -∗
    G &&{alt_WGuard S'}&&> (@[κ] ∗ S' Px).
  Proof.
    move: (H')=> [δ'[Hδ' Heq']]. iIntros "B #Gk #Gt".
    iDestruct (proj1 (proj2 Hi) κ idx Px with "B") as "(%Px' & #iff & #b)".
    iAssert (G &&{alt_WGuard S'}&&> (@[κ] ∗ S' Px'))%I as "#G'".
    { rewrite /alt_WGuard /cand_fun /= Heq' /=.
      iApply (idxbor_guard_at δ' Hδ' with "b Gk Gt"). }
    iApply (guard_trans with "G'"). iApply guard_intro.
    iIntros "!> [$ P]". iDestruct ("iff" with "P") as "$".
    iIntros "[$ Q]". by iApply "iff".
  Qed.

  Lemma idxbor_fml_shorten_at_cif {S} (H : alt_sem_cif S) κ κ' idx
    (Px : cif CON Σ) :
    st_incl κ' κ -∗ S (cif_idxbor κ idx Px) -∗ S (cif_idxbor κ' idx Px).
  Proof.
    move: (H)=> [δ[Hδ Heq]]. have ? : Deriv (λ _, True) δ := Hδ.
    rewrite /cand_fun /= Heq /= !cif_idxbor_sem.
    iIntros "#i (%Px' & #iff & #g)". iExists Px'. iFrame "iff". iModIntro.
    iApply (Deriv_map with "[] g"). iIntros (δ' ? _ _). rewrite !idxborJ_sem.
    iApply (llftl_idx_shorten (FML:=cifOF CON) κ κ' idx Px' with "i").
  Qed.
  Lemma Ltok_guard_frac_at_cif {S} (H : alt_sem_cif S) γ L q :
    frac_key_tok γ L ⊢ frac_tok γ q &&{alt_WGuard S}&&> llctx_interp L.
  Proof.
    move: H=> [δ[Hδ Heq]]. rewrite /alt_WGuard /= Heq.
    exact (Ltok_guard_frac_at' δ).
  Qed.

  (** *** Allocating a shared borrow.  The [sinv_tok] it allocates mentions
    no interpretation, so the guard it yields holds at every candidate - this
    is one of the two places where a guard can be stored. *)
  Lemma guard_fml_borrow_shared_cif {κ} {Px : cif CON Σ} :
    bor_sem Px -∗ |=[alerus_WGuard]=>
      (□ ∀ S (_ : alt_sem_cif S), @[κ] &&{alt_WGuard S}&&> S Px) ∗
      ([†κ] -∗ |=[alerus_WGuard]=> bor_sem Px).
  Proof.
    iIntros "P W".
    iMod (llftl_borrow_shared_tok (FML:=cifOF CON) κ Px with "P W")
      as "[$ (%γc & %sn & #tok & $)]".
    iIntros "!> !>" (S HS). move: HS=> [δ[Hδ Heq]].
    rewrite /alt_WGuard /cand_fun /= Heq /=.
    iApply (shr_tok_guard_at δ). iApply "tok".
  Qed.

  Lemma st_incl_of_sub_cif {κ κ'} : κ' ⊆ κ → ⊢ st_incl κ κ'.
  Proof. exact: st_incl_cif_of_sub. Qed.

  (** Eternalizing a lifetime.  The [eternal_tok] it allocates mentions no
    interpretation, so the inclusion it yields holds at every candidate. *)
  Lemma st_incl_eternalize_cif {κ} : @[κ] =[alerus_wsat]=∗ st_incl static κ.
  Proof.
    iIntros "K W".
    rewrite (wsat_incl alerus_wsat
      (eternal_wsat alerus_eternal_name llft_alive) _).
    iDestruct "W" as "[We Wr]".
    iMod (eternal_tok_alloc with "K We") as "[#tok We]". iModIntro.
    iSplitL "We Wr"; [by iFrame|].
    iApply (st_incl_cif_eternalize with "tok").
  Qed.

  (** *** A full borrow, stored as a guard

    Sharing the borrow's *token* with [llftl_borrow_shared_tok] gives a guard
    to the token at every candidate; composing it with the indexed borrow's
    own guard gives [@[κ] &&{W}&&> Px] there, which is what storing asks
    for.  This is the second place where a guard can be stored. *)
  Lemma guard_fml_of_bor_cif {κ} {Px : cif CON Σ} :
    llft_ctx -∗ full_bor κ Px =[alerus_wsat]=∗
      bor_sem (cif_guard (cif_alive κ) Px).
  Proof.
    iIntros "_ B W". rewrite (llftl_bor_idx (FML:=cifOF CON)).
    iDestruct "B" as (idx) "[#b tok]".
    rewrite (wsat_incl alerus_wsat alerus_WGuard _).
    iDestruct "W" as "[Wg Wr]".
    iMod (llftl_borrow_shared_tok (FML:=cifOF CON) κ
      (cif_bor_state idx.1
        (ra.Borrow (set_map ra.LtAtomSwell idx.2) {[ra.default_dead]}))
      with "[tok] Wg") as "[Wg (%γc & %sn2 & #stok & _)]".
    { rewrite /bor_sem /= cif_bor_state_sem -idx_bor_tok_unfold. iFrame "tok". }
    iModIntro. iSplitL "Wg Wr"; [by iFrame|].
    rewrite /bor_sem /= /cif_guard sem_cif_in /=.
    iIntros "!>". iApply Deriv_factor'. iIntros (δ' Hδ' _ _).
    rewrite guardJ_sem_at cif_alive_sem_at.
    iDestruct (shr_tok_guard_at δ' with "stok") as "#Gtok0".
    iDestruct (guard_rhs_iff cif_bor_state_sem with "Gtok0") as "#Gtok0'".
    rewrite -idx_bor_tok_unfold.
    iDestruct "Gtok0'" as "#Gtok".
    iDestruct (idxbor_guard_at δ' Hδ' with "b [] Gtok") as "#G";
      [iApply guard_refl|].
    by iApply (guard_rhs_sep_r with "G").
  Qed.

  Lemma st_incl_at_cif {S} (H : alt_sem_cif S) κ κ' :
    st_incl κ κ' ⊢ @[κ] &&{alt_WGuard S}&&> @[κ'].
  Proof.
    move: H=> [δ[Hδ Heq]]. rewrite /alt_WGuard /= Heq.
    exact (st_incl_cif_at δ).
  Qed.

  (** ** The [AltSem] instance *)
  #[export] Instance altSem_cif : AltSem (cifOF CON) Σ := {|
    alt_sem := alt_sem_cif;
    alt_into := alt_into_cif;
    alt_any := alt_any_cif;
    alt_sem_any := @alt_sem_any_cif;
    alt_any_ne := @alt_any_cif_ne;
    alt_here := alt_sem_cif_here;
    alt_into_here := alt_into_cif_here;
    sep_sem_at_any := @sep_sem_cif;
    false_sem_at_any := @false_sem_cif;
    empty_sem_at_any := @empty_sem_cif;
    pure_sem_at_any := @pure_sem_cif;
    ex_sem_at_any := @ex_sem_cif;
    exs_sem_at_any := @exs_sem_cif;
    or_sem_at_any := @or_sem_cif;
    alive_sem_at_any := @alive_sem_cif;
    dead_sem_at_any := @dead_sem_cif;
    cells_sem_at_any := @cells_sem_cif;
    ccells_sem_at_any := @ccells_sem_cif;
    cmapstoany_sem_at_any := @cmapstoany_sem_cif;
    freeable_sem_at_any := @freeable_sem_cif;
    vo_sem_at_any := @vo_sem_cif;
    pc_sem_at_any := @pc_sem_cif;
    gsrc_sem_at_any := @gsrc_sem_cif;
    guard_fml_sem_into := (λ _ _ _ _ Hi, proj1 Hi);
    guard_fml_sem_2 := @guard_fml_sem_2_cif;
    guard_fml_pers_at_any := @guard_fml_pers_cif;
    idxbor_fml_pers_at_any := @idxbor_fml_pers_cif;
    dalter := dalter_cif;
    dalter_persistent := (λ _ _, _);
    dalter_refl := @dalter_cif_refl;
    dalter_trans := @dalter_cif_trans;
    dalter_sem := @dalter_cif_sem;
    dalter_of_into := @dalter_of_into_cif;
    idxbor_fml_sem_1 := @idxbor_fml_sem_1_cif;
    idxbor_fml_alter := @idxbor_fml_alter_cif;
    idxbor_fml_of_bor := @idxbor_fml_of_bor_cif;
    idxbor_fml_iff_at := @idxbor_fml_iff_at_cif;
    bor_state_sem_at_any := @bor_state_sem_cif;
    idxbor_fml_guard_into := @idxbor_fml_guard_into_cif;
    idxbor_fml_shorten_at := @idxbor_fml_shorten_at_cif;
    incl_fml_sem_1 := @incl_fml_sem_1_cif;
    incl_fml_of_incl := @incl_fml_of_incl_cif;
    incl_fml_pers_at_any := @incl_fml_pers_cif;
    incl_fml_mono_at := @incl_fml_mono_at_cif;
    st_incl_of_sub := @st_incl_of_sub_cif;
    st_incl_at := @st_incl_at_cif;
    st_incl_eternalize := @st_incl_eternalize_cif;
    Ltok_guard_frac_at := @Ltok_guard_frac_at_cif;
    guard_fml_borrow_shared := @guard_fml_borrow_shared_cif;
    guard_fml_of_bor := @guard_fml_of_bor_cif;
  |}.
End altSem.

