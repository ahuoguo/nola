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
From nola.iris Require Export cif.
From nola.alerus.typing Require Export ctx.
From nola.alerus Require Import na_inv_fork.
From nola.alerus.util Require Import cancellable_na_invariants
  atomic_lock_counter.
Import iPropAppNotation ModwNotation CsemNotation.

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
| (** The atomic lock counter's handle *) as_handle (c : coPset).

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
    end%I.
  #[export] Program Instance alerusCT_ecsem {JUDG}
    : Ecsem alerusCT CON JUDG Σ :=
    ECSEM (λ _ _ s _ _ _, alerusCT_sem s) _.
  Next Obligation. done. Qed.
End alerusC.

(** [alerusC] semantics registered *)
Notation alerusCS := (inCS alerusCT).
