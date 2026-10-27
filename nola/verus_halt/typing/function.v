(** * Function types

  Ported from VerusBelt ([typing/function.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.

  Two things change.

  - [fn]'s [pt_gho] drops the [▷] in front of the function's specification.
    It exists so that the specification can be unfolded one step at a time;
    later-free there is nothing to unfold through, and [fn_ne] - which is the
    only client of that [▷] - is already commented out upstream.

  - [type_fnrec] is **not** ported.  Its proof is an [iLöb] that ties the
    function's own specification back into its body, and Löb induction is
    unavailable for a total weakest precondition.  A recursive function is a
    loop and needs a decreasing measure, which this judgment does not carry
    (VerusBelt does not model Verus's [decreases] clauses either).
    [type_fn], the non-recursive rule, is proved directly instead of being
    derived from [type_fnrec]. *)

Import EqNotations.
From iris.proofmode Require Import proofmode.
From nola.verus_halt.typing Require Import own programs cont.
From nola.verus_halt.typing Require Export type ctx.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation WpwNotation.
Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Fixpoint subst_plv {𝔄l} (bl: plistc binder 𝔄l) (vl: plistc val 𝔄l) (e: expr) : expr :=
  match 𝔄l, bl, vl with
  | [], _, _ => e
  | _::_, b -:: bl', v -:: vl' => subst' b v (subst_plv bl' vl' e)
  end.

Global Instance do_subst_plv {𝔄l} (bl vl: plistc _ 𝔄l) e :
  DoSubstL bl (map of_val vl) e (subst_plv bl vl e).
Proof.
  rewrite /DoSubstL. induction 𝔄l, bl, vl; [done|]=>/=. by rewrite IH𝔄l.
Qed.

Lemma subst_plv_renew {𝔄l 𝔅l} (bl: plistc binder 𝔄l) (vl': plistc val 𝔅l) eq eq' e :
  subst_plv (plistc_renew eq bl) vl' e =
    subst_plv bl (plistc_renew eq' vl') e.
Proof.
  move: 𝔄l 𝔅l bl vl' eq eq'. fix FIX 1.
  case=> [|??]; case=>//= ??[??][??]??. f_equal. apply FIX.
Qed.

Definition boxl (𝔄l: syn_typel) : syn_typel := (fmap at_locₛ 𝔄l).
Notation fn_spec 𝔄l 𝔅 ℭ := ((~~ℭ) → predl_trans' (boxl 𝔄l) (at_locₛ 𝔅)).

Section fn.
  Context `{!typeG FML Σ} {A: Type} {𝔄l 𝔅}.

  Record fn_params :=
    FP {
      fp_E_ex: lft → elctx;
      fp_ityl: typel 𝔄l;
      fp_oty: type 𝔅;
      fp_atomic_state: invctx_atomic_state
    }.

  Definition fn_params_dist n fp fp' : Prop :=
    (∀ϝ, fp.(fp_E_ex) ϝ = fp'.(fp_E_ex) ϝ) ∧
    fp.(fp_ityl) ≡{n}≡ fp'.(fp_ityl) ∧ fp.(fp_oty) ≡{n}≡ fp'.(fp_oty).

  Definition fp_E (fp: fn_params) ϝ : elctx :=
    fp.(fp_E_ex) ϝ ++ tyl_E fp.(fp_ityl) ++ tyl_outlives_E fp.(fp_ityl) ϝ ++
    fp.(fp_oty).(ty_E) ++ ty_outlives_E fp.(fp_oty) ϝ.

  Global Instance fp_E_ne n : Proper (fn_params_dist n ==> (=) ==> (=)) fp_E.
  Proof.
    rewrite /fp_E. move=> ?? Eq ??->. move: Eq=> [->[Eqi Eqo]].
    f_equiv. do 2 (f_equiv; [by rewrite Eqi|]). by rewrite Eqo.
  Qed.

  Lemma elctx_sat_fp_E (fp: fn_params) ϝ ϝ' L :
    fp_E_ex fp = const [] →
    elctx_sat (ϝ' ⊑ₑ ϝ :: fp_E fp ϝ) L (fp_E fp ϝ').
  Proof.
    move=> Eq. rewrite /fp_E Eq /=. apply elctx_sat_app; [solve_typing|].
    apply elctx_sat_app. { apply (tyl_outlives_E_elctx_sat_mono ϝ'); solve_typing. }
    apply elctx_sat_app; [solve_typing|].
    apply (ty_outlives_E_elctx_sat_mono ϝ'); solve_typing.
  Qed.

  Definition tr_ret {𝔄} : predl_trans' [𝔄] (𝔄) := λ post '-[a], λ mask π, post a mask π.
  
  Fixpoint box_typel {𝔅l} (tyl: typel 𝔅l) : (typel (boxl 𝔅l)) :=
    match tyl in hlist _ l return typel (boxl l) with
      | +[] => +[]
      | (ty +:: tyl') => (own.box ty +:: box_typel tyl')
    end.
  
  Notation boxed_predl 𝔄l := (pred' (plist (indep_interp_of_syn_type ∘ at_locₛ) 𝔄l)).
  Notation boxed_predl_trans' 𝔄l 𝔅 := (pred' (~~𝔅) → boxed_predl 𝔄l).
  
End fn.

(** ** The body of a function type's specification

  Named once, because it is what [FnFml] below is *about*: its one
  obligation is that [fn_fml]'s semantics be this, at every candidate.
  [Wlv j] is the thesis's [∗_{k<j} Winv_k], supplied by the client. *)
Definition fn_body `{!typeG FML Σ} {A : Type} {𝔄l 𝔅 ℭ}
    (Wlv : nat → iProp Σ) (j : nat)
    (fp : A → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
    (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)) : iProp Σ :=
  (∃fb kb (bl: plistc _ _) e H, ⌜fst x = @RecV fb (kb :: bl) e H⌝ ∗
    □ ∀y ϝ k (wl: plistc _ _),
      typed_body_at (Wlv j) (fp_E (fp y) ϝ) [ϝ ⊑ₗ []]
        (InvCtx [] ϝ (fp_atomic_state (fp y)))
        [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp y))),
          λ v: vec _ 1, +[vhd v ◁ own.box (fp y).(fp_oty)] } tr_ret]
        (hzip_with (λ _ boxty (w: val), w ◁ boxty)
          (box_typel (fp y).(fp_ityl)) wl)
        (subst' fb (RecV fb (kb :: bl) e) $ subst' kb k $ subst_plv bl wl e)
        (spec (snd x)))%I.

#[export] Instance fn_body_persistent `{!typeG FML Σ} {A 𝔄l 𝔅 ℭ}
  {Wlv j} {fp : A → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅)} {spec x} :
  Persistent (fn_body (ℭ:=ℭ) Wlv j fp spec x).
Proof. rewrite /fn_body. exact _. Qed.

(** Cutting the parameter range down: the body quantifies over [A], and
  pre-composing with [σ] is instantiating that quantifier. *)
Lemma fn_body_specialize `{!typeG FML Σ} {A B 𝔄l 𝔅 ℭ} (σ : A → B)
    {Wlv j} {fp : B → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅)} {spec x} :
  fn_body (ℭ:=ℭ) Wlv j fp spec x ⊢ fn_body Wlv j (fp ∘ σ) spec x.
Proof.
  rewrite /fn_body. iIntros "(%fb & %kb & %bl & %e & %H & %Hrec & #body)".
  iExists fb, kb, bl, e, H. iSplit; [done|]. iIntros "!>" (y ϝ k wl).
  iApply ("body" $! (σ y)).
Qed.

(** The formula standing for a function type's specification.

  A type's ghost assertion is a formula now (see [TypeFml] in
  [typing/ctx.v]), and [fn]'s is the whole typing judgment of the function's
  body - a [□ ∀ … typed_body …], which mentions the weakest precondition and
  therefore the world satisfaction that interprets formulas.  Expressing it
  needs a formula language closed under exactly that, i.e. a genuinely
  guarded-recursive domain equation; Nola's [cif] provides one for its own
  constructors, which is why [rust_halt] has no function type to begin with.
  It is stated here the way every other constructor in this development is -
  a constructor plus the equation pinning down its semantics - and it is the
  one whose realisability is *not* justified by the shapes already in
  [TypeFml].  See the note on [typing/soundness.v]. *)
Class FnFml `{!typeG FML Σ} := {
  (** The world satisfaction of a body at execution level [j]: the
    thesis's [∗_{k<j} Winv_k].  A parameter, because which levels exist
    is [typing/level_ctx.v]'s business - it supplies
    [verus_halt_wsat_below … j ∗ send_wsat]. *)
  fn_wsat_lv : nat → iProp Σ;
  (** The execution level the *ambient* world satisfaction is.  A
    typing derivation runs at one level, and that level bounds the
    arrow of every function type it may call. *)
  fn_lv_top : nat;
  (** **** The ambient world is the top of the family

    This is where the whole construction meets the port, and factoring
    it out as its own equation is what turned [FnFml] from "no model"
    into "one equation".  [typing/programs.v] states [typed_body] over
    [verus_halt_wsat]; the thesis states its judgment over
    [∗_{k<i} Winv_k].  Those are the same proposition exactly when the
    ambient ghost state is the family's top level, and nothing weaker
    will do: [verus_halt_wsat] at one level's names is that level's own
    borrows, box, invariants and store, while
    [verus_halt_wsat_below P ns j] is every level below [j], and no
    frame-preserving step takes one to the other.

    An earlier form of this class asked instead for
    [verus_halt_wsat ={∅}=∗ fn_wsat_lv j ∗ …] with no side condition,
    which *looks* like the thesis's "a caller lends the callee the part
    its level names" and is satisfied by no real family: it has to hold
    at every [j] at once, so [fn_wsat_lv] has to be the constant
    [verus_halt_wsat] and the execution level carries no information at
    all.  Splitting it in two is what makes the difference visible.

    To be exact about what that costs, since the earlier note here
    overstated it: a bad choice of [fn_wsat_lv] cannot make a divergent
    program typable.  [typing/soundness.v]'s [type_soundness] is a Rocq
    theorem taking [⊢ typed_body … e tr] to [sn erased_step], and these
    rules are machine-checked against it, so any [FnFml] whose
    obligations are provable is sound by construction.  What a constant
    [fn_wsat_lv] loses is not soundness but *content*: the level stops
    constraining anything, and whatever blocks Landin's knot is then
    something else - here, that a total [twp] has no Löb rule, so a
    self-referential [⊢ fn_body] has nothing to prove it with. *)
  fn_wsat_top : verus_halt_wsat ⊣⊢ fn_wsat_lv fn_lv_top;
  (** A caller at the ambient level lends a callee the world of any
    level **at or below** its own - the thesis's [j ≤ i].  Over the
    family this is [typing/level_ctx.v]'s [verus_halt_wsat_below_acsr],
    already proved; the side condition is what [fn_lv_top] is for, and
    what the unconditional form was quietly doing without.

    The strictness the discipline needs is one level down, inside
    [fn_wsat_lv] itself: the thesis's [∗_{k<j} Winv_k] is
    [verus_halt_wsat_below … j], the levels strictly *below* [j].  So
    [j = fn_lv_top] hands a callee exactly what the caller holds, which
    is what an ordinary top-level function needs and what the examples
    use, while [j < fn_lv_top] is the genuinely stratified case. *)
  fn_wsat_lv_acc {j} : (j ≤ fn_lv_top)%nat →
    ⊢ □ (fn_wsat_lv fn_lv_top ={∅}=∗
          fn_wsat_lv j ∗ (fn_wsat_lv j ={∅}=∗ fn_wsat_lv fn_lv_top));

  (** [j] is the arrow's **execution level** - the [j] of the thesis's
    [T →ⱼ U].  It is a parameter of [fn_fml] rather than a field of
    [fn_params] because the *type*'s level has to bound it, and
    [fn_params] is indexed by a parameter type [A] over which no maximum
    exists.  [fn] below sets [pt_lev := S j]. *)
  fn_fml {A : Type} {𝔄l 𝔅 ℭ} (j : nat)
    (fp : A → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
    (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)) : FML $oi Σ;

  (** *** The obligations: elimination at **every** candidate, and
    introduction at the Coq level.

    This replaces what used to be four fields - persistence,
    specialisation, and the two directions of the semantics, of which the
    introduction direction had no model at all.  All four are lemmas
    below; what a model owes is this equation and nothing else.

    The quantifier over [sem] is what makes it tractable rather than
    what makes it hard, and the reason is [nola/bi/deriv.v]'s
    [der_const].  A function type's ghost assertion has to be a formula,
    so its semantics may not mention [der]; a judgment's introduction
    normally then asks for the body at every *candidate*, and a
    candidate is not sound - a body cannot open the stored guards its own
    argument types carry ([typing/strat.v]).  But a semantics that does
    not depend on the candidate *at all* makes that quantifier vacuous,
    and [der_const] turns it into an [⊣⊢] in both directions.

    So the model's job is to pin [fn_fml j fp spec x] to a body that
    mentions no candidate - which is what the execution level is for: the
    body is read at the interpretation of a level *below* this one, one
    already constructed when this one is being defined.  The chain that
    makes that possible is [verus_halt_wsat_below] in
    [typing/level_ctx.v]. *)
  fn_fml_elim {sem} : alt_any sem →
    ∀ {A : Type} {𝔄l 𝔅 ℭ} (j : nat)
      (fp : A → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
      (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)),
    sem (fn_fml j fp spec x) ⊢ fn_body fn_wsat_lv j fp spec x;

  (** Introduction, at the **Coq** level, which is the shape every use
    in this file has: [type_fn]'s premise is [∀x ϝ k wl, ⊢ typed_body …],
    a tautology rather than an entailment from a context, because this
    port's [fn] is capture-free.

    This is the field that used to be the other half of an [⊣⊢], and
    the half that had no model.  The missing entailment is
    [fn_body ⊢ ⌜⊢ fn_body⌝], which is **false** - holding the body does
    not make it a tautology - so no model was ever going to supply it.
    Asking for the Coq-level implication instead is what makes the class
    realisable, and it costs nothing, because nothing in the development
    ever had the body as an Iris hypothesis to begin with. *)
  fn_fml_intro {A : Type} {𝔄l 𝔅 ℭ} (j : nat)
      (fp : A → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
      (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)) :
    (⊢ fn_body fn_wsat_lv j fp spec x) → ⊢ bor_sem (fn_fml j fp spec x);

  (** Persistence and specialisation, which the [⊣⊢] used to derive *)
  fn_fml_pers {sem} : alt_any sem →
    ∀ {A : Type} {𝔄l 𝔅 ℭ} (j : nat)
      (fp : A → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
      (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)),
    Persistent (sem (fn_fml j fp spec x));
  fn_fml_specialize {sem} : alt_any sem →
    ∀ {A B : Type} {𝔄l 𝔅 ℭ} (σ : A → B) (j : nat)
      (fp : B → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
      (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)),
    sem (fn_fml j fp spec x) ⊢ sem (fn_fml j (fp ∘ σ) spec x);
}.

(** The four fields that used to be assumed, now derived. *)
Section fn_fml_lemmas.
  Context `{!typeG FML Σ} `{FnFml0 : !FnFml}.

  Lemma fn_fml_pers_at {sem} (H : alt_sem sem)
    {A : Type} {𝔄l 𝔅 ℭ} (j : nat)
    (fp : A → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
    (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)) :
    Persistent (sem (fn_fml j fp spec x)).
  Proof. exact (fn_fml_pers (alt_sem_any H) j fp spec x). Qed.

  Lemma fn_fml_specialize_at {sem} (H : alt_sem sem)
      {A B : Type} {𝔄l 𝔅 ℭ} (σ : A → B) (j : nat)
      (fp : B → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
      (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)) :
    sem (fn_fml j fp spec x) ⊢ sem (fn_fml j (fp ∘ σ) spec x).
  Proof. exact (fn_fml_specialize (alt_sem_any H) σ j fp spec x). Qed.

  Lemma fn_fml_sem_1 {A : Type} {𝔄l 𝔅 ℭ} (j : nat)
      (fp : A → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
      (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)) :
    bor_sem (fn_fml j fp spec x) ⊢ fn_body fn_wsat_lv j fp spec x.
  Proof.
    (* [bor_sem] is [alt_amb] only up to conversion, so this is [exact]
      rather than [rewrite] - the same step [dinv_fml_sem] takes. *)
    exact (fn_fml_elim (alt_sem_any alt_here) j fp spec x).
  Qed.

  Lemma fn_fml_sem_2 {A : Type} {𝔄l 𝔅 ℭ} (j : nat)
      (fp : A → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
      (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)) :
    (⊢ fn_body fn_wsat_lv j fp spec x) → ⊢ bor_sem (fn_fml j fp spec x).
  Proof. exact (fn_fml_intro j fp spec x). Qed.
End fn_fml_lemmas.

Section fn.
  Context `{!typeG FML Σ} `{FnFml0 : !FnFml} {A: Type} {𝔄l 𝔅}.

  (** [j] is the arrow's execution level: [fn j fp spec] is the thesis's
    [T →ⱼ U], and its own level is [S j], so a function type sits
    *strictly above* every level its body may touch ([fn_ty_lev]). *)
  Program Definition fn {ℭ} (j : nat) (fp: A → fn_params)
      (spec: fn_spec 𝔄l 𝔅 ℭ)
    : type (exec_funₛ ℭ) :=
    {| (* FIXME : The definition of ty_lfts is less restrictive than the one
          used in Rust. In Rust, the type of parameters are taken into account
          for well-formedness, and all the liftime constrains relating a
          generalized liftime are ignored. For simplicity, we ignore all of
          them, but this is not very faithful. *)
      pt_size := 1;
      pt_lev := S j;
      (*
      pt_own (tr: predl_trans'ₛ _ _) tid vl := tc_opaque
        (∃fb kb (bl: plistc _ _) e H, ⌜vl = [@RecV fb (kb :: bl) e H]⌝ ∗
          ▷ □ ∀x ϝ k (wl: plistc _ _),
            typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
              [k ◁cont{[ϝ ⊑ₗ []], λ v: vec _ 1, +[vhd v ◁ own.box (fp x).(fp_oty)] } tr_ret]
              (hzip_with (λ _ ty (w: val), w ◁ own.box ty) (fp x).(fp_ityl) wl)
              (subst' fb (RecV fb (kb :: bl) e) $ subst' kb k $ subst_plv bl wl e)
              tr)
              *)
      pt_ghox (x: ~~ (exec_funₛ ℭ)) tid := fn_fml j fp spec x;
      pt_phys (x: ~~ (exec_funₛ ℭ)) tid := [FVal (fst x)];
    |}.
  Next Obligation. intros; apply fn_fml_pers_at; assumption. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.

  (** **** The stratification invariant

    A function type sits *strictly above* its arrow's level, so the
    world satisfaction its body is proved over - [∗_{k<j} Winv_k] -
    mentions only levels strictly below the type's own.  That is the
    well-foundedness condition of the thesis's (5.4), and it is now a
    fact about the former rather than a side condition anyone has to
    carry. *)
  Lemma fn_ty_lev {ℭ} (j : nat) (fp: A → fn_params)
    (spec: fn_spec 𝔄l 𝔅 ℭ) : ty_lev (fn j fp spec) = S j.
  Proof. done. Qed.

  Lemma fn_body_lev_lt {ℭ} (j : nat) (fp: A → fn_params)
    (spec: fn_spec 𝔄l 𝔅 ℭ) : (j < ty_lev (fn j fp spec))%nat.
  Proof. rewrite fn_ty_lev. lia. Qed.

  (** ** Landin's knot, at the port's own types

    [typing/strat_bor.v]'s [knot_not_typable] in the port's terms, and
    the reason [FnFml] must not be instantiated before the borrow slots
    carry the level of the machinery they use.

    A slot whose machinery is at level [k] may hold a value of type [ty]
    only when [ty_lev ty ≤ k] - the stored formula is read at level
    [k]'s interpretation, so its function types must already be defined
    there - while *reaching* that machinery asks for an execution level
    strictly above [k] ([typing/level_ctx.v]'s
    [verus_halt_wsat_below_acc]).

    A closure of arrow level [j] therefore needs a slot with
    [S j = ty_lev (fn j fp spec) ≤ k], and its own body, which runs at
    execution level [j], would need [k < j] to open the slot holding it.
    No [k] is both.  That is where all of [fn]'s soundness sits: with a
    [Wlv] that ignores the level the knot's body is provable as a
    tautology under the slot's declared type, and totality does not
    rescue it, because that body needs no Löb step - the callee's
    specification arrives from the context, not from an induction. *)
  Lemma knot_not_typable {ℭ} (j k : nat) (fp: A → fn_params)
    (spec: fn_spec 𝔄l 𝔅 ℭ) :
    (ty_lev (fn j fp spec) ≤ k)%nat → ¬ (k < j)%nat.
  Proof. rewrite fn_ty_lev. lia. Qed.

  (** Unfolding [fn]'s ghost assertion.  Only the two directions exist, not
    an [⊣⊢]: see [FnFml]. *)
  Lemma fn_gho_1 {ℭ} (j : nat) (fp: A → fn_params)
      (spec: fn_spec 𝔄l 𝔅 ℭ) x d g tid :
    ty_gho (fn j fp spec) x d g tid ⊢
      (∃fb kb (bl: plistc _ _) e H, ⌜fst x = @RecV fb (kb :: bl) e H⌝ ∗
        □ ∀y ϝ k (wl: plistc _ _),
          typed_body_at (fn_wsat_lv j) (fp_E (fp y) ϝ) [ϝ ⊑ₗ []]
            (InvCtx [] ϝ (fp_atomic_state (fp y)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp y))),
              λ v: vec _ 1, +[vhd v ◁ own.box (fp y).(fp_oty)] } tr_ret]
            (hzip_with (λ _ boxty (w: val), w ◁ boxty)
              (box_typel (fp y).(fp_ityl)) wl)
            (subst' fb (RecV fb (kb :: bl) e) $ subst' kb k $ subst_plv bl wl e)
            (spec (snd x))).
  Proof. apply fn_fml_sem_1. Qed.
  (** The same, with every body raised to the *ambient* world.

    A callee's body runs over [∗_{k<j} Winv_k] - that is the point of the
    level - and a caller holds the whole world and lends it the part its
    level names.  Doing that once here, rather than at the call, is what
    keeps [type_call_iris'] unchanged. *)
  Lemma fn_gho_1' {ℭ} (j : nat) (Hj : (j ≤ fn_lv_top)%nat)
      (fp: A → fn_params)
      (spec: fn_spec 𝔄l 𝔅 ℭ) x d g tid :
    ty_gho (fn j fp spec) x d g tid ⊢
      (∃fb kb (bl: plistc _ _) e H, ⌜fst x = @RecV fb (kb :: bl) e H⌝ ∗
        □ ∀y ϝ k (wl: plistc _ _),
          typed_body (fp_E (fp y) ϝ) [ϝ ⊑ₗ []]
            (InvCtx [] ϝ (fp_atomic_state (fp y)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp y))),
              λ v: vec _ 1, +[vhd v ◁ own.box (fp y).(fp_oty)] } tr_ret]
            (hzip_with (λ _ boxty (w: val), w ◁ boxty)
              (box_typel (fp y).(fp_ityl)) wl)
            (subst' fb (RecV fb (kb :: bl) e) $ subst' kb k $ subst_plv bl wl e)
            (spec (snd x))).
  Proof.
    rewrite fn_gho_1.
    iIntros "(%fb & %kb & %bl & %e & %H & %Hrec & #body)".
    iExists fb, kb, bl, e, H. iSplit; [done|].
    iIntros "!>" (y ϝ k wl). rewrite /typed_body /typed_body_at.
    iIntros (tid' xl mask post iκs) "A B C D E F G H2 I".
    iApply (twpw_incl_fupd (E:=∅) (W:=verus_halt_wsat)
      (W':=fn_wsat_lv j)); [set_solver| |].
    { rewrite fn_wsat_top. by iApply fn_wsat_lv_acc. }
    by iApply ("body" with "A B C D E F G H2 I").
  Qed.

  (** Introduction.  The premise is a Coq-level entailment, which is
    what [type_fn]'s own premise already is: see [FnFml]'s
    [fn_fml_intro] for why the Iris-level form is not merely unproved
    but false. *)
  Lemma fn_gho_2 {ℭ} (j : nat) (fp: A → fn_params)
      (spec: fn_spec 𝔄l 𝔅 ℭ) x d g tid :
      (⊢ ∃fb kb (bl: plistc _ _) e H, ⌜fst x = @RecV fb (kb :: bl) e H⌝ ∗
        □ ∀y ϝ k (wl: plistc _ _),
          typed_body_at (fn_wsat_lv j) (fp_E (fp y) ϝ) [ϝ ⊑ₗ []]
            (InvCtx [] ϝ (fp_atomic_state (fp y)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp y))),
              λ v: vec _ 1, +[vhd v ◁ own.box (fp y).(fp_oty)] } tr_ret]
            (hzip_with (λ _ boxty (w: val), w ◁ boxty)
              (box_typel (fp y).(fp_ityl)) wl)
            (subst' fb (RecV fb (kb :: bl) e) $ subst' kb k $ subst_plv bl wl e)
            (spec (snd x))) →
    ⊢ ty_gho (fn j fp spec) x d g tid.
  Proof. apply fn_fml_sem_2. Qed.

  (*
  Global Instance fn_ne n :
    Proper (pointwise_relation A (fn_params_dist n) ==> dist n) fn.
  Proof.
    move=> fp fp' Eq. apply ty_of_st_ne, st_of_pt_ne. split; [done|]=>/= ???.
    do 5 apply bi.exist_ne=> ?. do 3 f_equiv. f_equiv=> x. (do 5 f_equiv)=> wl.
    rewrite /typed_body /typed_body_at. (do 3 f_equiv)=> vπl.
    do 8 f_equiv; [by eapply fp_E_ne|]. do 2 f_equiv; [|f_equiv].
    - rewrite !cctx_interp_singleton /cctx_elt_interp. do 3 f_equiv.
      case=>/= [??]. rewrite /tctx_elt_interp. do 12 f_equiv. apply Eq.
    - move: (Eq x)=> [_[+ _]]. rewrite {1}/dist.
      move: (fp x).(fp_ityl) (fp' x).(fp_ityl)=> ??. clear=> Eq.
      induction Eq; [done|]. case wl=> ??. case vπl=> ??/=.
      f_equiv; [|by apply IHEq]. rewrite /tctx_elt_interp. by do 8 f_equiv.
  Qed.
  *)
End fn.

Arguments fn_params {_ _ _} _ _.

Global Instance elctx_empty : Empty (lft → elctx) := λ _, [].

(** The level sits on the *arrow*, as the thesis's [T →ⱼ U] has it. *)
Notation "fn< p > ( E ; ity , .. , ity' ) →{ j } oty" :=
  (fn j (λ p, FP E%EL (ity%T +:: .. (+[ity'%T]) ..) oty%T AtomicClosed))
  (at level 99, p pattern, j at level 0, oty at level 200, format
    "fn< p > ( E ;  ity ,  .. ,  ity' )  →{ j }  oty") : lrust_type_scope.
Notation "fn< p > ( E ) →{ j } oty" :=
  (fn j (λ p, FP E%EL +[] oty%T AtomicClosed))
  (at level 99, p pattern, j at level 0, oty at level 200, format
    "fn< p > ( E )  →{ j }  oty") : lrust_type_scope.
Notation "fn( E ; ity , .. , ity' ) →{ j } oty" :=
  (fn j (λ _: (), FP E%EL (ity%T +:: .. (+[ity'%T]) ..) oty%T AtomicClosed))
  (at level 99, j at level 0, oty at level 200, format
    "fn( E ;  ity ,  .. ,  ity' )  →{ j }  oty") : lrust_type_scope.
Notation "fn( E ) →{ j } oty" :=
  (fn j (λ _: (), FP E%EL +[] oty%T AtomicClosed))
  (at level 99, j at level 0, oty at level 200,
    format "fn( E )  →{ j }  oty") : lrust_type_scope.

Section typing.
  Context `{!typeG FML Σ} `{FnFml0 : !FnFml}.

  (*
  Global Instance fn_type_contractive {A 𝔄l 𝔅 ℭ} E
         (IT: A → type ℭ → typel 𝔄l) (OT: A → type ℭ → type 𝔅) :
    (∀x, ListTypeNonExpansive (IT x)) → (∀x, TypeNonExpansive (OT x)) →
    TypeContractive (λ ty, fn (λ x, FP (E x) (IT x ty) (OT x ty))).
  Proof.
    move=> NeIT NeOT.
    have Eq: (∀n ty ty', ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
      elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
      (∀vπ d tid vl, dist_later n (ty.(ty_own) vπ d tid vl) (ty'.(ty_own) vπ d tid vl)) →
      (∀vπ d κ tid l, (ty.(ty_shr) vπ d κ tid l) ≡{n}≡ (ty'.(ty_shr) vπ d κ tid l)) →
      ∀vπ vl,
        (fn (λ x, FP (E x) (IT x ty) (OT x ty))).(ty_own) vπ 0 xH vl ≡{n}≡
        (fn (λ x, FP (E x) (IT x ty') (OT x ty'))).(ty_own) vπ 0 xH vl); last first.
    { split; [|done| |].
      - apply (type_lft_morphism_const _ static [])=>//= ?. apply lft_equiv_refl.
      - move=> *. by apply Eq.
      - move=>/= n *. apply bi.exist_ne=> ?. apply bi.sep_ne; [done|].
        apply uPred_primitive.later_contractive. destruct n=>/=; [done|by apply Eq]. }
    move=>/= n ty ty' *. apply bi.exist_ne=> ?. apply bi.sep_ne; [done|].
    do 5 apply bi.exist_ne=> ?. f_equiv. f_contractive. (do 2 f_equiv)=> x.
    (do 5 f_equiv)=> wl. rewrite /typed_body /typed_body_at. (do 3 f_equiv)=> aπl. do 2 f_equiv.
    have EqBox: ∀𝔄 (T: type ℭ → type 𝔄), TypeNonExpansive T → ∀vπ d tid vl,
      (own.box (T ty)).(ty_own) vπ d tid vl ≡{n}≡ (own.box (T ty')).(ty_own) vπ d tid vl.
    { move=> ?? Ne. apply box_type_contractive=> *.
      - by apply Ne.
      - by iApply type_lft_morphism_lft_equiv_proper.
      - apply type_lft_morphism_elctx_interp_proper=>//. apply _.
      - apply dist_dist_later. by apply Ne.
      - apply dist_S. by apply Ne. }
    move: (NeIT x)=> [?[->NeITl]]. do 5 f_equiv; [|do 3 f_equiv; [|f_equiv]].
    - apply equiv_dist. rewrite /fp_E /= !elctx_interp_app.
      do 2 f_equiv; [|f_equiv; [|f_equiv]].
      + elim: NeITl; [done|]=> ????? _ ?. rewrite /tyl_E /= !elctx_interp_app.
        f_equiv; [|done]. apply type_lft_morphism_elctx_interp_proper=>//. apply _.
      + elim: NeITl; [done|]=> ????? _ ?. rewrite /tyl_outlives_E /= !elctx_interp_app.
        f_equiv; [|done]. rewrite !elctx_interp_ty_outlives_E.
        apply lft_incl_equiv_proper_r. by iApply type_lft_morphism_lft_equiv_proper.
      + apply type_lft_morphism_elctx_interp_proper=>//. apply _.
      + rewrite !elctx_interp_ty_outlives_E. apply lft_incl_equiv_proper_r.
        by iApply type_lft_morphism_lft_equiv_proper.
    - rewrite !cctx_interp_singleton /cctx_elt_interp. do 3 f_equiv. case=>/= ??.
      do 4 f_equiv. rewrite /tctx_elt_interp. do 6 f_equiv. by apply EqBox.
    - clear -NeITl EqBox. induction NeITl, wl, aπl; [done|]=>/=.
      f_equiv; [|done]. rewrite /tctx_elt_interp. do 6 f_equiv. by apply EqBox.
  Qed. *)

  Global Instance fn_send {A 𝔄l 𝔅 ℭ} j (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) : Send (fn j fp spec).
  Proof.
    split.
    - intros tid tid' x x' H. unfold syn_abstract in H. inversion H.
      unfold ty_phys, fn, ty_of_st. simpl. rewrite H1. trivial.
    - move=> tid tid' x d g G κs. iIntros "_ _ lfts _ K A $ !>".
      iExists x, 0%nat. rewrite Nat.add_0_r. iFrame "lfts K".
      iSplit; [|done].
      iExact "A".
  Qed.

  Global Instance fn_sync {A 𝔄l 𝔅 ℭ} j (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) : Sync (fn j fp spec).
  Proof. move=> *. by split. Qed.

  Lemma fn_resolve {A 𝔄l 𝔅 ℭ} j (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) E L : resolve E L (fn j fp spec) (const (const True)).
  Proof. apply resolve_just. Qed.

  Local Lemma subtypel_llctx_big_sep_box {𝔄l 𝔅l}
        (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl E L :
    subtypel E L tyl tyl' fl →
    llctx_interp L -∗ □ (elctx_interp E -∗
      [∗ hlist] ty; ty';- f ∈ tyl; tyl';- fl, type_incl (own.box ty) (own.box ty') (at_loc_mapₛ f)).
  Proof.
    elim=> [|>/box_subtype Sub _ IH]; [by iIntros "_!>_"|]. iIntros "L".
    iDestruct (Sub with "L") as "#Sub". iDestruct (IH with "L") as "#IH".
    iIntros "!> #E /=". iDestruct ("Sub" with "E") as "$".
    iDestruct ("IH" with "E") as "$".
  Qed.
  
  Program Definition fn_mapₛ {ℭ ℭ'}
      (f: (~~ℭ) → (~~ℭ')) : exec_funₛ ℭ →ₛ exec_funₛ ℭ'
   := {|
    syn_type_morphism_fn := (λ '(v, x), (v, f x)) ;
    syn_type_morphism_proph_fn := λ '(v, x) , (v, f x) ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  
  Fixpoint plist_boxl_mapₛ {𝔄l 𝔅l} :
      (plist2 (λ 𝔄 𝔅, 𝔄 →ₛ 𝔅) 𝔄l 𝔅l) → (Π! (boxl 𝔄l) →ₛ Π! (boxl 𝔅l)) :=
          match 𝔄l, 𝔅l with
          | [], [] => λ _, idₛ
          | _::_, _::_ => λ '(f -:: fl'), cons_prodₛ (at_loc_mapₛ f) (plist_boxl_mapₛ fl')
          | _, _ => absurd
          end.

  (*
  Lemma fn_subtype {A 𝔄l 𝔄l' 𝔅 𝔅'}
        j (fp: A → fn_params 𝔄l 𝔅) (fp': A → fn_params 𝔄l' 𝔅') fl
        (g: 𝔅 →ₛ 𝔅') E L :
    (∀x ϝ, let E' := E ++ fp_E (fp' x) ϝ in elctx_sat E' L (fp_E (fp x) ϝ) ∧
      subtypel E' L (fp' x).(fp_ityl) (fp x).(fp_ityl) fl ∧
      subtype E' L (fp x).(fp_oty) (fp' x).(fp_oty) g) →
    subtype E L (fn j fp) (fn j fp') (fn_mapₛ
     (λ tr (post: ~~(predₛ (at_locₛ 𝔅'))) (al': ~~((Π!%ST (boxl 𝔄l')))) mask π,
        tr (post ∘ (~~!ₛ (at_loc_mapₛ g))) (plist_boxl_mapₛ fl ~~$ₛ al') mask π)).
  Proof.
    move=> Big. apply subtype_plain_type=>/= ?. iIntros "L".
    iAssert (∀x ϝ, □ (elctx_interp (E ++ fp_E (fp' x) ϝ) -∗
      elctx_interp (fp_E (fp x) ϝ) ∗
      ([∗ hlist] ty'; ty;- f ∈ (fp' x).(fp_ityl); (fp x).(fp_ityl);- fl,
        type_incl (own.box ty') (own.box ty) f) ∗
      type_incl (own.box (fp x).(fp_oty)) (own.box (fp' x).(fp_oty)) g))%I as "#Big".
    { iIntros (x ϝ). case (Big x ϝ)=> Efp
        [/subtypel_llctx_big_sep_box Il /box_subtype O].
      iDestruct (Efp with "L") as "#Efp". iDestruct (Il with "L") as "#Il".
      iDestruct (O with "L") as "#O". iIntros "!> E'".
      iSplit; last iSplit; by [iApply "Efp"|iApply "Il"|iApply "O"]. }
    iIntros "!> #E". iSplit; [done|]. iSplit; [by iApply dincl_refl|].
    iIntros (tr _ vl). iDestruct 1 as (fb kb bl e H ->) "#fn".
    set eq := plist2_eq_nat_len fl. set bl' := plistc_renew (symmetry eq) bl.
    have Eq: (bl: list _) = bl' by rewrite vec_to_list_plistc_renew.
    iExists fb, kb, bl', e, (rew [λ bl₀, _ (_:b:_:b: bl₀ +b+_) _] Eq in H).
    simpl_eq. iSplit; [done|]. iNext. rewrite /typed_body /typed_body_at.
    iIntros (x ϝ ? wl' ? aπl' postπ') "!> LFT TIME PROPH UNIQ #Efp' Na L C T Obs".
    rewrite subst_plv_renew. set wl := plistc_renew _ wl'.
    iDestruct ("Big" with "[$E $Efp']") as "(Efp & InIl & InO)".
    iApply ("fn" $! _ _ _ _ _
      (plist_map_with (λ _ _, (∘)) fl aπl') (λ π b, postπ' π (g b))
      with "LFT TIME PROPH UNIQ Efp Na L [C] [T] [Obs]").
    - rewrite !cctx_interp_singleton. iRevert "InO C". iClear "#".
      iIntros "#(_&_& InO &_) C". iIntros (?[??]) "Na L /=[(%&%&%& ⧖ & oty) _] Obs".
      iApply ("C" $! _ -[_] with "Na L [⧖ oty] Obs"). iSplitL; [|done].
      iExists _, _. iSplitR; [done|]. iFrame "⧖". by iApply "InO".
    - iRevert "InIl T". iClear "#". iIntros "?". iStopProof. rewrite /wl.
      move: (fp x).(fp_ityl) (fp' x).(fp_ityl)=> tyl tyl'. clear.
      move: 𝔄l 𝔄l' tyl tyl' fl eq wl' aπl'. fix FIX 1. case=> [|??]; case=> [|??]//=
      tyl tyl'; inv_hlist tyl; inv_hlist tyl'; [by iIntros|].
      iIntros (????[]?[][]) "/= #[(_&_& In &_) ?] [t ?]".
      iSplitL "t"; [|by iApply FIX]. iDestruct "t" as (???) "[⧖ ?]".
      iExists _, _. iSplit; [done|]. iFrame "⧖". by iApply "In".
    - iApply proph_obs_eq; [|done]=>/= ?. f_equal. clear. move: 𝔄l 𝔄l' fl aπl'.
      fix FIX 1. case=> [|??]; case=>//= ??[??][??]. f_equal. apply FIX.
  Qed.
  *)

  Lemma fn_subtype_specialize {A B 𝔄l 𝔅 ℭ} (σ: A → B) j
      (fp: B → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) E L :
    subtype E L (fn j fp spec) (fn j (fp ∘ σ) spec) idₛ.
  Proof.
    apply subtype_plain_type. iIntros "_ !> _ /=". iSplit; [done|].
    iSplit; [iApply dincl_refl|]. iSplit; last by done.
    iIntros (sem Hs v tid). have ? := fn_fml_pers_at Hs.
    iIntros "#A". iSplitR; [by iApply (fn_fml_specialize_at Hs)|].
    iIntros "_". iApply "A".
  Qed.

  Local Lemma twp_app_hasty_box {𝔄l} vl r (f: val)
    (pl: plistc _ (boxl 𝔄l)) tyl vπl tid (Φ: val → iProp Σ) :
    tctx_interp tid (hzip_with (λ _ boxty q, q ◁ boxty) (box_typel tyl) pl) vπl -∗
    (∀wl: plistc _ _,
      tctx_interp tid (hzip_with (λ _ boxty (w: val), w ◁ boxty)
        (box_typel tyl) wl) vπl -∗
      WP[verus_halt_wsat] f (of_val r :: map of_val (vl ++ wl))%V [{ v, Φ v }]) -∗
    WP[verus_halt_wsat] f (of_val r :: map of_val vl ++ pl) [{ v, Φ v }].
  Proof.
    move: tyl pl vπl vl. elim=> [|???? IH].
    { iIntros "* _ Wp". iSpecialize ("Wp" $! -[] with "[//]").
      by rewrite !right_id. }
    iIntros ([p pl'][??]vl) "/= [p pl'] ToWp".
    have ->: App f (of_val r :: map of_val vl ++ p :: pl') =
      fill_item (AppRCtx f (r :: vl) pl') p by done.
    iApply twp_bind. iApply (twp_hasty with "p"). iIntros (w ? _) "p".
    have ->: fill_item (AppRCtx f (r :: vl) pl') w =
      App f (of_val r :: map of_val (vl ++ [w]) ++ pl') by rewrite map_app -assoc.
    iApply (IH with "pl'"). iIntros (?) "pl'". rewrite -assoc.
    iApply ("ToWp" $! (_-::_)). iFrame "pl'". iExists w, _. iFrame "p".
    by rewrite eval_path_of_val.
  Qed.

  Local Lemma invctx_interp_call Il ϝ' 𝛼 tid mask ϝ iκs :
      ϝ ⊑ ϝ' -∗
      ϝ ⊑ lft_intersect_list (fmap invctx_elt_unwrap Il) -∗
      invctx_interp tid mask iκs (InvCtx Il ϝ' 𝛼) -∗ ∃ iκs',
      invctx_interp tid mask iκs' (InvCtx [] ϝ 𝛼) ∗
          (∀ mask', invctx_interp tid mask' iκs' (InvCtx [] ϝ 𝛼) -∗ invctx_interp tid mask' iκs (InvCtx Il ϝ' 𝛼)).
  Proof.
      unfold invctx_interp.
      iIntros "#Incl1 #InclList".
      iDestruct 1 as (na_mask at_mask) "[#masks [[cna_lifetimes #Incl] [cna_own ato]]]".
      iExists (fmap invctx_elt_unwrap Il ++ iκs).
      iSplitL.
       - iExists na_mask, at_mask. iFrame "masks cna_own ato".
         unfold invctx_to_multiset. simpl. rewrite gmultiset_disj_union_left_id.
         rewrite list_to_set_disj_app. iFrame "cna_lifetimes".
         rewrite lft_intersect_list_app.
         iApply llftl_incl_glb; first by done.
         iApply (fguard_trans with "Incl1 Incl").
       - iDestruct 1 as (na_mask' at_mask') "[#masks' [[cna_lifetimes #Incl'] [cna_own ato]]]".
         iFrame. iFrame "#".
         unfold invctx_to_multiset. simpl. rewrite gmultiset_disj_union_left_id.
         rewrite list_to_set_disj_app. iFrame "cna_lifetimes".
  Qed.
  
  (** Calling a function.

    The original carries an arbitrary [Timeless G] together with guards from
    it to [llctx_interp L] and to [@[⨅κl]]; here the first is [Ltok γ L q]
    (whose persistent half gives the guard outright) and only the second is
    passed in.  [G] is shared for the call's lifetime [ϝ] with
    [llftl_borrow_shared], which now wants a *formula*: the fractional share
    is [gsrc_fml (GFrac γ q)].  The [wp_step_fupd] that collected [†ϝ] across
    a [Skip] is a plain update over the world satisfaction. *)
  Lemma type_call_iris' {A 𝔄l 𝔅 ℭ} L κl x j (fp: A → fn_params 𝔄l 𝔅)
      (spec: fn_spec 𝔄l 𝔅 ℭ) p ql ql' (k: expr) E xl efun tid
        (post: ~~ (at_locₛ 𝔅) → (Mask → (proph_asn → Prop)))
        (mask: Mask) Il ϝ' iκs γ q :
    (j ≤ fn_lv_top)%nat →
    AsVal k → IntoPlistc ql ql' →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) κl ++ E) L (fp_E (fp x) ϝ)) →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    fguardx (gsrc_fml (GFrac γ q)) (alive_fml (lft_intersect_list κl)) -∗
    Ltok γ L q -∗
    invctx_interp tid mask iκs (InvCtx Il ϝ' (fp_atomic_state (fp x))) -∗
    tctx_elt_interp tid (p ◁ fn j fp spec) efun -∗
    tctx_interp tid (hzip_with (λ _ boxty q, q ◁ boxty)
      (box_typel (fp x).(fp_ityl)) ql') xl -∗
    ⟨π, (spec efun.2) post xl mask π⟩ -∗
    (∀(ret: val) (mask': Mask) w, Ltok γ L q -∗
      invctx_interp tid mask' iκs (InvCtx Il ϝ' (fp_atomic_state (fp x))) -∗
      tctx_elt_interp tid (ret ◁ own.box (fp x).(fp_oty)) w -∗
      ⟨π, post w mask' π⟩ -∗
      WP[verus_halt_wsat] k [of_val ret] [{ _, cont_postcondition }]) -∗
    WP[verus_halt_wsat] (call: p ql → k) [{ _, cont_postcondition }].
  Proof.
    move=> Hj [k' <-]-> IctxAlv ToEfp.
    iIntros "#LFT #PROPH #UNIQ #E #Gguardsκl [#key tok] ii p ql Obs k".
    iApply fupdw_twpw_cont. iIntros "W".
    iDestruct (llftl_begin' with "LFT") as "B".
    iDestruct (bupdw_incl (W:=verus_halt_wsat) with "B") as "B'".
    iMod ("B'" with "W") as "[W (%ϝ & ϝtok & %ϝne)]".
    (* Read off what the external context gives, then put [L] back. *)
    iDestruct (Ltok_acc (W:=verus_halt_wsat) with "[$key $tok] W") as "[L →W]".
    iDestruct (ToEfp ϝ with "L") as "#EfpPre".
    iDestruct (lctx_ictx_alive_L_guards_ϝ _ _ _ _ _ IctxAlv with "L E")
      as "#Lguardsϝ'".
    iDestruct (lctx_ictx_alive_L_guards_list _ _ _ _ _ IctxAlv with "L E")
      as "#LguardsIl".
    iDestruct ("→W" with "L") as "[W [_ tok]]".
    (* Share the fraction for the call's lifetime. *)
    iDestruct (fguardx_borrow_shared (κ:=ϝ) (Px:=gsrc_fml (GFrac γ q))
      with "[tok]") as "Sh"; [by iApply gsrc_fml_sem_2|].
    iDestruct (bupdw_incl (W:=verus_halt_wsat) with "Sh") as "Sh'".
    iMod ("Sh'" with "W") as "[W [#fGuardsG0 ToG]]".
    iAssert (@[ϝ] &&{Wguard}&&> frac_tok γ q)%I as "#fGuardsG".
    { iDestruct (fguardx_alive_sem with "fGuardsG0") as "#G".
      iApply (guard_rhs_iff (gsrc_fml_sem (GFrac γ q))). iApply "G". }
    iAssert (dincl ϝ (lft_intersect_list κl)) as "#Borκl".
    { iApply dincl_fguardx.
      iApply (fguardx_trans with "fGuardsG0 Gguardsκl"). }
    iDestruct (guard_trans with "fGuardsG [] ") as "fGuardsL";
      [iApply (Ltok_guard_frac with "key")|].
    iDestruct ("EfpPre" with "[$E]") as "#Efp".
    { clear ToEfp. iClear "EfpPre". iClear "Gguardsκl".
      iInduction κl as [|κ κl] "IH"; [done|]=>/=.
      iSplit. { iApply (dincl_trans with "Borκl []").
        iApply dincl_intersect_l. }
      iApply "IH". iModIntro. iApply (dincl_trans with "Borκl []").
      iApply dincl_intersect_r. }
    iModIntro. iFrame "W".
    wp_bind p. iApply (twp_hasty with "p"). iIntros (?? _) "[gho %phys]".
    iDestruct (fn_gho_1' _ Hj with "gho") as (fb kb bl e Hclosed) "[%Hrec #e]".
    inversion phys as [Eqv].
    have ->: (λ: ["_r"], Skip;; k' ["_r"])%E = (λ: ["_r"], Skip;; k' ["_r"])%V
      by unlock.
    iApply (twp_app_hasty_box [] with "ql")=>/=. iIntros (wl) "ityl".
    rewrite Hrec. wp_rec.
    iDestruct (invctx_interp_call Il ϝ' _ tid mask ϝ iκs with "[] [] ii")
      as (iκs') "[ii iiback]".
      { iApply fguard_of_here. iApply (guard_trans with "fGuardsL Lguardsϝ'"). }
      { iApply fguard_of_here. iApply (guard_trans with "fGuardsL LguardsIl"). }
    iApply ("e" with "LFT PROPH UNIQ Efp [ϝtok] ii [ToG k iiback] ityl Obs").
    { iSplitL; [|done]. iExists _. iSplit; [by rewrite/= left_id|].
      by iFrame "ϝtok". }
    rewrite cctx_interp_singleton. iIntros (v' [locret b] mask').
    inv_vec v'=> v'.
    iIntros "[(%& %Eq & ϝtok &_) _] Invctx [oty ?] Obs".
    rewrite/= left_id in Eq. rewrite -Eq. wp_rec.
    iApply fupdw_twpw_cont. iIntros "W".
    iDestruct (llftl_end' with "LFT ϝtok") as "End"; [done|].
    iDestruct (fupdw_incl_mask (W:=verus_halt_wsat) (E':=⊤) with "End") as "End'";
      [set_solver|].
    iMod ("End'" with "W") as "[W †ϝ]".
    iDestruct ("ToG" with "†ϝ") as "ToG'".
    iDestruct (bupdw_incl (W:=verus_halt_wsat) with "ToG'") as "ToG''".
    iMod ("ToG''" with "W") as "[W tok]".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ q) with "tok") as "tok".
    iModIntro. iFrame "W". do 2 wp_seq.
    iDestruct ("iiback" with "Invctx") as "Invctx".
    destruct b. iApply ("k" with "[$key $tok] Invctx oty Obs").
  Qed.

  Lemma type_call_iris {A 𝔄l 𝔅 ℭ} x xl κl post (mask: Mask) j
      (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ)
      p ql ql' (k: expr) E efun tid γ q :
    (j ≤ fn_lv_top)%nat →
    AsVal k → IntoPlistc ql ql' →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) κl ++ E) [] (fp_E (fp x) ϝ)) →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    fguardx (gsrc_fml (GFrac γ q)) (alive_fml (lft_intersect_list κl)) -∗
    Ltok γ [] q -∗
    invctx_interp tid mask [] (InvCtx [] static (fp_atomic_state (fp x))) -∗
    tctx_elt_interp tid (p ◁ fn j fp spec) efun -∗
    tctx_interp tid (hzip_with (λ _ boxty q, q ◁ boxty)
      (box_typel (fp x).(fp_ityl)) ql') xl -∗
    ⟨π, (spec efun.2) post xl mask π⟩ -∗
    (∀(ret: val) (mask': Mask) w, Ltok γ [] q -∗
      invctx_interp tid mask' [] (InvCtx [] static (fp_atomic_state (fp x))) -∗
      tctx_elt_interp tid (ret ◁ own.box (fp x).(fp_oty)) w -∗
      ⟨π, post w mask' π⟩ -∗
      WP[verus_halt_wsat] k [of_val ret] [{ _, cont_postcondition }]) -∗
    WP[verus_halt_wsat] (call: p ql → k) [{ _, cont_postcondition }].
  Proof.
    iIntros (Hj ???) "LFT PROPH UNIQ E #Guardsκl tok Invctx p ql Obs k".
    iApply (type_call_iris' [] with
      "LFT PROPH UNIQ E Guardsκl tok Invctx p ql Obs").
      - exact Hj.
      - split.
        + unfold lctx_lft_alive. iIntros "_ _".
          setoid_rewrite static_alive_true. iApply guard_true.
        + intros κ Hnotin. simpl in Hnotin. rewrite elem_of_nil in Hnotin.
          contradiction.
      - done.
      - iIntros (???) "G I ret Obs". iApply ("k" with "G I ret Obs").
  Qed.

  Lemma type_call {A 𝔄l 𝔅 ℭl 𝔇l 𝔈l 𝔉 ℭ} x j (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) p ql ql' k trx
      trk tri E L (C: cctx 𝔉) Il ϝ' (T: tctx ℭl) (T': tctx 𝔇l) (Tk: vec val 1 → tctx 𝔈l) :
    (j ≤ fn_lv_top)%nat →
    IntoPlistc ql ql' → Forall (lctx_lft_alive_all E L) L.*1 →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    tctx_extract_ctx E L (p ◁ fn j fp spec +::
      hzip_with (λ _ boxty q, q ◁ boxty) (box_typel (fp x).(fp_ityl)) ql') T T' trx →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    k ◁cont{L, (InvCtx Il ϝ' (fp_atomic_state (fp x))), Tk} trk ∈ C →
    (∀ret: val, tctx_incl E L (ret ◁ own.box (fp x).(fp_oty) +:: T') (Tk [#ret]) tri) →
    ⊢ typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C T (call: p ql → k) (trx ∘
      (λ post '(trp -:: adl), λ mask π,
      let '(al, dl) := psep adl in
        (spec trp.2) (λ (b: ~~ (at_locₛ 𝔅)) mask π, tri (trk post) (b -:: dl) mask π) al mask π)).
  Proof.
    move=> Hj ? Alv ???? InTk. iApply typed_body_tctx_incl; [done|].
    iIntros (?[? adπl]mask post iκs). move: (papp_ex adπl)=> [aπl[dπl->]].
    iIntros "#LFT #PROPH #UNIQ #E L I C /=(p & ql & T') Obs".
    have Alv' := lctx_lft_alive_all_tok_list E L _ Alv.
    iDestruct (lctx_lft_alive_all_guards E L _ Alv' with "L E") as "#AlvAll".
    iApply fupdw_twpw_cont. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]". iModIntro. iFrame "W".
    iDestruct "tok" as "[#key tok]".
    iApply (type_call_iris' with
      "LFT PROPH UNIQ E [] [$key $tok] I p ql [Obs]"); [done|done|done|..].
    { iApply fguardx_of_all. iIntros "!>" (sem Hs).
      rewrite (gsrc_sem_at_any Hs) (alive_sem_at_any Hs).
      iApply (guard_trans with "[] []").
      - iApply (Ltok_guard_frac_at Hs with "key").
      - iApply ("AlvAll" $! sem with "[//]"). }
    { iApply proph_obs_eq; [|done]=>/= ?. by rewrite papp_sepl papp_sepr. }
    iIntros (ret mask' ?) "tok I ret Obs".
    iApply fupdw_twpw_cont. iIntros "W".
    iMod (proj2 (InTk _) _ _ _ (_-::_) with
      "LFT PROPH UNIQ E tok [$ret $T'] Obs W") as "[W (%& tok & Tk & Obs)]".
    iMod (Ltok_withdraw with "tok W") as "[W L]". iModIntro. iFrame "W".
    have ->: [ret: expr] = map of_val ([#ret]) by done.
    iApply ("C" with "[%//] L I Tk Obs").
  Qed.

  Lemma type_letcall {A 𝔄l 𝔅 ℭ ℭl 𝔇l 𝔈} x j (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) p ql ql'
                     Il ϝ' (T: tctx ℭl) (T': tctx 𝔇l) b e trx tr E L (C: cctx 𝔈)
                     `{!IntoPlistc ql ql', !Closed (b :b: []) e, !Closed [] p} :
    (j ≤ fn_lv_top)%nat →
    TCForall (Closed []) ql → Forall (lctx_lft_alive_all E L) L.*1 →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    tctx_extract_ctx E L (p ◁ fn j fp spec +::
      hzip_with (λ _ boxty q, q ◁ boxty) (box_typel (fp x).(fp_ityl)) ql') T T' trx →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    (∀ret: val, typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C
      (ret ◁ own.box (fp x).(fp_oty) +:: T') (subst' b ret e) tr) -∗
    typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C T (letcall: b := p ql in e) (trx ∘ (λ post '(trp -:: adl) mask π,
      let '(al, dl) := psep adl in (spec trp.2) (λ b mask π, tr post (b -:: dl) mask π) al mask π)).
  Proof.
    move=> Hj Clql ????. iIntros "e". iApply type_cont_norec.
    - (* TODO : make [solve_closed] work here. *)
      eapply is_closed_weaken; [done|]. set_solver+.
    - (* TODO : make [solve_closed] work here. *)
      rewrite /Closed /= !andb_True. split.
      + by eapply is_closed_weaken, list_subseteq_nil.
      + eapply Is_true_eq_left, forallb_forall, List.Forall_forall, Forall_impl;
        [by apply TCForall_Forall|]=> ??.
        eapply Is_true_eq_true, is_closed_weaken=>//. set_solver+.
    - iIntros (k).
      (* TODO : make [simpl_subst] work here. *)
      have ->: subst' "_k" k (call: p ql → "_k")%E = subst "_k" k p $
        (λ: ["_r"], Skip;; k ["_r"])%E :: map (subst "_k" k) ql by done.
      rewrite is_closed_nil_subst; [|done].
      have ->: map (subst "_k" k) ql = ql.
      { clear -Clql. elim Clql; [done|]=>/= ????->. by rewrite is_closed_nil_subst. }
      iApply typed_body_proper; last first.
      { iApply type_call=>//; [constructor|]=> v.
        have {1}->: v = vhd [#v] by done. move: [#v]=> ?. apply tctx_incl_refl. }
      done.
    - iIntros (? ret). inv_vec ret=> ret. rewrite /subst_v /=.
      rewrite (is_closed_subst []); [| |set_solver+]; last first.
      { apply subst'_is_closed; [|done]. apply is_closed_of_val. }
      iApply "e".
  Qed.

  (** *** The ambient level

    [fn_wsat_top] says the ambient world satisfaction *is* the family's
    top, so a body at execution level [fn_lv_top] is an ordinary
    [typed_body] and every rule in [typing/] applies to it unchanged.

    This is what an ordinary function is: the thesis's [j ≤ i] at
    [j = i].  A level strictly below the ambient one is the stratified
    case, and the only one that needs the family. *)
  Lemma typed_body_at_top {𝔄l 𝔅} E L (I : invctx) (C : cctx 𝔅)
      (T : tctx 𝔄l) e tr :
    typed_body_at (fn_wsat_lv fn_lv_top) E L I C T e tr ⊣⊢
      typed_body E L I C T e tr.
  Proof.
    rewrite /typed_body. apply bi.equiv_entails. split.
    - iIntros "H". iApply (typed_body_at_wsat with "[] H").
      rewrite fn_wsat_top. iIntros "!> W !>". iFrame "W".
      iIntros "W !>". iFrame.
    - iIntros "H". iApply (typed_body_at_wsat with "[] H").
      rewrite fn_wsat_top. iIntros "!> W !>". iFrame "W".
      iIntros "W !>". iFrame.
  Qed.

  (** Typing a function literal.

    VerusBelt proves the *recursive* rule [type_fnrec] by [iLöb] - tying the
    function's own specification back into its body - and derives [type_fn]
    from it by dropping the recursive hypothesis.  Löb induction is exactly
    what a total weakest precondition gives up, so [type_fnrec] is not
    ported, and [type_fn] is proved directly: a non-recursive body never
    needs its own specification. *)
  Lemma type_fn {A 𝔄l 𝔅 ℭ} tr j (fp: A → fn_params 𝔄l 𝔅)
      (spec: fn_spec 𝔄l 𝔅 ℭ)
      e bl bl' `{Into: !IntoPlistc bl bl',
      Cl: !Closed (("return" :: bl)%binder +b+ []) e} :
    (* The body is proved over [∗_{k<j} Winv_k], not over the whole world:
      a function at execution level [j] may touch only what the levels
      below [j] hold.  That is the stratification discipline, and it is
      what makes [fn]'s interpretation well-founded. *)
    (∀x ϝ k (wl: plistc _ (boxl 𝔄l)),
        ⊢ typed_body_at (fn_wsat_lv j) (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
            (InvCtx [] ϝ (fp_atomic_state (fp x)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp x))),
              λ v: vec _ 1, +[vhd v ◁ own.box (fp x).(fp_oty)] } tr_ret]
            (hzip_with (λ _ boxty (v: val), v ◁ boxty)
              (box_typel (fp x).(fp_ityl)) wl)
            (subst "return" k $ subst_plv bl' wl e) (spec tr)) →
    typed_val (fn: bl := e)%V (fn j fp spec)
      (@RecV BAnon ("return" :: bl)%binder e Cl, tr).
  Proof.
    move: Cl. rewrite Into. iIntros (Cl Body ????????) "_ _ _ _ $$ _ Obs".
    iApply twp_value.
    iExists -[((@RecV BAnon ("return" :: bl')%binder e Cl)%V, tr)].
    iFrame "Obs". iSplit; [|done]. iExists _, 0%nat.
    iSplit; [by rewrite/= decide_True_pi|]. iSplit; last by done.
    iApply fn_gho_2. iStartProof.
    iExists BAnon, "return", bl', e, _. iSplit; [done|].
    iIntros "!>" (y ϝ k wl). iApply Body.
  Qed.

  (** [type_fn] and [type_call] at the ambient level, which is where an
    ordinary function lives.

    The premise of [type_fn_top] is a plain [typed_body], so the rules
    of [typing/] compose with it directly, and [type_call_top] has no
    side condition left to discharge.  Between them these are the shape
    VerusBelt's own [type_fn] and [type_call] have - upstream has no
    execution level at all - so a program verified against them is
    verified against the port's rules exactly as it is upstream, with
    the level visible only in the type, as [fn fn_lv_top fp spec]. *)
  Lemma type_fn_top {A 𝔄l 𝔅 ℭ} tr (fp: A → fn_params 𝔄l 𝔅)
      (spec: fn_spec 𝔄l 𝔅 ℭ)
      e bl bl' `{Into: !IntoPlistc bl bl',
      Cl: !Closed (("return" :: bl)%binder +b+ []) e} :
    (∀x ϝ k (wl: plistc _ (boxl 𝔄l)),
        ⊢ typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
            (InvCtx [] ϝ (fp_atomic_state (fp x)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp x))),
              λ v: vec _ 1, +[vhd v ◁ own.box (fp x).(fp_oty)] } tr_ret]
            (hzip_with (λ _ boxty (v: val), v ◁ boxty)
              (box_typel (fp x).(fp_ityl)) wl)
            (subst "return" k $ subst_plv bl' wl e) (spec tr)) →
    typed_val (fn: bl := e)%V (fn fn_lv_top fp spec)
      (@RecV BAnon ("return" :: bl)%binder e Cl, tr).
  Proof.
    move=> Body.
    apply (type_fn tr fn_lv_top fp spec e bl bl' (Into:=Into) (Cl:=Cl)).
    move=> x ϝ k wl. rewrite typed_body_at_top. apply Body.
  Qed.

  Lemma type_call_top {A 𝔄l 𝔅 ℭl 𝔇l 𝔈l 𝔉 ℭ} x (fp: A → fn_params 𝔄l 𝔅)
      (spec: fn_spec 𝔄l 𝔅 ℭ) p ql ql' k trx
      trk tri E L (C: cctx 𝔉) Il ϝ' (T: tctx ℭl) (T': tctx 𝔇l)
      (Tk: vec val 1 → tctx 𝔈l) :
    IntoPlistc ql ql' → Forall (lctx_lft_alive_all E L) L.*1 →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    tctx_extract_ctx E L (p ◁ fn fn_lv_top fp spec +::
      hzip_with (λ _ boxty q, q ◁ boxty) (box_typel (fp x).(fp_ityl)) ql') T T' trx →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    k ◁cont{L, (InvCtx Il ϝ' (fp_atomic_state (fp x))), Tk} trk ∈ C →
    (∀ret: val, tctx_incl E L (ret ◁ own.box (fp x).(fp_oty) +:: T') (Tk [#ret]) tri) →
    ⊢ typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C T (call: p ql → k) (trx ∘
      (λ post '(trp -:: adl), λ mask π,
      let '(al, dl) := psep adl in
        (spec trp.2) (λ (b: ~~ (at_locₛ 𝔅)) mask π, tri (trk post) (b -:: dl) mask π) al mask π)).
  Proof.
    move=> *. apply (type_call x fn_lv_top fp spec p ql ql' k trx trk tri
      E L C Il ϝ' T T' Tk); [lia|assumption..].
  Qed.

  Lemma type_letcall_top {A 𝔄l 𝔅 ℭ ℭl 𝔇l 𝔈} x (fp: A → fn_params 𝔄l 𝔅)
      (spec: fn_spec 𝔄l 𝔅 ℭ) p ql ql'
      Il ϝ' (T: tctx ℭl) (T': tctx 𝔇l) b e trx tr E L (C: cctx 𝔈)
      `{!IntoPlistc ql ql', !Closed (b :b: []) e, !Closed [] p} :
    TCForall (Closed []) ql → Forall (lctx_lft_alive_all E L) L.*1 →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    tctx_extract_ctx E L (p ◁ fn fn_lv_top fp spec +::
      hzip_with (λ _ boxty q, q ◁ boxty) (box_typel (fp x).(fp_ityl)) ql') T T' trx →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    (∀ret: val, typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C
      (ret ◁ own.box (fp x).(fp_oty) +:: T') (subst' b ret e) tr) -∗
    typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C T (letcall: b := p ql in e) (trx ∘ (λ post '(trp -:: adl) mask π,
      let '(al, dl) := psep adl in (spec trp.2) (λ b mask π, tr post (b -:: dl) mask π) al mask π)).
  Proof.
    move=> *. apply (type_letcall x fn_lv_top fp spec p ql ql' Il ϝ' T T'
      b e trx tr E L C); [lia|assumption..].
  Qed.
End typing.

(** ** A candidate model, and what it does and does not settle

  [FnFml] above asks for an [⊣⊢]: the semantics *is* the body, at every
  candidate.  That is what [nola/bi/deriv.v]'s [der_const] shows is
  enough, and it is what a level-indexed interpretation would supply.

  This section records that a **weaker** interface - elimination at
  every candidate, and introduction at the *Coq* level - is realisable
  right now, with no level machinery at all, by taking the ghost
  assertion to be the pure proposition that the body is derivable.

  The reason that is even a candidate is a property of this port's [fn]
  that is easy to miss: it is **capture-free**.  [type_fn]'s premise is
  [∀x ϝ k wl, ⊢ typed_body …] - a *tautology*, not an entailment from a
  context - so the body's derivability is a fact about the code and
  carries no resources.  A pure proposition is then an honest reading of
  "this value is a function whose body is well-typed", and
  [pure_sem_at_any] makes it constant in the candidate for free, which
  is exactly the property [der_const] wants.

  **What this does not settle.**  Two things, and they are why nothing
  here is declared an instance.

  First, it does not instantiate [FnFml] as stated: [pure_fml] gives
  [tfn_elim] and [tfn_intro], not the [⊣⊢].  The missing direction is
  [fn_body ⊢ ⌜⊢ fn_body⌝], which is false - holding the body does not
  make it a tautology.  Every *use* in this file goes through the Coq
  level ([type_fn]'s premise, [type_call_iris']'s elimination), so the
  weaker interface would do; but the class would have to be restated,
  and whether that is the right interface is a design question.

  Second, and more important: its **soundness rests entirely on [Wlv]**,
  and the development already knows why.  With
  [Wlv := λ _, verus_halt_wsat] the execution level does no work at all, and
  the introduction rule above is then far too permissive: the body of
  Landin's knot - read a function out of the slot holding you, and call
  it - is provable as a tautology under the slot's declared type, so the
  knot would be typable and a diverging program would satisfy
  [verus_halt_type_soundness].

  Totality does *not* rescue it, which was worth checking: the knot's
  body needs no Löb step, because the callee's specification arrives as
  a hypothesis from the context rather than from an induction.  What
  rescues it is the level, and [typing/strat_bor.v]'s [knot_not_typable]
  is the argument in one line - a borrow slot of level [k] admits a
  function of execution level [j ≤ k], while *opening* that slot asks
  for execution level [> k], so a closure that reaches the borrow
  holding it would need [k < j] too, and no [j] is both.

  So the reading this section supports is not "the level is
  unnecessary".  It is the opposite, and sharper than the plan had it:
  the *formula* side of [fn] needs no judgment at all - a pure
  proposition will do, and [pure_sem_at_any] makes it candidate-
  independent for free - and **every bit of the work is carried by
  [Wlv]**.  Instantiating [FnFml] therefore turns on supplying the real
  [verus_halt_wsat_below … j], which this branch has built, together with
  the borrow-slot level discipline that [strat_bor.v] states and the
  port's borrow formers do not yet carry. *)
Section fn_pure_candidate.
  Context `{!typeG FML Σ}.

  Definition tfn_fml {A : Type} {𝔄l 𝔅 ℭ} (Wlv : nat → iProp Σ) (j : nat)
      (fp : A → fn_params 𝔄l 𝔅)
      (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)) : FML $oi Σ :=
    pure_fml (⊢ fn_body Wlv j fp spec x).

  (** Elimination, at every candidate *)
  Lemma tfn_elim {sem} (H : alt_any sem) {A 𝔄l 𝔅 ℭ} Wlv j
      (fp : A → fn_params 𝔄l 𝔅) (spec : fn_spec 𝔄l 𝔅 ℭ) x :
    sem (tfn_fml Wlv j fp spec x) ⊢ fn_body Wlv j fp spec x.
  Proof.
    rewrite /tfn_fml (pure_sem_at_any H). iIntros (Hb). iApply Hb.
  Qed.

  (** Introduction, at the Coq level - the shape [type_fn]'s premise has *)
  Lemma tfn_intro {A 𝔄l 𝔅 ℭ} Wlv j
      (fp : A → fn_params 𝔄l 𝔅) (spec : fn_spec 𝔄l 𝔅 ℭ) x :
    (⊢ fn_body Wlv j fp spec x) → ⊢ bor_sem (tfn_fml Wlv j fp spec x).
  Proof. move=> ?. rewrite /tfn_fml pure_fml_sem. by iPureIntro. Qed.

  Lemma tfn_pers {sem} (H : alt_any sem) {A 𝔄l 𝔅 ℭ} Wlv j
      (fp : A → fn_params 𝔄l 𝔅) (spec : fn_spec 𝔄l 𝔅 ℭ) x :
    Persistent (sem (tfn_fml Wlv j fp spec x)).
  Proof. rewrite /tfn_fml (pure_sem_at_any H). exact _. Qed.

  Lemma tfn_specialize {sem} (H : alt_any sem) {A B 𝔄l 𝔅 ℭ} (σ : A → B) Wlv j
      (fp : B → fn_params 𝔄l 𝔅) (spec : fn_spec 𝔄l 𝔅 ℭ) x :
    sem (tfn_fml Wlv j fp spec x) ⊢ sem (tfn_fml Wlv j (fp ∘ σ) spec x).
  Proof.
    rewrite /tfn_fml !(pure_sem_at_any H). iIntros (Hb). iPureIntro.
    iStartProof. iApply fn_body_specialize. iApply Hb.
  Qed.
End fn_pure_candidate.

Ltac simpl_fp_E := rewrite /fp_E /ty_outlives_E /=.

Global Hint Resolve elctx_sat_fp_E : lrust_typing.
Global Hint Resolve fn_resolve (* fn_subtype *) : lrust_typing.
