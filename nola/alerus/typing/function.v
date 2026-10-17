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
From nola.alerus.typing Require Import own programs cont.
From nola.alerus.typing Require Export type ctx.
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
  fn_fml {A : Type} {𝔄l 𝔅 ℭ} (fp : A → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
    (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)) : FML $oi Σ;
  (** A function type's ghost assertion is a judgment, so only its
    persistence is available at a candidate interpretation; see the note on
    [AltSem] in [typing/ctx.v]. *)
  fn_fml_pers_at {sem} : alt_sem sem →
    ∀ {A : Type} {𝔄l 𝔅 ℭ} (fp : A → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
      (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)),
    Persistent (sem (fn_fml fp spec x));
  fn_fml_sem {A : Type} {𝔄l 𝔅 ℭ} (fp : A → fn_params (𝔄l:=𝔄l) (𝔅:=𝔅))
    (spec : fn_spec 𝔄l 𝔅 ℭ) (x : ~~ (exec_funₛ ℭ)) :
    bor_sem (fn_fml fp spec x) ⊣⊢
      (∃fb kb (bl: plistc _ _) e H, ⌜fst x = @RecV fb (kb :: bl) e H⌝ ∗
        □ ∀y ϝ k (wl: plistc _ _),
          typed_body (fp_E (fp y) ϝ) [ϝ ⊑ₗ []]
            (InvCtx [] ϝ (fp_atomic_state (fp y)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp y))),
              λ v: vec _ 1, +[vhd v ◁ own.box (fp y).(fp_oty)] } tr_ret]
            (hzip_with (λ _ boxty (w: val), w ◁ boxty)
              (box_typel (fp y).(fp_ityl)) wl)
            (subst' fb (RecV fb (kb :: bl) e) $ subst' kb k $ subst_plv bl wl e)
            (spec (snd x)))%I;
}.

Section fn.
  Context `{!typeG FML Σ} `{FnFml0 : !FnFml} {A: Type} {𝔄l 𝔅}.

  Program Definition fn {ℭ} (fp: A → fn_params) (spec: fn_spec 𝔄l 𝔅 ℭ)
    : type (exec_funₛ ℭ) :=
    {| (* FIXME : The definition of ty_lfts is less restrictive than the one
          used in Rust. In Rust, the type of parameters are taken into account
          for well-formedness, and all the liftime constrains relating a
          generalized liftime are ignored. For simplicity, we ignore all of
          them, but this is not very faithful. *)
      pt_size := 1;
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
      pt_ghox (x: ~~ (exec_funₛ ℭ)) tid := fn_fml fp spec x;
      pt_phys (x: ~~ (exec_funₛ ℭ)) tid := [FVal (fst x)];
    |}.
  Next Obligation. move=> ??? sem H *. by apply (fn_fml_pers_at H). Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.

  (** Unfolding [fn]'s ghost assertion *)
  Lemma fn_gho {ℭ} (fp: A → fn_params) (spec: fn_spec 𝔄l 𝔅 ℭ) x d g tid :
    ty_gho (fn fp spec) x d g tid ⊣⊢
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
  Proof. apply fn_fml_sem. Qed.

  (*
  Global Instance fn_ne n :
    Proper (pointwise_relation A (fn_params_dist n) ==> dist n) fn.
  Proof.
    move=> fp fp' Eq. apply ty_of_st_ne, st_of_pt_ne. split; [done|]=>/= ???.
    do 5 apply bi.exist_ne=> ?. do 3 f_equiv. f_equiv=> x. (do 5 f_equiv)=> wl.
    rewrite /typed_body. (do 3 f_equiv)=> vπl.
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

Notation "fn< p > ( E ; ity , .. , ity' ) → oty" :=
  (fn (λ p, FP E%EL (ity%T +:: .. (+[ity'%T]) ..) oty%T AtomicClosed))
  (at level 99, p pattern, oty at level 200, format
    "fn< p > ( E ;  ity ,  .. ,  ity' )  →  oty") : lrust_type_scope.
Notation "fn< p > ( E ) → oty" := (fn (λ p, FP E%EL +[] oty%T AtomicClosed))
  (at level 99, p pattern, oty at level 200, format
    "fn< p > ( E )  →  oty") : lrust_type_scope.
Notation "fn( E ; ity , .. , ity' ) → oty" :=
  (fn (λ _: (), FP E%EL (ity%T +:: .. (+[ity'%T]) ..) oty%T AtomicClosed))
  (at level 99, oty at level 200, format
    "fn( E ;  ity ,  .. ,  ity' )  →  oty") : lrust_type_scope.
Notation "fn( E ) → oty" := (fn (λ _: (), FP E%EL +[] oty%T AtomicClosed))
  (at level 99, oty at level 200, format "fn( E )  →  oty") : lrust_type_scope.

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
    (do 5 f_equiv)=> wl. rewrite /typed_body. (do 3 f_equiv)=> aπl. do 2 f_equiv.
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

  Global Instance fn_send {A 𝔄l 𝔅 ℭ} (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) : Send (fn fp spec).
  Proof.
    split.
    - intros tid tid' x x' H. unfold syn_abstract in H. inversion H.
      unfold ty_phys, fn, ty_of_st. simpl. rewrite H1. trivial.
    - move=> tid tid' x d g G κs. iIntros "_ _ lfts _ K A $ !>".
      iExists x, 0%nat. rewrite Nat.add_0_r. iFrame "lfts K".
      iSplit; [|done].
      iExact "A".
  Qed.

  Global Instance fn_sync {A 𝔄l 𝔅 ℭ} (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) : Sync (fn fp spec).
  Proof. move=> *. split; [done|]. split; iSplit; iIntros "?"; done. Qed.

  Lemma fn_resolve {A 𝔄l 𝔅 ℭ} (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) E L : resolve E L (fn fp spec) (const (const True)).
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
        (fp: A → fn_params 𝔄l 𝔅) (fp': A → fn_params 𝔄l' 𝔅') fl (g: 𝔅 →ₛ 𝔅') E L :
    (∀x ϝ, let E' := E ++ fp_E (fp' x) ϝ in elctx_sat E' L (fp_E (fp x) ϝ) ∧
      subtypel E' L (fp' x).(fp_ityl) (fp x).(fp_ityl) fl ∧
      subtype E' L (fp x).(fp_oty) (fp' x).(fp_oty) g) →
    subtype E L (fn fp) (fn fp') (fn_mapₛ
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
    iIntros "!> #E". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iIntros (tr _ vl). iDestruct 1 as (fb kb bl e H ->) "#fn".
    set eq := plist2_eq_nat_len fl. set bl' := plistc_renew (symmetry eq) bl.
    have Eq: (bl: list _) = bl' by rewrite vec_to_list_plistc_renew.
    iExists fb, kb, bl', e, (rew [λ bl₀, _ (_:b:_:b: bl₀ +b+_) _] Eq in H).
    simpl_eq. iSplit; [done|]. iNext. rewrite /typed_body.
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

  Lemma fn_subtype_specialize {A B 𝔄l 𝔅 ℭ} (σ: A → B) (fp: B → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) E L :
    subtype E L (fn fp spec) (fn (fp ∘ σ) spec) idₛ.
  Proof.
    apply subtype_plain_type. iIntros "_ !> _ /=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|]. iSplit; last by done. iIntros "*".
    rewrite /pt_gho /= !fn_fml_sem.
    iIntros "#A". iFrame "A". iSplit; last by (iIntros "_"; done).
    iDestruct "A" as (fb kb bl e H) "[A #B]". iExists fb, kb, bl, e, H. iFrame "A".
    iModIntro. iIntros (y ϝ k wl). iApply "B".
  Qed.

  Local Lemma twp_app_hasty_box {𝔄l} vl r (f: val)
    (pl: plistc _ (boxl 𝔄l)) tyl vπl tid (Φ: val → iProp Σ) :
    tctx_interp tid (hzip_with (λ _ boxty q, q ◁ boxty) (box_typel tyl) pl) vπl -∗
    (∀wl: plistc _ _,
      tctx_interp tid (hzip_with (λ _ boxty (w: val), w ◁ boxty)
        (box_typel tyl) wl) vπl -∗
      WP[alerus_wsat] f (of_val r :: map of_val (vl ++ wl))%V [{ v, Φ v }]) -∗
    WP[alerus_wsat] f (of_val r :: map of_val vl ++ pl) [{ v, Φ v }].
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
         iApply (guard_trans with "Incl1 Incl").
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
  Lemma type_call_iris' {A 𝔄l 𝔅 ℭ} L κl x (fp: A → fn_params 𝔄l 𝔅)
      (spec: fn_spec 𝔄l 𝔅 ℭ) p ql ql' (k: expr) E xl efun tid
        (post: ~~ (at_locₛ 𝔅) → (Mask → (proph_asn → Prop)))
        (mask: Mask) Il ϝ' iκs γ q :
    AsVal k → IntoPlistc ql ql' →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) κl ++ E) L (fp_E (fp x) ϝ)) →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    (frac_tok γ q &&{Wguard}&&> @[lft_intersect_list κl]) -∗ Ltok γ L q -∗
    invctx_interp tid mask iκs (InvCtx Il ϝ' (fp_atomic_state (fp x))) -∗
    tctx_elt_interp tid (p ◁ fn fp spec) efun -∗
    tctx_interp tid (hzip_with (λ _ boxty q, q ◁ boxty)
      (box_typel (fp x).(fp_ityl)) ql') xl -∗
    ⟨π, (spec efun.2) post xl mask π⟩ -∗
    (∀(ret: val) (mask': Mask) w, Ltok γ L q -∗
      invctx_interp tid mask' iκs (InvCtx Il ϝ' (fp_atomic_state (fp x))) -∗
      tctx_elt_interp tid (ret ◁ own.box (fp x).(fp_oty)) w -∗
      ⟨π, post w mask' π⟩ -∗
      WP[alerus_wsat] k [of_val ret] [{ _, cont_postcondition }]) -∗
    WP[alerus_wsat] (call: p ql → k) [{ _, cont_postcondition }].
  Proof.
    move=> [k' <-]-> IctxAlv ToEfp.
    iIntros "#LFT #PROPH #UNIQ #E #Gguardsκl [#key tok] ii p ql Obs k".
    iApply fupdw_twpw_cont. iIntros "W".
    iDestruct (llftl_begin' with "LFT") as "B".
    iDestruct (bupdw_incl (W:=alerus_wsat) with "B") as "B'".
    iMod ("B'" with "W") as "[W (%ϝ & ϝtok & %ϝne)]".
    (* Read off what the external context gives, then put [L] back. *)
    iDestruct (Ltok_acc (W:=alerus_wsat) with "[$key $tok] W") as "[L →W]".
    iDestruct (ToEfp ϝ with "L") as "#EfpPre".
    iDestruct (lctx_ictx_alive_L_guards_ϝ _ _ _ _ _ IctxAlv with "L E")
      as "#Lguardsϝ'".
    iDestruct (lctx_ictx_alive_L_guards_list _ _ _ _ _ IctxAlv with "L E")
      as "#LguardsIl".
    iDestruct ("→W" with "L") as "[W [_ tok]]".
    (* Share the fraction for the call's lifetime. *)
    iDestruct (llftl_borrow_shared ϝ (gsrc_fml (GFrac γ q)) with "[tok]")
      as "Sh"; [by iApply gsrc_fml_sem_2|].
    iDestruct (bupdw_incl (W:=alerus_wsat) with "Sh") as "Sh'".
    iMod ("Sh'" with "W") as "[W [#fGuardsG0 ToG]]".
    iAssert (@[ϝ] &&{Wguard}&&> frac_tok γ q)%I as "#fGuardsG".
    { iApply (guard_rhs_iff (gsrc_fml_sem (GFrac γ q))). iApply "fGuardsG0". }
    iDestruct (guard_trans with "fGuardsG Gguardsκl") as "Borκl".
    iDestruct (guard_trans with "fGuardsG [] ") as "fGuardsL";
      [iApply (Ltok_guard_frac with "key")|].
    iDestruct ("EfpPre" with "[$E]") as "#Efp".
    { clear ToEfp. iClear "EfpPre". iClear "Gguardsκl".
      iInduction κl as [|κ κl] "IH"; [done|]=>/=.
      iSplit. { iApply (llftl_incl_trans with "Borκl []").
        iApply llftl_intersect_incl_l. }
      iApply "IH". iModIntro. iApply llftl_incl_trans; [done|].
      iApply llftl_intersect_incl_r. }
    iModIntro. iFrame "W".
    wp_bind p. iApply (twp_hasty with "p"). iIntros (?? _) "[gho %phys]".
    rewrite fn_gho. iDestruct "gho" as (fb kb bl e Hclosed) "[%Hrec #e]".
    inversion phys as [Eqv].
    have ->: (λ: ["_r"], Skip;; k' ["_r"])%E = (λ: ["_r"], Skip;; k' ["_r"])%V
      by unlock.
    iApply (twp_app_hasty_box [] with "ql")=>/=. iIntros (wl) "ityl".
    rewrite Hrec. wp_rec.
    iDestruct (invctx_interp_call Il ϝ' _ tid mask ϝ iκs with "[] [] ii")
      as (iκs') "[ii iiback]".
      { iApply (guard_trans with "fGuardsL Lguardsϝ'"). }
      { iApply (guard_trans with "fGuardsL LguardsIl"). }
    iApply ("e" with "LFT PROPH UNIQ Efp [ϝtok] ii [ToG k iiback] ityl Obs").
    { iSplitL; [|done]. iExists _. iSplit; [by rewrite/= left_id|].
      by iFrame "ϝtok". }
    rewrite cctx_interp_singleton. iIntros (v' [locret b] mask').
    inv_vec v'=> v'.
    iIntros "[(%& %Eq & ϝtok &_) _] Invctx [oty ?] Obs".
    rewrite/= left_id in Eq. rewrite -Eq. wp_rec.
    iApply fupdw_twpw_cont. iIntros "W".
    iDestruct (llftl_end' with "LFT ϝtok") as "End"; [done|].
    iDestruct (fupdw_incl_mask (W:=alerus_wsat) (E':=⊤) with "End") as "End'";
      [set_solver|].
    iMod ("End'" with "W") as "[W †ϝ]".
    iDestruct ("ToG" with "†ϝ") as "ToG'".
    iDestruct (bupdw_incl (W:=alerus_wsat) with "ToG'") as "ToG''".
    iMod ("ToG''" with "W") as "[W tok]".
    iDestruct (gsrc_fml_sem_1 (s := GFrac γ q) with "tok") as "tok".
    iModIntro. iFrame "W". do 2 wp_seq.
    iDestruct ("iiback" with "Invctx") as "Invctx".
    destruct b. iApply ("k" with "[$key $tok] Invctx oty Obs").
  Qed.

  Lemma type_call_iris {A 𝔄l 𝔅 ℭ} x xl κl post (mask: Mask)
      (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ)
      p ql ql' (k: expr) E efun tid γ q :
    AsVal k → IntoPlistc ql ql' →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) κl ++ E) [] (fp_E (fp x) ϝ)) →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    (frac_tok γ q &&{Wguard}&&> @[lft_intersect_list κl]) -∗ Ltok γ [] q -∗
    invctx_interp tid mask [] (InvCtx [] static (fp_atomic_state (fp x))) -∗
    tctx_elt_interp tid (p ◁ fn fp spec) efun -∗
    tctx_interp tid (hzip_with (λ _ boxty q, q ◁ boxty)
      (box_typel (fp x).(fp_ityl)) ql') xl -∗
    ⟨π, (spec efun.2) post xl mask π⟩ -∗
    (∀(ret: val) (mask': Mask) w, Ltok γ [] q -∗
      invctx_interp tid mask' [] (InvCtx [] static (fp_atomic_state (fp x))) -∗
      tctx_elt_interp tid (ret ◁ own.box (fp x).(fp_oty)) w -∗
      ⟨π, post w mask' π⟩ -∗
      WP[alerus_wsat] k [of_val ret] [{ _, cont_postcondition }]) -∗
    WP[alerus_wsat] (call: p ql → k) [{ _, cont_postcondition }].
  Proof.
    iIntros (???) "LFT PROPH UNIQ E #Guardsκl tok Invctx p ql Obs k".
    iApply (type_call_iris' [] with
      "LFT PROPH UNIQ E Guardsκl tok Invctx p ql Obs").
      - split.
        + unfold lctx_lft_alive. iIntros "_ _".
          setoid_rewrite static_alive_true. iApply guard_true.
        + intros κ Hnotin. simpl in Hnotin. rewrite elem_of_nil in Hnotin.
          contradiction.
      - done.
      - iIntros (???) "G I ret Obs". iApply ("k" with "G I ret Obs").
  Qed.

  Lemma type_call {A 𝔄l 𝔅 ℭl 𝔇l 𝔈l 𝔉 ℭ} x (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) p ql ql' k trx
      trk tri E L (C: cctx 𝔉) Il ϝ' (T: tctx ℭl) (T': tctx 𝔇l) (Tk: vec val 1 → tctx 𝔈l) :
    IntoPlistc ql ql' → Forall (lctx_lft_alive E L) L.*1 →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    tctx_extract_ctx E L (p ◁ fn fp spec +::
      hzip_with (λ _ boxty q, q ◁ boxty) (box_typel (fp x).(fp_ityl)) ql') T T' trx →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    k ◁cont{L, (InvCtx Il ϝ' (fp_atomic_state (fp x))), Tk} trk ∈ C →
    (∀ret: val, tctx_incl E L (ret ◁ own.box (fp x).(fp_oty) +:: T') (Tk [#ret]) tri) →
    ⊢ typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C T (call: p ql → k) (trx ∘
      (λ post '(trp -:: adl), λ mask π,
      let '(al, dl) := psep adl in
        (spec trp.2) (λ (b: ~~ (at_locₛ 𝔅)) mask π, tri (trk post) (b -:: dl) mask π) al mask π)).
  Proof.
    move=> ? Alv ???? InTk. iApply typed_body_tctx_incl; [done|].
    iIntros (?[? adπl]mask post iκs). move: (papp_ex adπl)=> [aπl[dπl->]].
    iIntros "#LFT #PROPH #UNIQ #E L I C /=(p & ql & T') Obs".
    iDestruct (lctx_lft_alive_tok_list with "L E") as "#Alv"; [done|].
    iApply fupdw_twpw_cont. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]". iModIntro. iFrame "W".
    iDestruct "tok" as "[#key tok]".
    iApply (type_call_iris' with
      "LFT PROPH UNIQ E [] [$key $tok] I p ql [Obs]"); [done|done|..].
    { iApply (guard_trans with "[] Alv"). iApply (Ltok_guard_frac with "key"). }
    { iApply proph_obs_eq; [|done]=>/= ?. by rewrite papp_sepl papp_sepr. }
    iIntros (ret mask' ?) "tok I ret Obs".
    iApply fupdw_twpw_cont. iIntros "W".
    iMod (proj2 (InTk _) _ _ _ (_-::_) with
      "LFT PROPH UNIQ E tok [$ret $T'] Obs W") as "[W (%& tok & Tk & Obs)]".
    iMod (Ltok_withdraw with "tok W") as "[W L]". iModIntro. iFrame "W".
    have ->: [ret: expr] = map of_val ([#ret]) by done.
    iApply ("C" with "[%//] L I Tk Obs").
  Qed.

  Lemma type_letcall {A 𝔄l 𝔅 ℭ ℭl 𝔇l 𝔈} x (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) p ql ql'
                     Il ϝ' (T: tctx ℭl) (T': tctx 𝔇l) b e trx tr E L (C: cctx 𝔈)
                     `{!IntoPlistc ql ql', !Closed (b :b: []) e, !Closed [] p} :
    TCForall (Closed []) ql → Forall (lctx_lft_alive E L) L.*1 →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    tctx_extract_ctx E L (p ◁ fn fp spec +::
      hzip_with (λ _ boxty q, q ◁ boxty) (box_typel (fp x).(fp_ityl)) ql') T T' trx →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    (∀ret: val, typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C
      (ret ◁ own.box (fp x).(fp_oty) +:: T') (subst' b ret e) tr) -∗
    typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C T (letcall: b := p ql in e) (trx ∘ (λ post '(trp -:: adl) mask π,
      let '(al, dl) := psep adl in (spec trp.2) (λ b mask π, tr post (b -:: dl) mask π) al mask π)).
  Proof.
    move=> Clql ????. iIntros "e". iApply type_cont_norec.
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

  (** Typing a function literal.

    VerusBelt proves the *recursive* rule [type_fnrec] by [iLöb] - tying the
    function's own specification back into its body - and derives [type_fn]
    from it by dropping the recursive hypothesis.  Löb induction is exactly
    what a total weakest precondition gives up, so [type_fnrec] is not
    ported, and [type_fn] is proved directly: a non-recursive body never
    needs its own specification. *)
  Lemma type_fn {A 𝔄l 𝔅 ℭ} tr (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ)
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
    typed_val (fn: bl := e)%V (fn fp spec)
      (@RecV BAnon ("return" :: bl)%binder e Cl, tr).
  Proof.
    move: Cl. rewrite Into. iIntros (Cl Body ????????) "_ _ _ _ $$ _ Obs".
    iApply twp_value.
    iExists -[((@RecV BAnon ("return" :: bl')%binder e Cl)%V, tr)].
    iFrame "Obs". iSplit; [|done]. iExists _, 0%nat.
    iSplit; [by rewrite/= decide_True_pi|]. iSplit; last by done.
    rewrite fn_gho. iExists BAnon, "return", bl', e, _. iSplit; [done|].
    iIntros "!>" (y ϝ k wl). iApply Body.
  Qed.
End typing.

Ltac simpl_fp_E := rewrite /fp_E /ty_outlives_E /=.

Global Hint Resolve elctx_sat_fp_E : lrust_typing.
Global Hint Resolve fn_resolve (* fn_subtype *) : lrust_typing.
