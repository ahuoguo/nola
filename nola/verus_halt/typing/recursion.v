(** * Recursion without Löb

  [typing/cont.v] and [typing/function.v] each leave out one upstream rule,
  and for the same reason: VerusBelt proves [type_cont] and [type_fnrec] by
  [iLöb], and a *total* weakest precondition has no Löb rule.  That is not an
  accident of the port.  Löb induction proves a loop safe without proving it
  terminates, which is exactly what totality is not allowed to do.

  This file is what replaces it, and the replacement is not a weaker Löb.  It
  is **well-founded recursion at the Coq level**, which is how
  [nola/examples/rust_halt/] already handles the matter: that development has
  neither a function type nor a continuation rule, and types the Ackermann
  function ([verify/ack.v]) by a nested [elim] on the arguments, unfolding
  each recursive call with its own [type_call].  A terminating loop needs a
  decreasing measure, and the measure may as well live in Coq.

  Three pieces, replacing the two [iLöb] rules the port does not have:

  - [type_pure] and [type_call_rec] - a pure step of the typing judgment, and
    the unfolding of a direct call to a [rec:] value.  [rust_halt]'s
    [type_call] is the second of these; this port had neither, which is why
    there was no way to type a recursive call at all.
  - [type_cont_wf] - the recursive continuation rule, with the Löb step
    replaced by [well_founded_induction] over a measure on the continuation's
    own arguments.  [typing/cont.v]'s [type_cont_norec] is the case where the
    continuation is never re-entered; this is the case where it is, and
    [typing/examples/loop.v] runs a loop through it.
  - [type_fnrec_wf] - the same for the *function type*, where the recursive
    occurrence is not a [rec:] value the body applies but an [f ◁ fn …] in
    its type context.  There the measure cannot live in the premise, because
    the body calls itself through the arrow; it lives in the arrow, which is
    handed to the body with its parameter range cut down to what is below
    the current argument.

  ** Where the measure lives

  A continuation's specification is a [predl_trans' 𝔅l ℭ], and its argument
  refinements [xl : plist indep_interp_of_syn_type 𝔅l] are *prophecy
  independent* - that is what [~~] means.  So a measure [μ] on them is an
  ordinary Coq function, and "this jump decreases" is an ordinary Coq
  proposition about the arguments rather than anything step-indexed.  That is
  the whole reason this works where Löb is unavailable: [cont_at] is what the
  body of the loop may assume about its arguments, [cont_lt] what a jump must
  establish, and the gap between them is one application of [R]. *)

From iris.proofmode Require Import coq_tactics reduction proofmode.
From nola.verus_halt.lang Require Import notation proofmode.
From nola.verus_halt.typing Require Import programs function own.
From nola.verus_halt.typing Require Export type ctx cont.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation WpwNotation.

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Section recursion.
  Context `{!typeG FML Σ}.

  (** ** Pure steps of the typing judgment

    [typed_body_at] ends in a weakest precondition and nothing else looks at
    the expression, so a pure step of the program is a pure step of the
    judgment.  Upstream never needs this because every rule it has mentions a
    concrete expression former; a recursive call is the one place where the
    step has to be taken on its own. *)
  Lemma type_pure_at {𝔄l 𝔅} (W : iProp Σ) E L (I: invctx) (C: cctx 𝔅)
      (T: tctx 𝔄l) φ n e e' tr :
    PureExec φ n e e' → φ →
    typed_body_at W E L I C T e' tr -∗ typed_body_at W E L I C T e tr.
  Proof.
    move=> ??. rewrite /typed_body_at.
    iIntros "body" (?????) "A B C D E F G H I".
    iDestruct ("body" with "A B C D E F G H I") as "twp".
    by eapply (tac_twp_pure []).
  Qed.
  Lemma type_pure {𝔄l 𝔅} E L (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) φ n e e' tr :
    PureExec φ n e e' → φ →
    typed_body E L I C T e' tr -∗ typed_body E L I C T e tr.
  Proof. apply type_pure_at. Qed.

  (** Unfolding a direct call of a [rec:] value - [rust_halt]'s [type_call]
    ([nola/examples/rust_halt/core.v]), at this port's judgment.

    This is the rule a recursive call goes through.  It is sound for the dull
    reason that the step is pure: no Löb, no level, nothing but [β]. *)
  Lemma type_call_rec_at {𝔄l 𝔅} (W : iProp Σ) E L (I: invctx) (C: cctx 𝔅)
      (T: tctx 𝔄l) e f xl erec (vl: list expr) erec' tr
      `{!AsRec e f xl erec, !TCForall AsVal vl,
        !Closed (f :b: xl +b+ []) erec, !DoSubstL (f :: xl) (e :: vl) erec erec'} :
    typed_body_at W E L I C T erec' tr -∗ typed_body_at W E L I C T (App e vl) tr.
  Proof. by iApply type_pure_at. Qed.
  Lemma type_call_rec {𝔄l 𝔅} E L (I: invctx) (C: cctx 𝔅)
      (T: tctx 𝔄l) e f xl erec (vl: list expr) erec' tr
      `{!AsRec e f xl erec, !TCForall AsVal vl,
        !Closed (f :b: xl +b+ []) erec, !DoSubstL (f :: xl) (e :: vl) erec erec'} :
    typed_body E L I C T erec' tr -∗ typed_body E L I C T (App e vl) tr.
  Proof. exact (type_call_rec_at _ E L I C T e f xl erec vl erec' tr). Qed.

  (** ** Recursive continuations, by well-founded recursion

    [μ] is the measure, read off the continuation's own argument refinements.
    [cont_at μ trk a] is what the loop body may *assume*: that its arguments
    really are the ones stage [a] names, beside the continuation's own
    specification.  [cont_lt R μ trk a] is what a jump must *establish*: that
    the arguments it hands in are at a stage strictly below [a].  The body is
    given the continuation at [cont_lt … a], so every jump it makes descends,
    and [R] being well founded is what turns that into termination. *)
  Definition cont_at {𝔅l ℭ A} (μ : plist indep_interp_of_syn_type 𝔅l → A)
    (trk : predl_trans' 𝔅l ℭ) (a : A) : predl_trans' 𝔅l ℭ :=
    λ post xl mask π, μ xl = a ∧ trk post xl mask π.
  Definition cont_lt {𝔅l ℭ A} (R : A → A → Prop)
    (μ : plist indep_interp_of_syn_type 𝔅l → A)
    (trk : predl_trans' 𝔅l ℭ) (a : A) : predl_trans' 𝔅l ℭ :=
    λ post xl mask π, R (μ xl) a ∧ trk post xl mask π.

  (** The rule.  Against [type_cont_norec] the only differences are that the
    body's own typing is a *Coq-level* entailment - it is replayed at every
    stage, which is what the Löb proof got from [□ ▷] - and that the
    continuation it may jump to is the one at [cont_lt], one stage down. *)
  Lemma type_cont_wf {A} (R : A → A → Prop) {𝔄l 𝔅l ℭ} bl
      (T': vec val (length bl) → tctx 𝔅l) μ trk (a0 : A)
      L' I' (T: tctx 𝔄l) kb ec e tr E L I (C: cctx ℭ) :
    well_founded R → Closed (kb :b: bl +b+ []) ec → Closed (kb :b: []) e →
    (∀ (a : A) (k: val) (vl: vec val (length bl)),
      ⊢ typed_body E L' I' (k ◁cont{L', I', T'} (cont_lt R μ trk a) :: C)
          (T' vl) (subst' kb k $ subst_v bl vl ec) (cont_at μ trk a)) →
    (∀k: val, typed_body E L I
      (k ◁cont{L', I', T'} (cont_lt R μ trk a0) :: C) T (subst' kb k e) tr) -∗
    typed_body E L I C T (letcont: kb bl := ec in e) tr.
  Proof.
    iIntros (Hwf ?? Hec) "He %tid %xl %mask %post %iκs
      #LFT #PROPH #UNIQ #E L I C T Obs".
    have ->: (rec: kb bl := ec)%E = of_val (rec: _ _ := _) by unlock.
    set k := (rec: kb bl := ec)%V.
    (** The continuation, at every stage, by well-founded recursion on the
      stage.  [C] is linear, but [cctx_interp] composes with [∧] rather than
      [∗], so the two branches below each get the whole of it. *)
    have Kont : ∀ a : A,
      ⊢ llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
        cctx_interp tid iκs post C -∗
        cctx_elt_interp tid iκs post
          (k ◁cont{L', I', T'} (cont_lt R μ trk a)).
    { apply (well_founded_induction Hwf)=> a IH.
      iIntros "#LFT' #PROPH' #UNIQ' #E' C %vl %xl' %mask' L'i I'i T'i #Obs'".
      iApply fupdw_twpw_cont. iIntros "W".
      iMod (proph_obs_sat ⊤ with "PROPH' Obs'") as %[π0 [Hlt _]]; [done|].
      iModIntro. iFrame "W". wp_rec.
      iApply (Hec (μ xl') k vl with "LFT' PROPH' UNIQ' E' L'i I'i [C] T'i").
      - rewrite cctx_interp_cons. iSplit; [|iExact "C"].
        iApply (IH (μ xl') Hlt with "LFT' PROPH' UNIQ' E' C").
      - iApply (proph_obs_impl with "Obs'")=>/= ?[_ ?]. by split. }
    wp_let. iApply ("He" $! k with "LFT PROPH UNIQ E L I [C] T Obs").
    rewrite cctx_interp_cons. iSplit; [|iExact "C"].
    iApply (Kont a0 with "LFT PROPH UNIQ E C").
  Qed.
End recursion.

(** * The same, for the function type

  [type_cont_wf] covers a loop, because a continuation's recursive
  occurrence is a [rec:] value the body applies directly.  A *function*
  that calls itself goes through its own function type instead:
  upstream's [type_fnrec] puts [f ◁ fn fp spec] in the body's type
  context and ties the knot with [iLöb].

  The well-founded version hands the body the arrow *restricted to
  arguments below the measure*, which is what makes the recursive call
  descend: calling it asks the caller for a proof of [R y x].  Cutting a
  parameter range down is [typing/function.v]'s [fn_body_specialize]'s
  business, and here it is the type itself that is cut. *)
Section fnrec.
  Context `{!typeG FML Σ} `{FnFml0 : !FnFml}.

  (** The parameter range below [x] *)
  Definition fp_lt {A 𝔄l 𝔅} (R : A → A → Prop) (fp : A → fn_params 𝔄l 𝔅)
    (x : A) : sig (λ y, R y x) → fn_params 𝔄l 𝔅 := λ y, fp (proj1_sig y).

  Lemma type_fnrec_wf {A 𝔄l 𝔅 ℭ} (R : A → A → Prop) tr j
      (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) fb e bl bl'
      `{Into: !IntoPlistc bl bl',
        Cl: !Closed (fb :b: ("return" :: bl)%binder +b+ []) e} :
    well_founded R →
    (∀ x ϝ (f: val) k (wl: plistc _ (boxl 𝔄l)),
        ⊢ typed_body_at (fn_wsat_lv j) (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
            (InvCtx [] ϝ (fp_atomic_state (fp x)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp x))),
              λ v: vec _ 1, +[vhd v ◁ own.box (fp x).(fp_oty)] } tr_ret]
            (f ◁ fn j (fp_lt R fp x) spec
              +:: hzip_with (λ _ boxty (v: val), v ◁ boxty)
                    (box_typel (fp x).(fp_ityl)) wl)
            (subst' fb f $ subst "return" k $ subst_plv bl' wl e)
            (λ post '(tr' -:: al), λ mask π,
              tr'.2 = tr ∧ spec tr post al mask π)%type) →
    typed_val (fnrec: fb bl := e)%V (fn j fp spec)
      (@RecV fb ("return" :: bl)%binder e Cl, tr).
  Proof.
    move: Cl. rewrite Into. iIntros (Cl Hwf Body).
    set f := (@RecV fb ("return" :: bl')%binder e Cl).
    (** [fn_gho_2], packaged over an arbitrary parameter range *)
    have Mk : ∀ (B : Type) (fq : B → fn_params 𝔄l 𝔅) d g tid,
      (∀ (z : B) ϝ k (wl : plistc _ (boxl 𝔄l)),
        ⊢ typed_body_at (fn_wsat_lv j) (fp_E (fq z) ϝ) [ϝ ⊑ₗ []]
            (InvCtx [] ϝ (fp_atomic_state (fq z)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fq z))),
              λ v: vec _ 1, +[vhd v ◁ own.box (fq z).(fp_oty)] } tr_ret]
            (hzip_with (λ _ boxty (v: val), v ◁ boxty)
              (box_typel (fq z).(fp_ityl)) wl)
            (subst' fb f $ subst "return" k $ subst_plv bl' wl e)
            (spec tr)) →
      ⊢ ty_gho (fn j fq spec) (f, tr) d g tid.
    { move=> B fq d g tid Hb. apply fn_gho_2. iStartProof.
      iExists fb, "return", bl', e, Cl. iSplit; [done|].
      iIntros "!>" (z ϝ k wl). iApply (Hb z ϝ k wl). }
    (** One unfolding of the body, given the arrow one stage down *)
    have Step : ∀ (x : A) ϝ k (wl : plistc _ (boxl 𝔄l)),
      (∀ d g tid, ⊢ ty_gho (fn j (fp_lt R fp x) spec) (f, tr) d g tid) →
      ⊢ typed_body_at (fn_wsat_lv j) (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
          (InvCtx [] ϝ (fp_atomic_state (fp x)))
          [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp x))),
            λ v: vec _ 1, +[vhd v ◁ own.box (fp x).(fp_oty)] } tr_ret]
          (hzip_with (λ _ boxty (v: val), v ◁ boxty)
            (box_typel (fp x).(fp_ityl)) wl)
          (subst' fb f $ subst "return" k $ subst_plv bl' wl e)
          (spec tr).
    { move=> x ϝ k wl Hgho. rewrite /typed_body_at.
      iIntros (tid2 xl mask post iκs) "LFT PROPH UNIQ Ei Li Ii Ci Ti Obs".
      iApply (Body x ϝ f k wl $! tid2 ((f, tr) -:: xl) mask post iκs
        with "LFT PROPH UNIQ Ei Li Ii Ci [Ti] [Obs]").
      - iSplitR "Ti"; [|iExact "Ti"].
        rewrite tctx_hasty_val. iExists 0%nat.
        iSplit; [iApply Hgho|done].
      - iApply (proph_obs_impl with "Obs")=>/= ??. by split. }
    (** The arrow at every parameter range below [x], by well-founded
      recursion on [x]: the body at [z] gets the arrow below [z], which
      is the induction hypothesis. *)
    have Gho : ∀ (x : A) d g tid,
      ⊢ ty_gho (fn j (fp_lt R fp x) spec) (f, tr) d g tid.
    { apply (well_founded_ind Hwf (λ x, ∀ (d g : nat) (tid : thread_id),
        ⊢ ty_gho (fn j (fp_lt R fp x) spec) (f, tr) d g tid)).
      move=> x IH d g tid.
      apply (Mk _ (fp_lt R fp x) d g tid)=> z ϝ k wl.
      apply (Step (proj1_sig z) ϝ k wl)=> d' g' tid'.
      exact (IH (proj1_sig z) (proj2_sig z) d' g' tid'). }
    (** And so at the full range *)
    iIntros (????????) "_ _ _ _ $$ _ Obs".
    iApply twp_value. iExists -[(f, tr)].
    iFrame "Obs". iSplit; [|done]. iExists _, 0%nat.
    iSplit; [by rewrite/= decide_True_pi|]. iSplit; last by done.
    iApply (Mk A fp)=> x ϝ k wl. exact (Step x ϝ k wl (Gho x)).
  Qed.

  (** At the ambient level, where an ordinary function lives.  The
    premise is a plain [typed_body], so the rules of [typing/] compose
    with it directly - the shape [typing/function.v]'s [type_fn_top]
    has. *)
  Lemma type_fnrec_top_wf {A 𝔄l 𝔅 ℭ} (R : A → A → Prop) tr
      (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) fb e bl bl'
      `{Into: !IntoPlistc bl bl',
        Cl: !Closed (fb :b: ("return" :: bl)%binder +b+ []) e} :
    well_founded R →
    (∀ x ϝ (f: val) k (wl: plistc _ (boxl 𝔄l)),
        ⊢ typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
            (InvCtx [] ϝ (fp_atomic_state (fp x)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp x))),
              λ v: vec _ 1, +[vhd v ◁ own.box (fp x).(fp_oty)] } tr_ret]
            (f ◁ fn fn_lv_top (fp_lt R fp x) spec
              +:: hzip_with (λ _ boxty (v: val), v ◁ boxty)
                    (box_typel (fp x).(fp_ityl)) wl)
            (subst' fb f $ subst "return" k $ subst_plv bl' wl e)
            (λ post '(tr' -:: al), λ mask π,
              tr'.2 = tr ∧ spec tr post al mask π)%type) →
    typed_val (fnrec: fb bl := e)%V (fn fn_lv_top fp spec)
      (@RecV fb ("return" :: bl)%binder e Cl, tr).
  Proof.
    move=> Hwf Body.
    apply (type_fnrec_wf R tr fn_lv_top fp spec fb e bl bl'
      (Into:=Into) (Cl:=Cl) Hwf).
    move=> x ϝ f k wl. rewrite typed_body_at_top. apply Body.
  Qed.

  (** And the check that the premise is dischargeable: [type_fn_top] is
    the case where the body never calls itself.  With [R] empty the
    recursive hypothesis is present and unused, and dropping it is
    [tctx_incl_resolve_head] - which is exactly how upstream derives
    [type_fn] from [type_fnrec]. *)
  Lemma type_fn_top_of_fnrec_wf {A 𝔄l 𝔅 ℭ} tr
      (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) e bl bl'
      `{Into: !IntoPlistc bl bl',
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
    apply (type_fnrec_top_wf (λ _ _, False) tr fp spec BAnon e bl bl'
      (Into:=Into) (Cl:=Cl)).
    { move=> ?. constructor. by move=> ?[]. }
    move=> x ϝ f k wl.
    iApply typed_body_impl; last first.
    { iApply typed_body_tctx_incl; [|iApply Body].
      apply tctx_incl_resolve_head. }
    by move=>/= ?[??]??[_ ?].
  Qed.
End fnrec.
