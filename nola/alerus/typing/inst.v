(** * A concrete constructor signature and judgment type

  Nola itself - and [nola/examples/rust_halt/] with it - stays parametric in
  the constructor signature [CON] and the judgment type [JUDG], with
  constraint classes saying they *contain* what the development needs.  So
  does this port.  Nothing proves that those constraints are satisfiable,
  though, and a vacuous [typeG] would make [typing/soundness.v] say nothing.

  This file closes that: it builds the smallest [CON] and [JUDG] that
  satisfy them, as the dependent sums [sigTCT] and [sigTO] of the six
  constructor signatures and three judgment types the development declares,
  and gives every instance the typing layer asks for. *)

From nola.alerus.typing Require Export soundness.
From nola.alerus.typing Require Import function programs product base_type
  type_context shr_bor.
From nola.util Require Import productive cit.
From nola.alerus.lang Require Import races notation.
From nola.util Require Import tagged.
From nola.bi Require Import deriv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation.

(** ** The constructor signature *)
Variant alerus_consel :=
| acs_alerus | acs_naInv | acs_guard | acs_idxbor | acs_incl | acs_exs
| acs_pstore | acs_dinv.

Definition alerusCONF (s : alerus_consel) : cifcon :=
  match s with
  | acs_alerus => alerusCT | acs_naInv => naInvCT | acs_guard => guardCT
  | acs_idxbor => idxborCT | acs_incl => inclCT | acs_exs => exsCT
  | acs_pstore => pstoreCT | acs_dinv => dinvCT
  end.

Definition alerusCON : cifcon := sigTCT alerusCONF.

#[export] Instance alerusC_CON : alerusC alerusCON :=
  sigTCT_inC (a := acs_alerus).
#[export] Instance naInvC_CON : naInvC alerusCON :=
  sigTCT_inC (a := acs_naInv).
#[export] Instance guardC_CON : guardC alerusCON :=
  sigTCT_inC (a := acs_guard).
#[export] Instance idxborC_CON : idxborC alerusCON :=
  sigTCT_inC (a := acs_idxbor).
#[export] Instance inclC_CON : inclC alerusCON :=
  sigTCT_inC (a := acs_incl).
#[export] Instance exsC_CON : exsC alerusCON :=
  sigTCT_inC (a := acs_exs).
#[export] Instance pstoreC_CON : pstoreC alerusCON :=
  sigTCT_inC (a := acs_pstore).
#[export] Instance dinvC_CON : dinvC alerusCON :=
  sigTCT_inC (a := acs_dinv).

#[export] Instance typingC_CON : typingC alerusCON :=
  TYPING_C _ _ _ _ _ _ _ _ _.

(** ** The judgment type *)
Variant alerus_jsel :=
  ajs_guard | ajs_idxbor | ajs_incl | ajs_iff | ajs_pstore.

Definition alerusJUDGF Σ (s : alerus_jsel) : ofe :=
  match s with
  | ajs_guard => guardJT (cifO alerusCON Σ)
  | ajs_idxbor => idxborJT (cifO alerusCON Σ)
  | ajs_incl => inclJT | ajs_iff => iffJT (cifO alerusCON Σ)
  | ajs_pstore => pstoreJT (cifO alerusCON Σ)
  end.

Definition alerusJUDG Σ : ofe := sigTO (alerusJUDGF Σ).

#[export] Instance guardJ_JUDG {Σ} :
  guardJ (cifO alerusCON Σ) (alerusJUDG Σ) := sigT_inJ (a := ajs_guard).
#[export] Instance idxborJ_JUDG {Σ} :
  idxborJ (cifO alerusCON Σ) (alerusJUDG Σ) := sigT_inJ (a := ajs_idxbor).
#[export] Instance inclJ_JUDG {Σ} : inclJ (alerusJUDG Σ) :=
  sigT_inJ (a := ajs_incl).
#[export] Instance iffJ_JUDG {Σ} :
  iffJ (cifO alerusCON Σ) (alerusJUDG Σ) := sigT_inJ (a := ajs_iff).
#[export] Instance pstoreJ_JUDG {Σ} :
  pstoreJ (cifO alerusCON Σ) (alerusJUDG Σ) := sigT_inJ (a := ajs_pstore).

#[export] Instance typingJ_JUDG {Σ} :
  typingJ alerusCON (alerusJUDG Σ) Σ := TYPING_J _ _ _ _ _ _ _ _.

(** ** How the semantics came to exist

  They do exist - [alerusCsem] and [alerusJsem] are below - but getting
  there took two design changes, and the record of what blocked it is worth
  keeping, because the obstacle looked structural twice and was not.

  [Csem] was always free of [Jsem]: no [Ecsem] quantifies the
  interpretation, so the constructors' semantics mention [δ] only by
  applying it to a judgment.  [Jsem] was not free of *itself*, and the
  reason was a design choice of this port rather than anything forced.

  *** The shape Nola requires

  Definition 4.1 of the thesis (§ 4.3) builds [Deriv] and [der] from a
  judgment semantics [⟦⟧+_ : (Judg → iProp) → (Judg → iProp)] that must
  already exist.  So the construction order is

    [Csem] (from the [Ecsem]s)  →  [Jsem] (applying δ)  →  [Deriv], [der].

  Nola keeps to it everywhere.  Its judgment semantics *apply* δ and never
  quantify over it - [⟦Px ⇒ Qx⟧δ+ ≜ ⟦Px⟧δ -∗ |⇛ ⟦Qx⟧δ] (thesis § 6.4),
  [jiff], [jbupd].  The quantification over interpretations lives one layer
  up, in the *lemmas* - [Deriv_factor'], [Deriv_map], [bor_wand]'s
  [⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝] - never inside [⟦⟧+_].

  This port's [guardJT_sem] has exactly that shape:

    [guardJT_sem δ J := ⟦J.1⟧(δ) &&{alerus_WGuard_at δ}&&> ⟦J.2⟧(δ)]

  [idxborJT_sem] and [inclJT_sem] do not.  Both were made *constant* in δ,
  and the only way to make a guard constant in δ is to quantify over every δ:

    [st_incl κ κ' := □ ∀ δ, ⌜Deriv ⊤ δ⌝ → @[κ] &&{alerus_WGuard_at δ}&&> @[κ']]

  That quantification has to be restricted to the good candidates (an
  unrestricted one cannot be produced where a type's semantic equality is
  what produces it), "good" is [Deriv], [Deriv] is defined from [Jsem], and
  [st_incl] sits inside [idx_bor] = [idxborJT_sem].  Hence the cycle.

  *** The fix, in two parts

  Both parts are Nola's own, and neither costs the development anything it
  uses.  (A third change followed, on the stored borrow itself; see "The
  relaxed borrow" below.)

  (1) [st_incl] becomes a **token**.  Nola's persistent lifetime inclusion is
  [lft_sincl α β := [†α] ∨ [∞ lft_diff β α]] ([nola/iris/lft.v]) - plain
  ghost state, mentioning no interpretation, hence readable at every
  candidate for free.  The counterpart here is

    [st_incl κ κ' := ⌜κ' ⊆ κ⌝ ∨ ∃ κ0, ⌜κ' ⊆ κ ∪ κ0⌝ ∗ [∗ set] k ∈ κ0, eternal_tok k]

  and [st_incl_at] stops being a field of [AltSem]: it is derived by
  replaying [llftl_incl_sub] and [eternal_tok_guard] at the candidate's own
  [alt_WGuard sem], both of which are parametric in [BorSem].  This is sound
  because those two are the *only* sources of an inclusion in the whole
  typing layer - every [dincl] in [typing/] comes from [dincl_refl],
  [dincl_of_sub], [dincl_trans], [dincl_glb] or [st_incl_eternalize].

  The one casualty is [st_incl_of_all], which turns an arbitrary family into
  a storable inclusion.  It has exactly one use, [dincl_fguardx], which has
  exactly one use, [typing/function.v]'s [type_call_iris'] - and [function.v]
  is already the one file whose [AltSem] obligation ([fn_fml_sem_2]) has no
  model pending stratification.  So the two open issues still close together,
  but not for the reason previously recorded here.

  (2) [st_iff] moves **out of the borrow and into the δ layer**.  Nola's
  borrow token carries the formula literally and has no alteration at all,

    [bor_tok α Px := [†α] ∨ ∃ α' i j, α ⊑□ α' ∗ (bor_jtok i j α' (Px, Clsd) ∨ …)]

  and the alteration lives one layer up ([nola/iris/borrow_deriv.v]):

    [bor δ α Px := ∃ Qx, □ δ (jbupd Px Qx) ∗ □ δ (jbupd Qx Px) ∗ bor_tok α Qx]

  which is the thesis's [⟦bor^α P⟧δ ≜ ∃Q. δ(P⇒Q) ∗ δ(Q⇒P) ∗ bor^α Q] (§ 6.4,
  (6.4)).  The counterpart here is

    [idxborJT_sem δ κ idx Px := ∃ Px', □ δ (iff_j Px' Px) ∗ idx_bor_raw κ idx Px']

  with [idx_bor_raw] carrying only the token inclusion of (1) and a
  [sinv_tok].  [Jsem] then applies δ, and the construction order above goes
  through.

  Note that this does **not** cost [&uniq{κ}] its semantic type equality, as
  an earlier version of this comment claimed.  § 6.4 of the thesis is titled
  "Semantic Alteration by Derivability" precisely because [bor-alter],

    [δ(P⇒Q) ∗ δ(Q⇒P) ∗ ⟦bor^α P⟧δ ⊨ ⟦bor^α Q⟧δ],

  is supported.  [AltSem]'s [idxbor_fml_iff_at] simply takes the shape of
  [bor_wand]: the alteration is required at the candidates [sem'] with
  [alt_into sem sem'], not at every candidate.  Its callers all hold the
  unrestricted family already (it is what [type_incl] carries), and an
  unrestricted family discharges a restricted obligation, so every call site
  survives.  [nola/examples/rust_halt]'s [ty_mutref] never needs the
  alteration only because mutable references are invariant there.

  *** What the two moves really depend on

  Both are done, and the semantics below are concrete.  Move (1) made
  [st_incl] a token; move (2) dropped [⌜Deriv (λ _, True) δ⌝] from [st_iff],
  which is what takes [Deriv] - and with it [Jsem] - out of [idx_bor].

  What (2) cost is on the *introduction* side: [AltSem]'s
  [idxbor_fml_iff_at] wants the alteration at interpretations that are not
  candidates.  [Sync] therefore became an equation of formulas, as
  [nola/examples/rust_halt/type.v] has it, and [uniq_subtype] carries a
  premise that is discharged exactly when the two ghost assertions agree as
  formulas ([uniq_subtype_eq]).

  *** The relaxed borrow

  [idxbor_fml_iff_at] originally wanted its alteration at interpretations
  that are not candidates, which an [eqtype] cannot supply, and
  [uniq_subtype] carried a premise for it.  That was an artefact of how a
  borrow was stored, not of storing one.

  Upstream has semantic subtyping of [&mut] -
  [nola/examples/rust_halt/mutref.v]'s

    [subty_mutref : □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
       subty δ' T U id ∧ subty δ' U T id) ⊢ subty δ (ty_mutref α T) …]

  whose premise ranges over the *good* candidates only, and whose proof
  alters the borrow with [pbor_wand], premised on
  [⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝].  The mechanism is the stored
  constructor's [Ecsem]: [ty_mutref] stores [cif_pbor], and
  [nola/iris/pborrow_deriv.v] interprets it as the *relaxed* borrower,
  [∃ Qx, □ δ (jbupd Px Qx) ∗ □ δ (jbupd Qx Px) ∗ pbor_tok α Qx] - the
  thesis's § 6.4 - so the alteration is read at [δ] and [Deriv_map] reaches
  it.

  [idxborCT_ecsem] now has that shape, [dalter] carries the alteration at
  the ambient interpretation so it can be read *and* re-stored, and
  [uniq_subtype] takes an [lctx_lft_incl] and an [eqtype], nothing more.

  The borrow API did not have to be restated wholesale, as
  [nola/iris/borrow_deriv.v] does.  [dFullBor_exact] turns a relaxed full
  borrow back into an exact one under an update - open it atomically, carry
  the contents across the alteration, close at the formula wanted - so every
  existing [full_bor] lemma applies unchanged.  Only the lemmas that consume
  an [idx_bor] directly needed transported forms.

  *** A caveat about parity

  [nola/examples/rust_halt/] is parametric in [CON] and [JUDG] exactly as
  this port is, and never instantiates them either: [sigTCT] and [sigTO] are
  used nowhere in [nola/examples/].  For [rust_halt] the instantiation is
  mechanical, for the reason just given; here it took the changes above.
  With them done the gap is closed, and what follows is the instance. *)

(** ** The semantics

  With [st_incl] a token and [st_iff] quantifying over every interpretation
  rather than over the good ones, neither [idxborJT_sem] nor [inclJT_sem]
  mentions [Deriv], so the construction order of Definition 4.1 of the thesis
  goes through: [Csem] from the [Ecsem]s, then [Jsem] applying the
  interpretation, then [Deriv] and [der]. *)

(** The constructors' semantics, by cases on the signature *)
Definition alerusCONF_ecsem {Σ} `{!alerusGS (cifOF alerusCON) Σ}
  (a : alerus_consel) : Ecsem (alerusCONF a) alerusCON (alerusJUDG Σ) Σ :=
  match a with
  | acs_alerus => alerusCT_ecsem | acs_naInv => naInvCT_ecsem
  | acs_guard => guardCT_ecsem | acs_idxbor => idxborCT_ecsem
  | acs_incl => inclCT_ecsem | acs_exs => exsCT_ecsem
  | acs_pstore => pstoreCT_ecsem | acs_dinv => dinvCT_ecsem
  end.

#[export] Instance alerusCsem {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  Csem alerusCON (alerusJUDG Σ) Σ :=
  sigTCT_Csem (ecsem := alerusCONF_ecsem).

(** Each constructor's semantics is the one it was given, by [sigTCT_inCS] *)
#[export] Instance alerusCS_CON {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  alerusCS alerusCON (alerusJUDG Σ) Σ :=
  sigTCT_inCS (semec := alerusCONF_ecsem) (a := acs_alerus).
#[export] Instance naInvCS_CON {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  naInvCS alerusCON (alerusJUDG Σ) Σ :=
  sigTCT_inCS (semec := alerusCONF_ecsem) (a := acs_naInv).
#[export] Instance guardCS_CON {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  guardCS alerusCON (alerusJUDG Σ) Σ :=
  sigTCT_inCS (semec := alerusCONF_ecsem) (a := acs_guard).
#[export] Instance idxborCS_CON {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  idxborCS alerusCON (alerusJUDG Σ) Σ :=
  sigTCT_inCS (semec := alerusCONF_ecsem) (a := acs_idxbor).
#[export] Instance inclCS_CON {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  inclCS alerusCON (alerusJUDG Σ) Σ :=
  sigTCT_inCS (semec := alerusCONF_ecsem) (a := acs_incl).
#[export] Instance exsCS_CON {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  exsCS alerusCON (alerusJUDG Σ) Σ :=
  sigTCT_inCS (semec := alerusCONF_ecsem) (a := acs_exs).
#[export] Instance pstoreCS_CON {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  pstoreCS alerusCON (alerusJUDG Σ) Σ :=
  sigTCT_inCS (semec := alerusCONF_ecsem) (a := acs_pstore).
#[export] Instance dinvCS_CON {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  dinvCS alerusCON (alerusJUDG Σ) Σ :=
  sigTCT_inCS (semec := alerusCONF_ecsem) (a := acs_dinv).

(** The judgments' semantics, by cases on the judgment type.  Each one
  *applies* the interpretation - [guardJT_sem] to the two sub-formulas,
  [idxborJT_sem_at] to the borrow's alteration - and none quantifies over
  interpretations, which is why this is definable at all. *)
Definition alerusJUDGF_dsem {Σ} `{!alerusGS (cifOF alerusCON) Σ}
  (a : alerus_jsel) : Dsem (alerusJUDG Σ) (alerusJUDGF Σ a) (iProp Σ) :=
  match a with
  | ajs_guard => guardJT_dsem | ajs_idxbor => idxborJT_dsem
  | ajs_incl => inclJT_dsem | ajs_iff => iffJT_dsem
  | ajs_pstore => pstoreJT_dsem
  end.

#[export] Instance alerusJsem {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  Jsem (alerusJUDG Σ) (iProp Σ) :=
  sigT_dsem (alerusJUDGF Σ) (H := alerusJUDGF_dsem).

(** Each judgment's semantics is the one it was given, by [sigT_inJS] *)
#[export] Instance guardJS_JUDG {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  guardJS alerusCON (alerusJUDG Σ) Σ :=
  sigT_inJS alerusJUDGF_dsem (a := ajs_guard).
#[export] Instance idxborJS_JUDG {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  idxborJS alerusCON (alerusJUDG Σ) Σ :=
  sigT_inJS alerusJUDGF_dsem (a := ajs_idxbor).
#[export] Instance inclJS_JUDG {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  inclJS alerusCON (alerusJUDG Σ) Σ :=
  sigT_inJS alerusJUDGF_dsem (a := ajs_incl).
#[export] Instance iffJS_JUDG {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  iffJS alerusCON (alerusJUDG Σ) Σ :=
  sigT_inJS alerusJUDGF_dsem (a := ajs_iff).
#[export] Instance pstoreJS_JUDG {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  pstoreJS alerusCON (alerusJUDG Σ) Σ :=
  sigT_inJS alerusJUDGF_dsem (a := ajs_pstore).

#[export] Instance typingCS_CON {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  typingCS alerusCON (alerusJUDG Σ) Σ :=
  {| typingCS_alerus := _; typingCS_naInv := _; typingCS_guard := _;
     typingCS_idxbor := _; typingCS_incl := _; typingCS_exs := _;
     typingCS_pstore := _; typingCS_dinv := _ |}.
#[export] Instance typingJS_JUDG {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  typingJS alerusCON (alerusJUDG Σ) Σ :=
  {| typingJS_guard := _; typingJS_idxbor := _; typingJS_incl := _;
     typingJS_iff := _; typingJS_pstore := _ |}.


(** ** Non-vacuity

  [typing/soundness.v]'s [type_soundness] and [type_safety] leave the four
  semantics existentially quantified, so they would say nothing if nothing
  satisfied them.  This is the witness: everything they ask for, at the
  concrete [CON] and [JUDG] above. *)
Definition alerus_sem {Σ} `{!alerusGS (cifOF alerusCON) Σ} :
  Csem alerusCON (alerusJUDG Σ) Σ * Jsem (alerusJUDG Σ) (iProp Σ) *
  typingCS alerusCON (alerusJUDG Σ) Σ * typingJS alerusCON (alerusJUDG Σ) Σ :=
  (alerusCsem, alerusJsem, typingCS_CON, typingJS_JUDG).

(** Supplying the four semantics to a typing derivation: the non-vacuity of
  [typing/soundness.v]'s two theorems, in the form a client needs it. *)
Lemma alerus_sem_intro {Σ} `{!alerusGS (cifOF alerusCON) Σ}
    {𝔅} (e : expr) (tr : predl_trans' [] 𝔅) :
  (⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx 𝔅) +[] e tr) →
  ∃ (_ : Csem alerusCON (alerusJUDG Σ) Σ) (_ : Jsem (alerusJUDG Σ) (iProp Σ))
    (_ : typingCS alerusCON (alerusJUDG Σ) Σ)
    (_ : typingJS alerusCON (alerusJUDG Σ) Σ),
  ⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx 𝔅) +[] e tr.
Proof.
  move=> big. by exists alerusCsem, alerusJsem, typingCS_CON, typingJS_JUDG.
Qed.

(** ** Soundness with the constraints discharged

  The same two statements for the concrete [CON] and [JUDG] above, with
  their semantics supplied, so that neither is vacuous. *)
Theorem alerus_type_soundness {Σ} `{!alerusGpreS (cifOF alerusCON) Σ}
    {𝔅} (e : expr) (tr : predl_trans' [] 𝔅) :
  (∀ post xl mask π, tr post xl mask π) →
  (∀ H : alerusGS (cifOF alerusCON) Σ,
    ⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx 𝔅)
        +[] e tr) →
  sn erased_step ([e], (∅, false)).
Proof.
  move=> Htr big.
  refine (type_soundness (CON := alerusCON) (JUDG := alerusJUDG Σ) e tr Htr _).
  move=> H. exists alerusCsem, alerusJsem, typingCS_CON, typingJS_JUDG.
  exact: big.
Qed.

Theorem alerus_type_safety {Σ} `{!alerusGpreS (cifOF alerusCON) Σ}
    {𝔅} (e : expr) (tr : predl_trans' [] 𝔅) t σ :
  (∀ post xl mask π, tr post xl mask π) →
  (∀ H : alerusGS (cifOF alerusCON) Σ,
    ⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx 𝔅)
        +[] e tr) →
  rtc erased_step ([e], (∅, false)) (t, σ) →
  nonracing_threadpool t σ ∧
    (∀ e', e' ∈ t → is_Some (to_val e') ∨ reducible e' σ).
Proof.
  move=> Htr big.
  refine (type_safety (CON := alerusCON) (JUDG := alerusJUDG Σ) e tr t σ
    Htr _).
  move=> H. exists alerusCsem, alerusJsem, typingCS_CON, typingJS_JUDG.
  exact: big.
Qed.

(** Both rest on nothing but the axiom Iris itself uses, now at a concrete
  constructor signature, judgment type and semantics. *)
Print Assumptions alerus_type_soundness.
Print Assumptions alerus_type_safety.

(** ** [&shr{κ}] is productive

  This is the property the shared borrow was rebuilt for.  A recursive type
  guarded by [&shr{κ}] is [profix] of a map that must be [Productive], and
  over [cif] that is a *syntactic* condition: [proeqv] at level [k] compares
  a constructor's selector and data by equality, its [idom] children at
  level [k], and only its [cdom] children at level [< k].  So every mention
  of the borrowed type has to be a [cdom] child, and a [cdom] child is one an
  [Ecsem] may hand to [δ] as a judgment but never take the semantics of.

  [&shr{κ} ty] mentions [ty] in exactly two places, and after the rebuild
  each is in the right position: [ty_ghox] under [cif_guard] and
  [ty_gho_persx] under [cif_pstore].  The physical contents used to be a
  third, in [cif_cells]' *selector* - which [cit] compares by equality at
  every level, so it would have been fatal - and the definition writes
  [syn_phys] there instead, which [ty_phys_eq2] says is the same thing.

  This statement is at the concrete [alerusCON] because [cif] is where the
  [prost] lives; the development's [FML] is an abstract [oFunctor] and has
  none.  [nola/examples/rust_halt/rec.v] is specialised the same way. *)
Section productive.
  Context {Σ} `{!alerusGS (cifOF alerusCON) Σ}.

  Local Lemma proeqv_later_refl {PR : prost} k (a : PR) : proeqv_later k a a.
  Proof. destruct k as [|k]=>//=. Qed.

  (** [Citg] with no coinductive children and trivial data *)
  Local Ltac citg_ind :=
    apply Citg_preserv_productive;
      [|apply proeqv_later_refl|done].

  Lemma shr_bor_ghox_productive {𝔄} κ (ty ty' : type 𝔄) k x d g tid :
    (∀ y dd gg t,
      proeqv_later k (ty.(ty_ghox) y dd gg t) (ty'.(ty_ghox) y dd gg t)) →
    (∀ y dd gg t,
      proeqv_later k (ty.(ty_gho_persx) y dd gg t)
        (ty'.(ty_gho_persx) y dd gg t)) →
    proeqv k (st_ghox (shr_bor_st κ ty) x d g tid)
      (st_ghox (shr_bor_st κ ty') x d g tid).
  Proof.
    move=> Hgho Hpers. rewrite /= /by_ltx /by_lex.
    citg_ind. move=> dd /=.
    citg_ind. move=> b. destruct b=>/=; [reflexivity|].
    citg_ind. move=> gg /=.
    citg_ind. move=> b. destruct b=>/=; [reflexivity|].
    citg_ind. move=> ? /=.
    citg_ind. move=> b. destruct b=>/=.
    - reflexivity.
    - citg_ind. move=> b. destruct b=>/=.
      + apply cif_guard_productive; [apply proeqv_later_refl|]. apply Hgho.
      + apply cif_pstore_productive. apply Hpers.
  Qed.
End productive.

(** Productivity, like the two soundness theorems above, rests on nothing but
  [Eq_rect_eq] - which [sigTCT]/[sigTO] need for their dependent matches. *)
Print Assumptions shr_bor_ghox_productive.
