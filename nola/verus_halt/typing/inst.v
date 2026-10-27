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

From nola.verus_halt.typing Require Export soundness.
From nola.verus_halt.typing Require Import function programs product base_type
  type_context shr_bor.
From nola.util Require Import productive cit.
From nola.verus_halt.lang Require Import races notation.
From nola.util Require Import tagged.
From nola.bi Require Import deriv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation.

(** ** The constructor signature *)
Variant verus_halt_consel :=
| acs_verus_halt | acs_naInv | acs_guard | acs_idxbor | acs_incl | acs_exs
| acs_pstore | acs_dinv | acs_eown.

Definition verus_haltCONF (s : verus_halt_consel) : cifcon :=
  match s with
  | acs_verus_halt => verus_haltCT | acs_naInv => naInvCT | acs_guard => guardCT
  | acs_idxbor => idxborCT | acs_incl => inclCT | acs_exs => exsCT
  | acs_pstore => pstoreCT | acs_dinv => dinvCT | acs_eown => eownCT
  end.

Definition verus_haltCON : cifcon := sigTCT verus_haltCONF.

#[export] Instance verus_haltC_CON : verus_haltC verus_haltCON :=
  sigTCT_inC (a := acs_verus_halt).
#[export] Instance naInvC_CON : naInvC verus_haltCON :=
  sigTCT_inC (a := acs_naInv).
#[export] Instance guardC_CON : guardC verus_haltCON :=
  sigTCT_inC (a := acs_guard).
#[export] Instance idxborC_CON : idxborC verus_haltCON :=
  sigTCT_inC (a := acs_idxbor).
#[export] Instance inclC_CON : inclC verus_haltCON :=
  sigTCT_inC (a := acs_incl).
#[export] Instance exsC_CON : exsC verus_haltCON :=
  sigTCT_inC (a := acs_exs).
#[export] Instance pstoreC_CON : pstoreC verus_haltCON :=
  sigTCT_inC (a := acs_pstore).
#[export] Instance dinvC_CON : dinvC verus_haltCON :=
  sigTCT_inC (a := acs_dinv).
#[export] Instance eownC_CON : eownC verus_haltCON :=
  sigTCT_inC (a := acs_eown).

#[export] Instance typingC_CON : typingC verus_haltCON :=
  TYPING_C _ _ _ _ _ _ _ _ _ _.

(** ** The judgment type *)
Variant verus_halt_jsel :=
  ajs_guard | ajs_idxbor | ajs_incl | ajs_iff | ajs_pstore | ajs_eown.

Definition verus_haltJUDGF Σ (s : verus_halt_jsel) : ofe :=
  match s with
  | ajs_guard => guardJT (cifO verus_haltCON Σ)
  | ajs_idxbor => idxborJT (cifO verus_haltCON Σ)
  | ajs_incl => inclJT | ajs_iff => iffJT (cifO verus_haltCON Σ)
  | ajs_pstore => pstoreJT (cifO verus_haltCON Σ)
  | ajs_eown => eownJT (cifO verus_haltCON Σ)
  end.

Definition verus_haltJUDG Σ : ofe := sigTO (verus_haltJUDGF Σ).

#[export] Instance guardJ_JUDG {Σ} :
  guardJ (cifO verus_haltCON Σ) (verus_haltJUDG Σ) := sigT_inJ (a := ajs_guard).
#[export] Instance idxborJ_JUDG {Σ} :
  idxborJ (cifO verus_haltCON Σ) (verus_haltJUDG Σ) := sigT_inJ (a := ajs_idxbor).
#[export] Instance inclJ_JUDG {Σ} : inclJ (verus_haltJUDG Σ) :=
  sigT_inJ (a := ajs_incl).
#[export] Instance iffJ_JUDG {Σ} :
  iffJ (cifO verus_haltCON Σ) (verus_haltJUDG Σ) := sigT_inJ (a := ajs_iff).
#[export] Instance pstoreJ_JUDG {Σ} :
  pstoreJ (cifO verus_haltCON Σ) (verus_haltJUDG Σ) := sigT_inJ (a := ajs_pstore).
#[export] Instance eownJ_JUDG {Σ} :
  eownJ (cifO verus_haltCON Σ) (verus_haltJUDG Σ) := sigT_inJ (a := ajs_eown).

#[export] Instance typingJ_JUDG {Σ} :
  typingJ verus_haltCON (verus_haltJUDG Σ) Σ := TYPING_J _ _ _ _ _ _ _ _ _.

(** ** How the semantics came to exist

  They do exist - [verus_haltCsem] and [verus_haltJsem] are below - but getting
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

    [guardJT_sem δ J := ⟦J.1⟧(δ) &&{verus_halt_WGuard_at δ}&&> ⟦J.2⟧(δ)]

  [idxborJT_sem] and [inclJT_sem] do not.  Both were made *constant* in δ,
  and the only way to make a guard constant in δ is to quantify over every δ:

    [st_incl κ κ' := □ ∀ δ, ⌜Deriv ⊤ δ⌝ → @[κ] &&{verus_halt_WGuard_at δ}&&> @[κ']]

  "Good" is [Deriv], [Deriv] is defined from [Jsem], and [st_incl] sits
  inside [idx_bor] = [idxborJT_sem].  Hence the cycle.

  *** The fix, in two parts

  Both parts are Nola's own, and neither costs the development anything it
  uses.  (A third change followed, on the stored borrow itself; see "The
  relaxed borrow" below.)

  (1) **[st_incl] drops the [⌜Deriv ⊤ δ⌝].**  The cycle is the
  *restriction*, not the family:

    [st_incl κ κ' := □ ∀ δ, @[κ] &&{verus_halt_WGuard_at δ}&&> @[κ']]

  mentions no [Deriv], so [Jsem] may be defined from it.  And nothing is
  lost, because the lifetime logic never needs an interpretation to be
  sound - every proof it has about a guard is parametric in [BorSem], which
  is why [st_sub_at], [st_glb_at], [eternal_incl_at] and
  [shr_tok_guard_at] in [model.v] all take an arbitrary [δ] already.

  An earlier version of this file made [st_incl] a **token** instead -
  [⌜κ' ⊆ κ⌝] together with a finite set of eternalized lifetimes - on the
  grounds that an unrestricted family "cannot be produced where a type's
  semantic equality is what produces it".  That was wrong, and the place it
  was wrong is exactly [st_incl_of_all]: a *semantic* inclusion is produced
  by [typing/function.v]'s [type_call_iris'], which creates a fresh [ϝ] for
  the call and guards its aliveness by the caller's local lifetime context,
  and a token cannot express that.  The token form survives as
  [eternal_incl_cif], which is what [st_incl_eternalize] produces and which
  implies the family; the family is what [AltSem] carries.

  The one thing the weakening costs is that every *producer* of a guard
  family has to produce it at every interpretation rather than at the good
  ones: [fguardx], [lctx_lft_alive_all], [guard_fml_borrow_shared] and
  [Ltok_guard_frac_at] are all stated over [alt_any].  Each was already
  proved that way.

  This closes [FnFml]'s [fn_incl_of_all], which is now the derived rule
  [dincl_fguardx] in [typing/ctx.v].  [fn_fml_sem_2] is left as the one
  field of the whole typing layer with no model, and it is the one the
  execution-level stratification has to supply.

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
Definition verus_haltCONF_ecsem {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ}
  (a : verus_halt_consel) : Ecsem (verus_haltCONF a) verus_haltCON (verus_haltJUDG Σ) Σ :=
  match a with
  | acs_verus_halt => verus_haltCT_ecsem | acs_naInv => naInvCT_ecsem
  | acs_guard => guardCT_ecsem | acs_idxbor => idxborCT_ecsem
  | acs_incl => inclCT_ecsem | acs_exs => exsCT_ecsem
  | acs_pstore => pstoreCT_ecsem | acs_dinv => dinvCT_ecsem
  | acs_eown => eownCT_ecsem
  end.

#[export] Instance verus_haltCsem {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  Csem verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigTCT_Csem (ecsem := verus_haltCONF_ecsem).

(** Each constructor's semantics is the one it was given, by [sigTCT_inCS] *)
#[export] Instance verus_haltCS_CON {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  verus_haltCS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigTCT_inCS (semec := verus_haltCONF_ecsem) (a := acs_verus_halt).
#[export] Instance naInvCS_CON {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  naInvCS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigTCT_inCS (semec := verus_haltCONF_ecsem) (a := acs_naInv).
#[export] Instance guardCS_CON {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  guardCS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigTCT_inCS (semec := verus_haltCONF_ecsem) (a := acs_guard).
#[export] Instance idxborCS_CON {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  idxborCS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigTCT_inCS (semec := verus_haltCONF_ecsem) (a := acs_idxbor).
#[export] Instance inclCS_CON {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  inclCS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigTCT_inCS (semec := verus_haltCONF_ecsem) (a := acs_incl).
#[export] Instance exsCS_CON {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  exsCS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigTCT_inCS (semec := verus_haltCONF_ecsem) (a := acs_exs).
#[export] Instance pstoreCS_CON {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  pstoreCS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigTCT_inCS (semec := verus_haltCONF_ecsem) (a := acs_pstore).
#[export] Instance dinvCS_CON {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  dinvCS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigTCT_inCS (semec := verus_haltCONF_ecsem) (a := acs_dinv).
#[export] Instance eownCS_CON {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  eownCS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigTCT_inCS (semec := verus_haltCONF_ecsem) (a := acs_eown).

(** The judgments' semantics, by cases on the judgment type.  Each one
  *applies* the interpretation - [guardJT_sem] to the two sub-formulas,
  [idxborJT_sem_at] to the borrow's alteration - and none quantifies over
  interpretations, which is why this is definable at all. *)
Definition verus_haltJUDGF_dsem {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ}
  (a : verus_halt_jsel) : Dsem (verus_haltJUDG Σ) (verus_haltJUDGF Σ a) (iProp Σ) :=
  match a with
  | ajs_guard => guardJT_dsem | ajs_idxbor => idxborJT_dsem
  | ajs_incl => inclJT_dsem | ajs_iff => iffJT_dsem
  | ajs_pstore => pstoreJT_dsem | ajs_eown => eownJT_dsem
  end.

#[export] Instance verus_haltJsem {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  Jsem (verus_haltJUDG Σ) (iProp Σ) :=
  sigT_dsem (verus_haltJUDGF Σ) (H := verus_haltJUDGF_dsem).

(** Each judgment's semantics is the one it was given, by [sigT_inJS] *)
#[export] Instance guardJS_JUDG {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  guardJS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigT_inJS verus_haltJUDGF_dsem (a := ajs_guard).
#[export] Instance idxborJS_JUDG {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  idxborJS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigT_inJS verus_haltJUDGF_dsem (a := ajs_idxbor).
#[export] Instance inclJS_JUDG {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  inclJS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigT_inJS verus_haltJUDGF_dsem (a := ajs_incl).
#[export] Instance iffJS_JUDG {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  iffJS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigT_inJS verus_haltJUDGF_dsem (a := ajs_iff).
#[export] Instance pstoreJS_JUDG {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  pstoreJS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigT_inJS verus_haltJUDGF_dsem (a := ajs_pstore).
#[export] Instance eownJS_JUDG {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  eownJS verus_haltCON (verus_haltJUDG Σ) Σ :=
  sigT_inJS verus_haltJUDGF_dsem (a := ajs_eown).

#[export] Instance typingCS_CON {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  typingCS verus_haltCON (verus_haltJUDG Σ) Σ :=
  {| typingCS_verus_halt := _; typingCS_naInv := _; typingCS_guard := _;
     typingCS_idxbor := _; typingCS_incl := _; typingCS_exs := _;
     typingCS_pstore := _; typingCS_dinv := _; typingCS_eown := _ |}.
#[export] Instance typingJS_JUDG {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  typingJS verus_haltCON (verus_haltJUDG Σ) Σ :=
  {| typingJS_guard := _; typingJS_idxbor := _; typingJS_incl := _;
     typingJS_iff := _; typingJS_pstore := _; typingJS_eown := _ |}.


(** ** Non-vacuity

  [typing/soundness.v]'s [type_soundness] and [type_safety] leave the four
  semantics existentially quantified, so they would say nothing if nothing
  satisfied them.  This is the witness: everything they ask for, at the
  concrete [CON] and [JUDG] above. *)
Definition verus_halt_sem {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ} :
  Csem verus_haltCON (verus_haltJUDG Σ) Σ * Jsem (verus_haltJUDG Σ) (iProp Σ) *
  typingCS verus_haltCON (verus_haltJUDG Σ) Σ * typingJS verus_haltCON (verus_haltJUDG Σ) Σ :=
  (verus_haltCsem, verus_haltJsem, typingCS_CON, typingJS_JUDG).

(** Supplying the four semantics to a typing derivation: the non-vacuity of
  [typing/soundness.v]'s two theorems, in the form a client needs it. *)
Lemma verus_halt_sem_intro {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ}
    {𝔅} (e : expr) (tr : predl_trans' [] 𝔅) :
  (⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx 𝔅) +[] e tr) →
  ∃ (_ : Csem verus_haltCON (verus_haltJUDG Σ) Σ) (_ : Jsem (verus_haltJUDG Σ) (iProp Σ))
    (_ : typingCS verus_haltCON (verus_haltJUDG Σ) Σ)
    (_ : typingJS verus_haltCON (verus_haltJUDG Σ) Σ),
  ⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx 𝔅) +[] e tr.
Proof.
  move=> big. by exists verus_haltCsem, verus_haltJsem, typingCS_CON, typingJS_JUDG.
Qed.

(** ** Soundness with the constraints discharged

  The same two statements for the concrete [CON] and [JUDG] above, with
  their semantics supplied, so that neither is vacuous. *)
Theorem verus_halt_type_soundness {Σ} `{!verus_haltGpreS (cifOF verus_haltCON) Σ}
    {𝔅} (e : expr) (tr : predl_trans' [] 𝔅) :
  (∀ post xl mask π, tr post xl mask π) →
  (∀ H : verus_haltGS (cifOF verus_haltCON) Σ,
    ⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx 𝔅)
        +[] e tr) →
  sn erased_step ([e], (∅, false)).
Proof.
  move=> Htr big.
  refine (type_soundness (CON := verus_haltCON) (JUDG := verus_haltJUDG Σ) e tr Htr _).
  move=> H. exists verus_haltCsem, verus_haltJsem, typingCS_CON, typingJS_JUDG.
  exact: big.
Qed.

Theorem verus_halt_type_safety {Σ} `{!verus_haltGpreS (cifOF verus_haltCON) Σ}
    {𝔅} (e : expr) (tr : predl_trans' [] 𝔅) t σ :
  (∀ post xl mask π, tr post xl mask π) →
  (∀ H : verus_haltGS (cifOF verus_haltCON) Σ,
    ⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx 𝔅)
        +[] e tr) →
  rtc erased_step ([e], (∅, false)) (t, σ) →
  nonracing_threadpool t σ ∧
    (∀ e', e' ∈ t → is_Some (to_val e') ∨ reducible e' σ).
Proof.
  move=> Htr big.
  refine (type_safety (CON := verus_haltCON) (JUDG := verus_haltJUDG Σ) e tr t σ
    Htr _).
  move=> H. exists verus_haltCsem, verus_haltJsem, typingCS_CON, typingJS_JUDG.
  exact: big.
Qed.

(** Both rest on nothing but the axiom Iris itself uses, now at a concrete
  constructor signature, judgment type and semantics. *)
Print Assumptions verus_halt_type_soundness.
Print Assumptions verus_halt_type_safety.

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

  This statement is at the concrete [verus_haltCON] because [cif] is where the
  [prost] lives; the development's [FML] is an abstract [oFunctor] and has
  none.  [nola/examples/rust_halt/rec.v] is specialised the same way. *)
Section productive.
  Context {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ}.

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
