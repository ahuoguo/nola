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
From nola.util Require Import tagged.
From nola.bi Require Import deriv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation.

(** ** The constructor signature *)
Variant alerus_consel :=
| acs_alerus | acs_naInv | acs_guard | acs_idxbor | acs_incl | acs_exs.

Definition alerusCONF (s : alerus_consel) : cifcon :=
  match s with
  | acs_alerus => alerusCT | acs_naInv => naInvCT | acs_guard => guardCT
  | acs_idxbor => idxborCT | acs_incl => inclCT | acs_exs => exsCT
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

#[export] Instance typingC_CON : typingC alerusCON :=
  TYPING_C _ _ _ _ _ _ _.

(** ** The judgment type *)
Variant alerus_jsel := ajs_guard | ajs_idxbor | ajs_incl.

Definition alerusJUDGF Σ (s : alerus_jsel) : ofe :=
  match s with
  | ajs_guard => guardJT (cifO alerusCON Σ)
  | ajs_idxbor => idxborJT (cifO alerusCON Σ)
  | ajs_incl => inclJT
  end.

Definition alerusJUDG Σ : ofe := sigTO (alerusJUDGF Σ).

#[export] Instance guardJ_JUDG {Σ} :
  guardJ (cifO alerusCON Σ) (alerusJUDG Σ) := sigT_inJ (a := ajs_guard).
#[export] Instance idxborJ_JUDG {Σ} :
  idxborJ (cifO alerusCON Σ) (alerusJUDG Σ) := sigT_inJ (a := ajs_idxbor).
#[export] Instance inclJ_JUDG {Σ} : inclJ (alerusJUDG Σ) :=
  sigT_inJ (a := ajs_incl).

#[export] Instance typingJ_JUDG {Σ} :
  typingJ alerusCON (alerusJUDG Σ) Σ := TYPING_J _ _ _ _ _ _.

(** ** The semantics, and why they cannot be given yet

  [Csem] is now free of [Jsem]: no [Ecsem] quantifies the interpretation, so
  the constructors' semantics mention [δ] only by applying it to a judgment.
  [Jsem] is not free of [Csem] - it cannot be - and that is fine; the
  problem is that it is not free of *itself*.

  [idxborJT_sem] is [idx_bor], which carries [StBor]'s [st_incl] and
  [st_iff], and both are families over the *good* derivability predicates:

    [st_incl κ κ' := □ ∀ δ, ⌜Deriv ⊤ δ⌝ → @[κ] &&{alerus_WGuard_at δ}&&> @[κ']]

  [Deriv] is defined from [Jsem], so [Jsem] would have to be defined from
  itself.  Dropping the [⌜Deriv ⊤ δ⌝] is what one would try next, and the
  closure rules survive it - [llftl_incl_sub], [eternal_tok_guard],
  [sinv_tok_guard], [guard_trans] all hold at every interpretation.  One
  source does not: [AltSem]'s [idxbor_fml_iff_at] takes an alteration that
  holds at every *candidate*, and its callers get it from a type's
  subtyping, whose proof for [&uniq{κ}] has to produce [δ J] and so needs
  [δ] to be good.

  What Nola does instead is worth spelling out, because it says exactly
  what would have to change.  Its borrow token

    [bor_tok α Px := [†α] ∨ ∃ α' i j, α ⊑□ α' ∗ bor_jtok i j α' (Px, Clsd) ∨ …]

  is plain ghost state: the lifetime inclusion [⊑□] is a *persistent token*
  rather than a guard, and there is **no alteration at all** - the formula
  [Px] sits in the ghost state, so a borrow of [Px] and a borrow of [Qx] are
  the same token exactly when [Px ≡ Qx].  [rust_halt] gets away with that
  because [ty_mutref] is invariant in its argument and its type equality is
  [≡] on [cif]s.  This port's [uniq_subtype] takes a *semantic* [eqtype],
  whose ghost component is a bi-implication of interpretations rather than
  an equality of formulas, and that is what forces [st_iff].

  So the fix is to put the stored things where Nola puts them - in a
  judgment at the *ambient* interpretation - and to let the lifetime logic
  take them as parameters.  Concretely:

  - a fourth judgment [iffJT], with
    [iffJT_sem δ (Px, Qx) := □ (⟦Px⟧ᶜ(δ) ↔ ⟦Qx⟧ᶜ(δ))];
  - [inclJT_sem δ (κ, κ') := @[κ] &&{alerus_WGuard_at δ}&&> @[κ']] - the
    *raw* guard at [δ], not the family;
  - [idxborJT_sem δ (κ, (sn, κ'), Px) := (@[κ] &&{W δ}&&> @[κ']) ∗
      ∃ Px', □ (⟦Px'⟧ᶜ(δ) ↔ ⟦Px⟧ᶜ(δ)) ∗ sinv_tok sn Px'] - likewise raw.

  Every one of the four mentions only [Csem], so [Jsem] is free of itself
  and the model exists.  [StBor] then supplies

    [st_idx κ idx Px := □ der (idxbor_j κ idx Px)]
    [st_incl κ κ'   := □ der (incl_j κ κ')]
    [st_iff Px Qx   := □ der (iff_j Px Qx)]

  - all three outside [Jsem], so [der] may appear in them - and
  [lifetime_full.v]'s [idx_bor] becomes [st_idx] rather than a record of
  parts.  [StBorSem] at a candidate [δ] that [der] maps into eliminates
  each by [dinto der δ], and creating one is [Deriv_factor'] at [der],
  whose obligation is the raw form at every candidate [der] maps into -
  which is exactly what [llftl_incl_sub], [sinv_tok_guard],
  [eternal_tok_guard] and [AltSem]'s [idxbor_fml_iff_at] premise give.

  The one thing to check while doing it is that the lifetime logic only
  ever opens a borrow at a candidate [der] maps into; [AltSem]'s
  [idxbor_fml_guard_into] already has that shape.

  Until that is done, the development stays parametric in [Csem] and
  [Jsem] exactly as [nola/examples/rust_halt/] does, and the constructor
  signature and judgment type above are as far as a concrete instance
  gets. *)
