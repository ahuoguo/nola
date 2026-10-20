# Porting AlerusBelt / VerusBelt into Nola, later-free

Branch `later-free-guard`.  Upstream: `verus-belt/src/`.  Keep Leaf's
guarding logic (`P &&{W}&&> Q`); drop `▷` and `iLöb`; use Nola's magic
derivability, `cif` formulas and explicit world satisfactions.  Replacing
the guards with Nola's own borrows is *not* the route.

Everything ported builds green (`make -f Makefile.coq -j4`).

## Where it stands

The model is **done**: `nola/alerus/typing/model.v` builds the `cif` model
of `typing/ctx.v`'s interface (`FML := cifOF CON`, `bor_sem := ⟦⟧ᶜ(der)`,
three judgments for the guard, the indexed borrow and the stored
inclusion), `model_inst.v` bundles it into a `typeG` with the remaining
formula-language classes, and `soundness.v` allocates the world
satisfaction and proves both

> a closed, semantically well-typed program has no data race and no thread
> gets stuck  (`type_safety`, the original's conclusion)

and

> it **terminates**  (`type_soundness`)

The second is one the original cannot state: its weakest precondition is
partial, because a guard there hands out a `▷` that only a later credit
pays for.  `Print Assumptions` reports only `Eq_rect_eq` for both.

File-by-file map to upstream: `nola/alerus/CORRESPONDENCE.md`.

## Not ported

| upstream | lines | why |
|---|---|---|
| `guarding/storage_protocol/` | 1382 | only needed by `typing/protocol.v` |
| `guarding/lib/rwlock.v` | 518 | client of the above |
| `typing/protocol.v` | 1189 | needs `storage_protocol/` |
| `typing/spawn.v` | 394 | `join` is an `iLöb` spin loop - no later-free version |

The rest of `guarding/` is here; the line counts shrink because Leaf's
later/`iLöb`/`pers` machinery disappears.  Nothing in the tree waits on a
missing guarding lemma, so pull in `storage_protocol/` when starting
`protocol.v`, not before.

## The one open hole: is the model concrete?

`model.v` gives the interpretation *parametrically* in `CON` and `JUDG`,
with constraint classes - exactly as `nola/examples/rust_halt/` does.
`typing/inst.v` tries to build the smallest `CON` and `JUDG` that satisfy
them.  The constructor signature and the judgment type come out fine, and
`Csem` is now free of `Jsem` (no `Ecsem` quantifies the interpretation).
`Jsem` is not free of *itself*:

> `idxborJT_sem` is `idx_bor`, which carries `StBor`'s `st_incl` and
> `st_iff`, and both are families over the **good** derivability
> predicates.  `Deriv` is defined from `Jsem`.

Dropping the goodness restriction is the obvious next move, and every
closure rule survives it - `llftl_incl_sub`, `eternal_tok_guard`,
`sinv_tok_guard`, `guard_trans` all hold at every interpretation.  One
source does not: `AltSem`'s `idxbor_fml_iff_at` takes an alteration that
holds at every *candidate*, and its callers get it from a type's subtyping,
whose proof for `&uniq{κ}` has to produce `δ J` and so needs `δ` to be
good.

Two routes out, written up in `inst.v`:

* make lifetime inclusion and the borrow's alteration **tokens**, as Nola's
  own lifetime logic does (`nola/iris/lft.v`: `lft_incl` is pure and `⊑□` a
  persistent token).  Every inclusion this model *creates* is structural or
  eternal - both token-shaped - except the one `type_call_iris'` builds
  from a shared borrow of a fraction;
* stratify, so that a judgment whose semantics quantifies over
  interpretations lives below the ones quantified over.

The second route is the same device the `fn` type needs (next section), so
the two open issues would close together: level-index the formula language
up to a fixed maximum `L`, give each level its own interpretation, and let
a level-`j` judgment quantify over the interpretations of levels `< j`.

Until one is done the development is at parity with `rust_halt`: sound and
parametric, with the satisfiability of its constraints open.

## Next

1. **`fn` must be stratified by an execution level** (thesis (5.4),
   § 3.4.1).  `FnFml`'s `fn_fml_sem_2` has no model and must not be
   discharged as it stands, so `fn` is the one type former the model does
   not interpret - which is why `soundness.v` is stated about a typing
   judgment, as `rust_halt`'s adequacy is.  `FML`, `bor_sem` and
   `alerus_wsat` become level-indexed up to a fixed maximum `L`, and a
   `type` carries the level of its ghost assertion.
2. **`typing/fixpoint.v`** builds a recursive type as a COFE limit; a `cif`
   is complete as a `prost`, not an OFE, so it must move to
   `profix`/`Productive` (cf. `rust_halt/rec.v`).  Until then it assumes
   `Cofe (FML $oi Σ)`, which the model cannot discharge.
3. **A worked example**, the way `rust_halt/verify/` has one: a concrete
   `CON`/`JUDG` and a small typed program run through `type_soundness`.

## Rules this port had to learn

Written out in `nola/alerus/typing/README.md`:

* a judgment can be eliminated at a candidate the ambient interpretation
  maps into, and introduced at every candidate from interpretation-free
  ghost state - but never *moved* between interpretations;
* anything to be *used* at a candidate must be the family of the things
  themselves, not of stored judgments (`fguardx`, `st_incl`, `st_iff`);
* a thing whose semantics ignores the candidate can be a formula with a
  `⊣⊢` at every candidate (`cif_idxbor`, `cif_incl`);
* a candidate is a *wrapped* `AlerusSem`: unwrapped it would shadow the
  ambient instance under every binder;
* `cif`'s own existential is capped at `cif_sel`'s universe, which is below
  the one `~~𝔄` lives in - hence `exs_fml` and its own constructor;
* seal anything that unfolds to `□ ∀ sem, …`, or typeclass search goes
  under the binder and build times go from seconds to minutes;
* ghost state is allocated before the interpretation and the interpretation
  handed in afterwards, because `bor_sem` is `⟦⟧ᶜ(der)` and its `Csem`
  mentions the ghost state;
* an allocation lemma should hand out the ghost *name*, not the record: a
  projection of an opaque record does not reduce, and the program logic has
  to recognise the instance it was given.
