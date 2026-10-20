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
with constraint classes - as `nola/examples/rust_halt/` does.
`typing/inst.v` builds the smallest `CON` and `JUDG` satisfying them.  The
constructor signature and the judgment type come out fine, and `Csem` is
free of `Jsem`.  `Jsem` is not free of *itself*.

Nola's construction order (thesis Def. 4.1) is

> `Csem` (from the `Ecsem`s) → `Jsem` (**applying** δ) → `Deriv`, `der`

and it holds everywhere upstream: `⟦Px ⇒ Qx⟧δ = ⟦Px⟧δ -∗ |⇛ ⟦Qx⟧δ` (§ 6.4).
The quantification over interpretations lives in the *lemmas* -
`Deriv_factor'`, `Deriv_map`, `bor_wand` - never inside the semantics.
Our `guardJT_sem` has that shape.  `idxborJT_sem` and `inclJT_sem` were
instead made **constant** in δ, and the only way to make a guard constant in
δ is to quantify over every δ - which must be restricted to the *good* ones,
which is `Deriv`, which is defined from `Jsem`.  Hence the cycle.

**The fix is two moves, both Nola's own**, written out in `inst.v`:

1. `st_incl` becomes a **token**, as `lft_sincl α β := [†α] ∨ [∞ lft_diff β α]`
   is upstream.  `st_incl_at` then stops being a field and is *derived* by
   replaying `llftl_incl_sub` and `eternal_tok_guard` at the candidate's own
   world satisfaction - both are parametric in `BorSem`.  Sound because those
   two are the only sources of an inclusion in the whole typing layer.
2. `st_iff` moves **out of the borrow into the δ layer**, exactly as
   `bor δ α Px := ∃ Qx, □ δ (jbupd Px Qx) ∗ □ δ (jbupd Qx Px) ∗ bor_tok α Qx`
   is built on a token that carries no alteration.

Contrary to what this file said before, (2) does **not** cost `&uniq{κ}` its
semantic type equality: § 6.4 is *titled* "Semantic Alteration by
Derivability" and `bor-alter` is one of its rules.  `idxbor_fml_iff_at`
simply takes `bor_wand`'s shape - the alteration is wanted at the candidates
`sem'` with `alt_into sem sem'`, not at every candidate - and its callers all
hold the unrestricted family already.

The one casualty is `st_incl_of_all`.  It has one use (`dincl_fguardx`),
which has one use (`function.v`'s `type_call_iris'`) - and `function.v` is
already the file whose `AltSem` obligation has no model pending
stratification.  The two open issues still close together, for a different
reason than previously recorded.

**Not at parity with `rust_halt`.**  Neither development instantiates `CON`
and `JUDG` - `sigTCT`/`sigTO` appear nowhere in `nola/examples/`.  But for
`rust_halt` it is mechanical, because its types are formulas all the way
down (`ty_own, ty_shr : … → cif CON Σ`), so `Send`, `Sync` and type equality
are `≡` in the `cif` OFE with no interpretation anywhere:

```coq
send : ty_own T t d xπ vl ≡ ty_own T t' d xπ vl
```

We state them as `∀ sem, alt_sem sem → sem … ⊣⊢ sem …`, and that is what
pushes a family into `idx_bor`.  Adopting `≡` for `Send`/`Sync` - strictly
stronger, provable the same way by congruence - removes their dependence on
`idxbor_fml_iff_at` outright, leaving only `subtype`/`eqtype` on the
`bor_wand` shape.  Our `ty_shr` is still an `iProp`, not a formula; that is
the other half of the same divergence.

## Next

0. **Close the model.**  Four steps, in order; `lifetime_full.v` is not
   touched, because the lifetime logic is *instantiated at the candidate*
   rather than rewritten.

   a. `st_incl` becomes a token, per-atom:
      `st_incl κ κ' := ∃ E, ⌜κ' ⊆ κ ∪ E⌝ ∗ [∗ set] a ∈ E, eternal_tok {[a]}`.
      `st_incl_at` follows from `llftl_incl_sub` on `κ' ∩ κ` and a
      `llftl_incl_glb` fold of `eternal_tok_guard` over `κ' ∖ κ`.  Drop
      `st_incl_of_all`, and with it `dincl_fguardx` and the one use in
      `function.v`.
   b. `stBor_cif` takes the candidate: `st_iff := λ Px Qx, □ (⟦Px⟧ᶜ(δ) ↔
      ⟦Qx⟧ᶜ(δ))`, so `idxborJT_sem` **applies** δ instead of being constant
      in it.  `idxbor_fml_iff_at` takes `bor_wand`'s shape (`alt_into sem
      sem'`) and `idxbor_fml_guard_into` gains `alt_into alt_amb sem`; both
      call sites in `uniq_util.v` already have what that asks for.
   c. `inclJT` can go away entirely - a token needs no judgment, so
      `inclCT`'s `Ecsem` returns `st_incl` directly.
   d. `inst.v`'s `Csem` and `Jsem`, which are then mechanical: `sigTCT_Csem`
      from the `Ecsem`s, `sigT_dsem` from the two remaining judgments.

   Not needed, but worth doing afterwards: `Send`/`Sync` to `≡` on formulas,
   as `rust_halt` has them.  It is strictly stronger and removes their use of
   `idxbor_fml_iff_at` outright.
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
