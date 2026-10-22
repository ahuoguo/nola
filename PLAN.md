# Porting AlerusBelt / VerusBelt into Nola, later-free

Branch `later-free-guard`.  Upstream: `verus-belt/src/`.  Keep Leaf's
guarding logic (`P &&{W}&&> Q`); drop `▷` and `iLöb`; use Nola's magic
derivability, `cif` formulas and explicit world satisfactions.  Replacing
the guards with Nola's own borrows is *not* the route.

Everything ported builds green (`make -f Makefile.coq -j4`).

## Where it stands

The model is **done**: `nola/alerus/typing/model.v` builds the `cif` model
of `typing/ctx.v`'s interface (`FML := cifOF CON`, `bor_sem := ⟦⟧ᶜ(der)`,
four judgments - the guard, the indexed borrow, the stored inclusion and
the borrow's alteration), `model_inst.v` bundles it into a `typeG` with the remaining
formula-language classes, and `soundness.v` allocates the world
satisfaction and proves both

> a closed, semantically well-typed program has no data race and no thread
> gets stuck  (`type_safety`, the original's conclusion)

and

> it **terminates**  (`type_soundness`)

The second is one the original cannot state: its weakest precondition is
partial, because a guard there hands out a `▷` that only a later credit
pays for.  `Print Assumptions` reports only `Eq_rect_eq` for both.

`typing/inst.v` then builds a concrete `CON` and `JUDG` **with their
semantics**, so neither theorem is vacuous; `alerus_type_soundness` and
`alerus_type_safety` are the concrete forms, and `Print Assumptions` gives
only `Eq_rect_eq` for those too.  Neither this development nor
`nola/examples/rust_halt/` had ever instantiated `sigTCT`/`sigTO` before.

Two checkable statements fix what is left:

* **`FnFml` is the only class in `typing/` with no instance anywhere.**  Its
  two fields, `fn_fml_sem_2` and `fn_incl_of_all`, are what an execution-level
  stratification has to supply - item 2 below.
* **`TypeContractive` has no instance either**, so `typing/fixpoint.v` is
  inert: it is a correct construction with nothing to apply it to, and its
  `Cofe (FML $oi Σ)` assumption is one the model cannot discharge - item 3.

File-by-file map to upstream: `nola/alerus/CORRESPONDENCE.md`.
Performance traps, four of which present as a hang: `nola/alerus/PERF.md`.

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

## Is the model concrete?  Yes, as of `af5aee0`

`model.v` gives the interpretation parametrically in `CON` and `JUDG`, as
`nola/examples/rust_halt/` does; `typing/inst.v` now builds the smallest
`CON` and `JUDG` satisfying the constraints **and their semantics**.
Neither development had ever instantiated `sigTCT`/`sigTO` before - they
appear nowhere in `nola/examples/`.

The obstruction was that `Jsem` would have had to be defined from itself.
Nola's construction order (thesis Def. 4.1) is

> `Csem` (from the `Ecsem`s) → `Jsem` (**applying** δ) → `Deriv`, `der`

and upstream holds to it everywhere: `⟦Px ⇒ Qx⟧δ = ⟦Px⟧δ -∗ |⇛ ⟦Qx⟧δ`
(§ 6.4).  The quantification over interpretations lives in the *lemmas* -
`Deriv_factor'`, `Deriv_map`, `bor_wand` - never inside the semantics.
`guardJT_sem` here already had that shape; `idxborJT_sem` and `inclJT_sem`
were instead made **constant** in δ, and the only way to make a guard
constant in δ is to quantify over every δ - which has to be restricted to
the *good* ones, which is `Deriv`, which is defined from `Jsem`.

Both offenders are gone: `st_incl` is a token, and `st_iff` quantifies over
every interpretation rather than the good ones.  See step 0 below for what
that cost.

## Next

The model is closed and both of the blockers that were open after it are
gone; what is written up in `nola/alerus/typing/inst.v` is the record of
how.  What remains is one small item and two large ones, and the two large
ones are large for reasons now understood rather than guessed at.

1. **A worked example** (in progress).  `typing/examples/basic.v` types two
   small programs against the rules, parametric in `CON`/`JUDG` exactly as
   `rust_halt/verify/` is.  Worth extending to a program that allocates,
   writes and frees a box, which exercises `own_ptr`, `type_assign` and
   `type_deref`, and to one that uses `uniq_subtype`, which exercises the
   relaxed borrow.  Beware the two traps in `nola/alerus/PERF.md`:
   `type_val` cannot be applied to a concrete program, and transformers must
   be built forward into an evar.

2. **`fn` must be stratified by an execution level** (thesis § 5, and (5.4)).
   `FnFml`'s `fn_fml_sem_2` and `fn_incl_of_all` have no model, so `fn` is
   the one type former the model does not interpret - which is why
   `soundness.v` is stated about a typing judgment, as `rust_halt`'s adequacy
   is.

   The device, from § 5.2: types carry a level `i`, and the function type's
   interpretation is a total Hoare triple whose *world satisfaction mentions
   only lower levels*,

   > `⟦T →ⱼ U⟧ᵢ v ≜ ∀u. [⟦T⟧ᵢ u] v(u) [⟦U⟧ᵢ] ∗_{k<j} Winv_k ⟦⟧*_k`   (5.4)

   which is well-formed because `k < j ≤ i`, so the recursion on the level
   is well-founded.  That is exactly what `fn_fml_sem_2` lacks: `Deriv_factor'`
   asks for `typed_body` at every candidate, and `typed_body` is stated at the
   ambient interpretation.

   The cost is the whole ghost-state layer: one copy of the formula
   machinery (`sinv`, the box, the borrows) per level up to a fixed maximum
   `L` - the thesis parameterises by `L` for the same reason, that Coq's
   global camera is finite (§ 5.2 fn. 3) - plus `FML`, `bor_sem`,
   `alerus_wsat` and `typed_body` indexed by level, and a level on every
   type former.  This is weeks, not days.

3. **`typing/fixpoint.v`** builds a recursive type as a COFE limit; a `cif`
   is complete as a `prost`, not an OFE, so it must move to
   `profix`/`Productive` (cf. `rust_halt/rec.v`, which is 145 lines because
   `ty` there is *pure data*).  Until then it assumes `Cofe (FML $oi Σ)`,
   which the model cannot discharge.

   The blocker is that `profix` needs `type 𝔄` to be a `prost`, and ours is a
   record with eight law fields.  It has to be split into data plus a `Ty`
   class, as `rust_halt` has it, which means rewriting every type former's
   `Program Definition` and adding `!Ty ty` to every lemma that quantifies
   over a type.  Note the file is currently inert: its own header records
   that no type former here is `TypeContractive`, because later-free
   `own_ptr` and `&shr` cannot hide a later.  So this buys recursive types,
   not a fix to a live path.

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
