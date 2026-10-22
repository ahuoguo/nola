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

0. ~~**Close the model.**~~  **Done**, in four steps; see
   `nola/alerus/typing/inst.v` for the write-up.

   a. `st_incl` is a token - every atom of `κ'` is supplied by `κ` or covered
      by one of a finite set of eternalized lifetimes - so it mentions no
      interpretation and reads at every candidate for free, as Nola's
      `lft_sincl` does.  `st_incl_of_all` moved to `FnFml` as
      `fn_incl_of_all`: its one use creates a fresh lifetime whose aliveness
      is guarded by the caller's context, which is neither shape a token
      records, and `rust_halt` has no counterpart because it has no function
      type.
   b. `Sync` is an equation of *formulas*, as `rust_halt` states it.  Every
      instance is then a congruence.  This is what (c) needs.
   c. `st_iff` quantifies over every interpretation rather than over the good
      ones, so `idx_bor` - which is `idxborJT_sem` - mentions no `Deriv`.
      The interface gains `alt_any`; the definitional `AltSem` fields read
      there.  The price is a premise on `uniq_subtype`.
   d. `Csem` by `sigTCT_Csem`, `Jsem` by `sigT_dsem`, and the six `inCS` and
      three `inJS` obligations with them.  `alerus_sem` bundles the four.

   **Not** done: restating `type_soundness`/`type_safety` concretely.
   Measured, each under a hard memory cap: the statement elaborates at the
   concrete `CON`/`JUDG` instantly; `refine` in place of `apply` is also
   instant; and `alerus_sem_intro`, whose existential is written out at the
   concrete signature, costs 487MB - so *supplying* the four semantics is
   cheap.  What is not is connecting the two, by `exists`, by `ex_intro`
   under `refine`, or by `exact`: that reached 9.1GB after 25 minutes
   without finishing, so the two existential types are not syntactically
   equal and conversion unfolds the whole `typeG`.  `Strategy opaque` on the
   signature, the judgment type and `typeG_cif` changes nothing.  Next thing
   to try: have `soundness.v` name `typeG_cif` explicitly rather than
   re-resolve it under the existential, so the terms are equal by
   construction.

   Also not removed: `uniq_subtype`'s premise.  It is reachable exactly when
   the two ghost assertions agree *as formulas* - `uniq_ghox_any_of_eq`,
   `uniq_subtype_eq`, `uniq_eqtype_eq` - and that is intrinsic, not a gap in
   the proof: a stored borrow's semantics is `□ δ (idxbor_j κ idx Px)`, and
   at a non-candidate `δ` is an arbitrary predicate.  Removing it means
   moving the alteration into the judgment's semantics, as
   `borrow_deriv.v`'s `bor` does over `bor_tok`, which needs `StBor` to lose
   `st_iff` and `lifetime_full.v`'s `idx_bor` with it.

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
3. ~~**A worked example**~~  **Started**:
   `nola/alerus/typing/examples/basic.v` types two small programs against
   the rules, parametric in `CON`/`JUDG` exactly as `rust_halt/verify/` is
   (upstream never applies `type_total` there either).  What it found:
   `programs.v`'s generic `type_val` cannot be applied to a concrete
   program - its conclusion has `let: xb := v in e` for a *value*, so
   unification has to invert `of_val ?v` against a literal and diverges.
   Each type's own rule (`type_int`, `type_bool`) applies first-order.  The
   same holds of any rule stated with `of_val`: pass the value explicitly
   and `simpl_subst` after each binder.  Worth extending with a program that
   allocates, writes and frees a box.

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
