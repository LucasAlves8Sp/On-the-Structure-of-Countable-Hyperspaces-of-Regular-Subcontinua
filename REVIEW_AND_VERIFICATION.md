# Review and verification

This file records the mathematical audit of the paper, the coverage of the paper by the Lean formalization, how the Lean proofs differ from the written proofs, and the checks run. The paper is the 20-page version of 11 November 2026, in `paper/`. The Lean development is in `lean/`; the logs are in [`lean/checks/`](lean/checks/).

## 1. Outcome

**Every numbered theorem, lemma, proposition and corollary of Sections 1 and 3–6 of the paper, and Proposition 7.5, is proved in Lean 4.** There is no `sorry` outside `Challenge.lean`, no added axiom and no hypothesis beyond those of the paper. The only axioms are Lean's standard three, `propext`, `Classical.choice` and `Quot.sound` (`lean/CheckAxioms.lean`). The answer to the question is

```lean
theorem RegularSubcontinua.no_continuum_with_regular_hyperspace_rat :
    ¬ ∃ (X : Type u) (_ : MetricSpace X) (_ : CompactSpace X)
      (_ : ConnectedSpace X), Nonempty (↥(regular X) ≃ₜ ℚ)
```

* **Size.** About 2,800 lines of proofs in 9 files, plus `Challenge.lean` (293 lines) and `Solution.lean`.
* **Not formalized.** Examples 7.1–7.3, the remarks, and Lemmas 2.3 and 2.4 as stated. So the theorems of the paper are formalized, not the whole paper.
* **The formalization found no mathematical gap.** No statement had to be changed; one hypothesis turned out to be unnecessary (Proposition 4.3(2) holds without countability).
* **Not yet done.** No human has refereed the paper, and no human has compared the Lean statements with the paper. The second task needs only `lean/Challenge.lean` and Section 2.

**What one must trust:** the Lean kernel; Mathlib's definitions of the objects in the statements (`NonemptyCompacts` and its topology, `closure`, `interior`, `IsConnected`, `IsCompact`, `IsGδ`, `IsCompletelyMetrizableSpace`, `Homeomorph`, `ℚ`, cardinals); and the 13 short definitions at the top of `lean/Challenge.lean`, listed in Section 2.

## 2. Coverage: paper → Lean

Paper: *On the structure of countable hyperspaces of regular subcontinua*, 20-page version of 11 November 2026. All Lean names are in the
namespace `RegularSubcontinua`. Statements are in `Challenge.lean`; the same
names are proved in `Solution.lean`; the proofs are in `RegularSubcontinua/`.

The status columns are independent:

- **Math**: re-derived in the pre-formalization audit (Section 5 below).
- **Compiles**: the statement is accepted by Lean.
- **Re-audited**: after compiling, the statement was read back against the
  paper (by the AI system that wrote it; no human has done this).
- **Proved**: a `sorry`-free proof compiles, `#print axioms` reports only
  `propext`, `Classical.choice`, `Quot.sound`, and the local Comparator run
  described in Section 4 accepted it.

### Results covered

| Paper result | Lean declaration (compared) | Proof in the library | Math | Compiles | Re-audited | Proved |
| --- | --- | --- | --- | --- | --- | --- |
| Lemma 3.2 | `card_eq_continuum_of_independent` | `card_of_independent` | yes | yes | yes | yes |
| Theorem 3.4 | `card_eq_continuum_of_blisters` | `card_of_blisters` | yes | yes | yes | yes |
| Lemma 4.1 | `complement_lemma` | `complement_lemma'` | yes | yes | yes | yes |
| Proposition 4.3 (1) | `isFiniteUnion_operations` | `IsFiniteUnion.union`, `isFiniteUnion_regDiff`, `isFiniteUnion_regMeet` | yes | yes | yes | yes |
| Proposition 4.3 (2) | `components_of_isFiniteUnion` | `components_of_isFiniteUnion'` | yes | yes | yes (note 1) | yes |
| Theorem 4.4 | `absorption` | `absorption'` | yes | yes | yes | yes |
| Corollary 4.5 | `minimal_disjoint_interior` | `minimal_disjoint_interior'` | yes | yes | yes | yes |
| **Lemma 4.6** | `decreasing_intersection` | `decreasing_intersection'` | yes | yes | yes | yes |
| **Theorem 5.1** | `dense_interior_minimal` | `dense_interior_minimal'` | yes | yes | yes | yes |
| Lemma 6.2 | `atomicFamily_basic` | `atomicFamily_basic'` | yes | yes | yes | yes |
| Proposition 6.3 (a) | `atomicFamily_coding` | `atomicFamily_coding'` | yes | yes | yes | yes |
| Proposition 6.3 (b) | `atomicFamily_open_of_mem`, `atomicFamily_discrete` | primed versions | yes | yes | yes | yes |
| Theorem 1.5 | `isGdelta_regular_of_isDAtomic` | `isGδ_regular_of_isDAtomic'` | yes | yes | yes | yes |
| Theorem 1.4 | `structure_theorem` | `structure_theorem'` | yes | yes | yes | yes |
| Theorem 1.2 | `main_theorem`, `not_homeomorphic_rat`, `no_continuum_with_regular_hyperspace_rat` | `main_theorem'`, `not_homeomorphic_rat'` | yes | yes | yes | yes |
| Corollary 6.5 | `dichotomy`, `dichotomy_exclusive` | `dichotomy'`, `not_countable_of_card_eq_continuum` | yes | yes | yes (note 2) | yes |
| Proposition 7.5 | `no_rational_chain` | `no_rational_chain'` | yes | yes | yes (note 3) | yes |
| (bridge, not in the paper) | `isRegSubcontinuum_iff_exists_mem_regular` | `isRegSubcontinuum_iff_exists` | n/a | yes | yes | yes |
| (sanity, not in the paper) | `countable_hypothesis_satisfiable` | `countable_regular_punit` | n/a | yes | yes | yes |

Lemma 4.6 and Theorem 5.1 are standalone Comparator targets.

Notes.

1. The paper states Proposition 4.3 under "D(X) countable". Part (2) does not
   need it: the Lean proof has no countability hypothesis. The compared
   statement keeps the hypothesis so that it matches the paper. The paper also
   assumes `F ≠ ∅`; the Lean statement does not need to, because the empty set
   has no components.
2. "Exactly one of the following holds" is two declarations: `dichotomy` (at
   least one holds) and `dichotomy_exclusive` (they exclude each other).
3. "No subset of D(X) is ordered by inclusion in the order type of ℚ" is
   stated as: there is no strictly monotone map `ℚ → Set X` whose values are
   regular subcontinua.
4. `countable_hypothesis_satisfiable` says that some metric continuum has
   countable `D(X)` (the one-point space). It is there only to show that the
   hypothesis of the main theorem is not contradictory. It is not Example 7.2.

### Preliminaries of Section 2

These are auxiliary. They are in the library, not in the compared surface.

| Paper | Lean | Status |
| --- | --- | --- |
| Lemma 2.2 (a) | `isRegularClosed_closure_sUnion`, `isRegularClosed_closure_iUnion` | proved |
| Lemma 2.2 (b) | `IsRegularClosed.inter_interior_nonempty`, `IsRegularClosed.interior_nonempty` | proved |
| Lemma 2.2 (c) | `IsRelClopen.isRegularClosed` | proved |
| Lemma 2.2 (d), (e), (f) | `isRegularClosed_regDiff`, `diff_subset_regDiff`, `regMeet_union_regDiff`, `regDiff_union_left`, `regDiff_regDiff`, `regMeet_eq_regDiff_regDiff`, and neighbours | proved |
| Lemma 2.3 | replaced by `finClopenCover_or_seq` and `FinClopenCover.components_spec` | **not formalized as stated** |
| Lemma 2.4 (boundary bumping) | none | **not formalized; not used by the Lean proofs** |
| Lemma 2.5 | `isPreconnected_iInter_of_antitone`, `isConnected_iInter_of_antitone` | proved |
| Lemma 2.6 | Mathlib, and `isClosed_setOf_subset` | proved |
| Lemma 2.7 (thinning) | `exists_thinning` | proved, in the form used by Theorem 3.4 |

### New claims of the paper that are NOT covered

| Paper item | Nature | Covered? | Reason |
| --- | --- | --- | --- |
| Example 7.3 (minimal element without absorption) | new example | **no** | Needs the buckethandle continuum and its indecomposability in Lean |
| Remark 3.3 (the arc has no independent family and no blister family) | new remark | **no** | Illustration; not needed by any theorem |
| Remark 1.3 (Hausdorff metric never complete on an infinite D(X)) | remark | **no** | Depends on Ordoñez 2018, Corollary 4.13, which is cited and not formalized |
| Remarks 3.5, 5.2, 6.4, 6.6, 7.4 | remarks | **no** | Commentary; 6.6 and 7.4 depend on cited results |
| Example 7.1 (arc) | elementary | **no** | Not a new result |
| Example 7.2 (null chain) | known (Ramírez Angarita) | **no** | Not a new result |

Consequence: the correct claim is **"every numbered lemma, proposition,
theorem and corollary of Sections 1 and 3 to 6, and Proposition 7.5, is
formalized; Examples 7.1 to 7.3, the remarks, and Lemmas 2.3 and 2.4 as stated
are not"**. The paper as a whole is therefore only partially formalized.

### Definitions

| Paper | Lean | Comment |
| --- | --- | --- |
| continuum | `[MetricSpace X] [CompactSpace X] [ConnectedSpace X]` | `ConnectedSpace` includes nonempty |
| `C(X)` | `Subcontinua X` | subtype of `TopologicalSpace.NonemptyCompacts X`; Vietoris topology = Hausdorff-metric topology by construction in Mathlib |
| regular closed | `IsRegularClosed` | `closure (interior s) = s` |
| regular subcontinuum (as a set) | `IsRegSubcontinuum` | compact, connected, regular closed |
| `D(X)` | `regular X : Set (Subcontinua X)` | subspace topology of `C(X)` |
| "D(X) countable" | `(regular X).Countable` | includes finite |
| independent family (Def. 3.1) | `IsIndependentOver` | |
| `F ⊖ G`, `F ∧ G` (Def. 2.1) | `regDiff`, `regMeet` | |
| `𝓕(X)` (Def. 4.2) | `IsFiniteUnion` | finite set of regular subcontinua; empty set allowed |
| components | `components F` | image of `connectedComponentIn F` |
| minimal element | `IsMinimalReg` | |
| atomic family, D-atomic (Def. 6.1) | `IsAtomicFamily`, `IsDAtomic` | disjointness of interiors not assumed |
| scattered | `IsScattered` | not found in Mathlib; defined here |
| `G_δ` | Mathlib `IsGδ (regular X)` | in the ambient space `Subcontinua X` |
| completely metrizable | Mathlib `TopologicalSpace.IsCompletelyMetrizableSpace` | |
| isolated point | `IsOpen {K}` | |
| homeomorphic to ℚ | `↥(regular X) ≃ₜ ℚ` | ℚ with its metric topology from `Mathlib.Topology.Instances.Rat` |

## 3. Architecture of the Lean development

This file replaces the earlier plan. It describes the proof development that
exists and compiles. Lean `v4.35.0-rc2`, Mathlib tag `v4.35.0-rc2`
(commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`).

### 3.1 Modules

| Module | Lines | Content |
| --- | --- | --- |
| `Challenge.lean` | statements | 13 definitions and 23 statements, each closed by `sorry`. Imports Mathlib only. |
| `RegularSubcontinua/Defs.lean` | 97 | The 13 definitions, copied verbatim from `Challenge.lean`. |
| `RegularSubcontinua/Basic.lean` | 404 | Regular closed sets (Lemma 2.2 (a)–(c)); connectedness through closed separations; nested intersections (Lemma 2.5); relatively clopen sets; the dichotomy that replaces Lemma 2.3. |
| `RegularSubcontinua/Counting.lean` | 377 | Thinning (Lemma 2.7); the bridge between sets and points of `regular X`; `#(regular X) ≤ 𝔠`; **Lemma 3.2**; **Theorem 3.4**. |
| `RegularSubcontinua/Complement.lean` | 440 | Lemma 2.2 (d)–(f); **Lemma 4.1**; **Proposition 4.3**; **Theorem 4.4**; **Corollary 4.5**. |
| `RegularSubcontinua/Decreasing.lean` | 222 | **Lemma 4.6**. |
| `RegularSubcontinua/Density.lean` | 526 | **Theorem 5.1**. |
| `RegularSubcontinua/Atomic.lean` | 297 | **Lemma 6.2**; **Proposition 6.3**; Lemma 2.6 (a); **Theorem 1.5**. |
| `RegularSubcontinua/Main.lean` | 298 | `C(X)` is closed in the hyperspace of compact sets; a `G_δ` subset of a Polish space is Polish; countable completely metrizable spaces are scattered; **Theorem 1.4**; **Theorem 1.2**; **Proposition 7.5**; the one-point space has countable `D(X)`. |
| `RegularSubcontinua/Dichotomy.lean` | 119 | `D(X)` is Borel in `C(X)`; perfect set property for `D(X)`; **Corollary 6.5**. |
| `Solution.lean` | restatements | The 23 statements of `Challenge.lean` under the same names, each proved by one call to the library. |

Import order: `Defs → Basic → Counting → Complement → Decreasing → Density →
Atomic → Main → Dichotomy`.

### 3.2 Where the Lean proofs differ from the written proofs

The Lean development proves the *statements* of the paper. It does not follow
every written proof step by step. The differences are listed here so that
nobody reads the kernel check as a certificate of the paper's text.

1. **Boundary bumping (Lemma 2.4) is not formalized and not used.** Wherever
   the paper uses it (Lemma 4.6), the Lean proof argues directly with closed
   separations: a closed set is connected iff it is not the union of two
   disjoint nonempty closed sets (`isPreconnected_of_closed_sep`,
   `IsPreconnected.subset_or_subset_of_closed`).
2. **Lemma 2.3 (components of a compact metric space) is replaced.** The Lean
   proof uses one dichotomy for a closed set `R`
   (`finClopenCover_or_seq`): either `R` is a finite union of connected
   relatively clopen sets, or `R` contains infinitely many pairwise disjoint
   nonempty relatively clopen sets. The first alternative identifies the
   components (`FinClopenCover.components_spec`); the second feeds the
   independent-family and blister arguments. No use is made of "components
   equal quasi-components".
3. **Theorem 5.1 uses different bookkeeping.** The paper builds a tree of
   finite ordered covers by cells and argues with branches. The Lean proof
   builds a sequence of *levels*, where a level is a finite set of *gaps*
   `(P, P')` (`IsLevel`): `P ⊆ P'`, `P` is empty or a regular subcontinuum,
   `P'` is a regular subcontinuum, the cell `regDiff P' P` is a regular
   subcontinuum, the cells cover `X`, and any two gaps are ordered
   (`g.2 ⊆ h.1` or `h.2 ⊆ g.1`). Refinement by a regular subcontinuum `D` is
   `exists_refinement`; it uses Proposition 4.3 and the peeling lemma
   `exists_peel`. Branches are counted by the map sending a branch to the
   closure of the union of its lower ends, which is at most two-to-one, and
   Lemma 4.6 and Baire category finish the proof as in the paper.
4. **Cardinality.** `#(regular X) ≤ 𝔠` is proved from second countability of
   `regular X` (a `T₀` second countable space injects into the power set of a
   countable base), not from `|C(X)| ≤ 𝔠`.
5. **Proposition 4.3 (2) does not use countability.** The Lean proof
   (`components_of_isFiniteUnion'`) has no countability hypothesis. The
   compared statement keeps the hypothesis so that it matches the paper.
6. **Corollary 6.5.** The paper cites Ramírez Angarita, Teorema 2.0.2, for
   "`D(X)` is Borel". The Lean development proves it
   (`measurableSet_regular`): `K` is regular iff for every `m` there are
   finitely many basic open sets contained in `K` whose `1/(m+1)`-thickenings
   cover `K`.

### 3.3 Mathlib results the development relies on

| Need | Mathlib |
| --- | --- |
| Hyperspace of nonempty compact sets, Vietoris topology | `TopologicalSpace.NonemptyCompacts`, `NonemptyCompacts.isOpen_subsets_of_isOpen`, `isOpen_inter_nonempty_of_isOpen`, `isClosed_subsets_of_isClosed`, `isClosed_inter_nonempty_of_isClosed` |
| Compactness, second countability of the hyperspace | instances in `Topology/Sets/VietorisTopology.lean` |
| Separation of disjoint compact sets | `SeparatedNhds.of_isCompact_isCompact` |
| Baire category | `nonempty_interior_of_iUnion_of_closed`, `dense_iUnion_interior_of_closed` |
| Polish spaces | `IsOpen.polishSpace`, `IsClosed.polishSpace`, `Topology.IsClosedEmbedding.polishSpace` |
| Perfect set property (closed sets) | `IsClosed.exists_nat_bool_injection_of_not_countable` |
| Borel sets are clopen in a finer Polish topology | `MeasurableSet.isClopenable'` |
| Disjoint open sets in a separable space | `Set.PairwiseDisjoint.countable_of_isOpen` |
| Cardinal arithmetic | `Cardinal.mk_set_nat`, `Cardinal.aleph0_lt_continuum`, `Cardinal.lift_mk_le'` |
| `ℝ` is uncountable | `Mathlib.Analysis.Real.Cardinality` |

Built in this repository because no Mathlib version was found by text search:
regular closed sets; scattered spaces; a `G_δ` subset of a Polish space is
Polish (`polishSpace_of_isGδ`); the connected members of
`NonemptyCompacts X` form a closed set (`isClosed_setOf_isConnected`); the
intersection of a decreasing sequence of compact connected sets is connected
(`isPreconnected_iInter_of_antitone`).

### 3.4 What is not formalized

See Section 2, the table of items not covered: Examples 7.1 to 7.3 and the
remarks. Example 7.3 would need the Knaster buckethandle continuum and a proof
that it is indecomposable; neither was found in Mathlib.

## 4. Verification performed

Output of the commands run on 11 November 2026 on the sources in this
repository, in a cloud container (Linux x86_64). Long build output is filtered
to warnings and errors; nothing else was edited.

| File | Command | Result |
| --- | --- | --- |
| `versions.txt` | `lean --version`, `lake --version`, Mathlib commit | Lean 4.35.0-rc2; Mathlib `0653561` |
| `lake-build.txt` | `lake build` | Build completed successfully. 41 warnings: 23 are the intended `sorry` of `Challenge.lean`, the rest are style linters. |
| `forbidden-constructs.txt` | `grep` for `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern` in `Solution.lean` and the library | No match. |
| `axioms.txt` | `#print axioms` for each of the 23 compared theorems | Each: `propext`, `Classical.choice`, `Quot.sound`. |
| `source-checks.txt` | `lean/scripts/check-lean-sources.py`, `lean/scripts/validate-formalization.rb`, line counts | Both exit 0. |
| `comparator-no-sandbox.txt` | `lake comparator --inadvisably-no-sandbox`, with nanoda and con-ron | "Your solution is okay!" |
| `comparator-no-sandbox-paranoid.txt` | the same with `--paranoid` | "Your solution is okay!" (Lean default and paranoid kernels, lean4lean, nanoda, con-leche, con-ron) |
| `comparator-negative-control.txt` | the same on a deliberately altered `Solution.lean` | Rejected, as expected. |

### What these logs are not

- **Not the sandboxed Comparator runs.** Palomar's own sandboxed verification
  of commit `959fb91` passed on 11 November 2026. Before that, CI ran one: the job
  "Check statement against solution" ran `lean/scripts/verify-comparator.sh` with
  `bubblewrap` on commit `49a57d8` and accepted the solution
  (https://github.com/LucasAlves8Sp/On-the-Structure-of-Countable-Hyperspaces-of-Regular-Subcontinua/actions/runs/43079572098).
  Locally, `bubblewrap` was not installed, so every
  Comparator run used `--inadvisably-no-sandbox`, and Comparator itself prints
  "this run is not trustworthy" for such runs.
- **Not a fresh-checkout build.** The build directory was reused across the
  session, and Mathlib was compiled from source because its cache server could
  not be reached. CI did build from a fresh checkout, with the Mathlib
  cache.
- **Not CI.** These logs were made before the first push. CI results are in the
  Actions tab of the repository.

`lake-build.txt`, `axioms.txt`, `forbidden-constructs.txt`, `source-checks.txt` and
`comparator-no-sandbox.txt` were made in this `lean/` folder after the repository was
reorganised. `comparator-no-sandbox-paranoid.txt` and `versions.txt` were made on the same
Lean sources at the repository root, before the move; `comparator-negative-control.txt` was
made before a comment-only change to the header of `Challenge.lean` (new title of the paper).

## 5. Mathematical audit

Audited text: the paper, 19-page version of 11 November 2026, then titled
"The hyperspace of regular subcontinua is never homeomorphic to the rationals".
The current 20-page version differs from it only in the title, the abstract, and
the two unnumbered sections at the end (formalization, AI declaration).
Auditor: Claude Fable 5.2 (AI), 11 November 2026. This is the same system that
wrote much of the paper, so it is a re-derivation, not an independent review.
No human referee has examined the proofs.

Sections 5.1 to 5.5 are the audit made **before** any Lean code was written and
are kept as they were. Section 5.6 records what the formalization found
afterwards.

Result classes: **V** = every inference re-derived and found valid;
**V\*** = valid, but the written proof needs a more explicit form in Lean
(listed in Section 5.3); **K** = known result, cited; **OUT** = not audited to
formalization standard.

### 5.1 Dependency graph

```
2.2 regular closed sets ──┬─────────────► 3.2 independent families ──► 4.1 complement lemma ──┬─► 4.4 absorption ─► 4.5
2.3 components ───────────┤                                                                   └─► 4.3 algebra 𝓕(X)
2.5 nested intersections ─┼─► 3.4 blister theorem ◄── 2.7 thinning                                    │
2.4 boundary bumping ─────┴───────────────────────────────► 4.6 decreasing intersections ◄────────────┘
                                                                     │
4.3, 4.6, 2.5, Baire category ──────────────────────────────► 5.1 density
4.4, 4.5, 5.1, 6.2 ─────────────────────────────────────────► 1.4 structure theorem
6.1 definition ─► 6.2 ─► 6.3
2.6 hyperspace facts, 6.2, 2.2(a) ──────────────────────────► 1.5 atomic ⇒ G_δ
1.4, 1.5, [G_δ ⇒ completely metrizable], Baire category ────► 1.2 main theorem
1.2, 1.4, [D(X) is Borel], [perfect set property] ──────────► 6.5 dichotomy
2.2(a) ─────────────────────────────────────────────────────► 7.5 scattered chains
```

Bracketed items are external facts. There is no cycle. The theorem that some
minimal element is isolated, and the funnel theorem, are not in the paper and
not in this graph.

### 5.2 Status of every statement

| Result | Class | Notes |
| --- | --- | --- |
| Lemma 2.2 (a)–(f) | V | Each identity re-derived. (f) uses that `G`, `G₁`, `G₂` are closed. |
| Lemma 2.3 (a)–(c) | V | (a) rests on components = quasi-components in compact Hausdorff spaces. |
| Lemma 2.4 boundary bumping | V | Checked that the clopen set `V` is open in `Z` (open in `cl W` and inside `W`). |
| Lemma 2.5 | K | Standard. |
| Lemma 2.6 | V | |
| Lemma 2.7 thinning | V | |
| Lemma 3.2 | V | Upper bound uses `|C(X)| ≤ 𝔠`. |
| Remark 3.3 (arc) | V | **Corrected in the paper**, see 5.4 below. |
| Theorem 3.4 blister | V | Covering claim (1) and the regularity step re-derived. |
| Lemma 4.1 | V | Part (2) needs `A ∪ B = A ∪ R`; checked. |
| Proposition 4.3 | V\* | Cases `F = ∅`, `G = ∅` are implicit. |
| Theorem 4.4, Corollary 4.5 | V | |
| Lemma 4.6 | V\* | Re-derived in full: openness of `O_i`, both cases of connectedness, regularity near `K` and away from `K`. `R = ∅` (i.e. `K = X`) is implicit. |
| Theorem 5.1 | V\* | Re-derived in full, including: well-definedness and transitivity of the order on branches; `L_b ⊆ P^n_i` for levels below and above `n`; the map `b ↦ L_b` is at most two-to-one; Step 4. |
| Remark 5.2 | V | **Corrected in the paper**, see 5.4 below. |
| Lemma 6.2, Proposition 6.3 | V | |
| Theorem 1.5 | V | `U_m` open in the closed set `H`; both inclusions of `D(X) = ⋂ U_m` checked. |
| Theorem 1.4 | V | Assembly. |
| Theorem 1.2 | V | Uses "G_δ in a completely metrizable space is completely metrizable". |
| Corollary 6.5 | V | Uses that `D(X)` is Borel (Ramírez Angarita, Teorema 2.0.2) and the perfect set property for Borel sets. Both must be supplied in Lean. |
| Proposition 7.5 | V | |
| Example 7.1 (arc) | V | Elementary. |
| Example 7.2 (null chain) | V, K | Known example; the description of the topology was re-derived. |
| Example 7.3 (buckethandle with cone) | V | Every claim re-derived on paper, taking the indecomposability of the buckethandle as known. **OUT** of the formalization scope: see Section 5. |
| Remark 1.3 | V | Rests on Ordoñez 2018, Corollary 4.13 (cited, not re-proved). |

No result is classed GAP, FALSE or UNRESOLVED.

### 5.3 Places where Lean will require more than the paper writes

These are not gaps; they are steps a formal proof must make explicit.

1. **Components.** The paper speaks of "components of `R`". Lean needs a fixed
   representation; the statement surface uses `connectedComponentIn R x` and
   the set `components R` of all of them. Lemma 2.3 (b) and (c) must be proved
   for this representation.
2. **Empty cases.** `𝓕(X)` contains `∅`. Proposition 4.3 with `F = ∅` or
   `G = ∅`, and Lemma 4.6 with `K = X`, are trivial but must be handled.
3. **Cells are positions, not sets.** In Theorem 5.1 a cell must be an index
   in a list, with a parent function. That two different positions of one
   level hold different sets follows from disjoint nonempty interiors, but the
   proof is cleaner if it never needs it.
4. **Branches.** A branch is a function `b : ∀ n, Fin (k n)` with
   `parent (b (n+1)) = b n`. "Distinct at level `n` implies distinct at all
   later levels" is immediate from the parent function; the paper leaves it
   implicit.
5. **Enumeration.** `D(X) = {D₁, D₂, …}` with repetitions: a surjection
   `ℕ → regular X`, which exists because the set is countable and nonempty.
6. **Baire on an open subset.** Step 5 of Theorem 5.1 applies Baire category
   to an open subset `U`. With Mathlib it is simpler to apply
   `dense_iUnion_interior_of_closed` to the countable closed cover `{K_b}` of
   `X` directly; this gives exactly the density statement.
7. **Hyperspace topology.** The paper uses the Hausdorff metric. Mathlib's
   topology on `NonemptyCompacts X` is the Vietoris topology, and the
   Hausdorff metric instance is built to have that topology. Lemma 2.6 (b),
   (c) are then Mathlib lemmas; 2.6 (a) is a short consequence.
8. **`C(X)` as a space.** Complete metrizability of `D(X)` needs `C(X)` to be
   completely metrizable, hence that the connected members form a closed
   subset of `NonemptyCompacts X`. The paper takes compactness of `C(X)` from
   the literature.
9. **Cardinality.** "`|D(X)| = 𝔠`" needs the bound `|C(X)| ≤ 𝔠` (second
   countable `T₀` space).

### 5.4 Corrections made to the paper as a result of this audit

1. **Remark 3.3.** The reason given for "the arc has no infinite blister
   family" was garbled. Replaced by a correct one: if `A = [a, b]` and
   `A \ O` is a subinterval, the nonempty set `O` contains `a` or `b`, so a
   pairwise disjoint family of such sets has at most two members.
2. **Remark 5.2.** It said that countability is essential in the density proof
   only in Steps 3 and 5. That was wrong: the enumeration on which the whole
   construction rests (Steps 1 and 4) also needs it. The remark now says so.

Neither change affects a theorem or a proof.

### 5.5 Scope decisions for the formalization

- **In scope:** every numbered lemma, proposition, theorem and corollary of
  Sections 3 to 6, Theorems 1.2, 1.4, 1.5, and Proposition 7.5.
- **Out of the first scope, and to be reported as such:** Example 7.3. It is a
  new example, but a formal certificate needs the Knaster buckethandle and a
  proof that it is indecomposable, neither of which was found in Mathlib. That
  is a separate project of comparable size to a section of the paper.
- **Out of scope:** Examples 7.1 and 7.2 (elementary or known), Remark 1.3
  (depends on a cited external theorem), Remark 3.3 (an illustration).

If any of these stays unformalized, the repository formalizes the theorems of
the paper and not the whole paper, and must say so.

### 5.6 After the formalization

The statements of Section 5.5 "in scope" were all proved in Lean 4 on
11 November 2026 (see Section 4 for exactly what was run).

1. **No mathematical gap was found.** Every in-scope statement was proved as
   stated in the paper, with the paper's hypotheses and no additional one.
2. **No statement had to be changed.** The two remarks corrected in Section 5.4
   were found by reading, before the formalization.
3. **One hypothesis is unnecessary.** Proposition 4.3 (2) holds without
   "D(X) countable" (already suspected in Section 5.3; now confirmed by the Lean
   proof, which does not use it).
4. **The Lean proofs do not follow the written proofs line by line.**
   Section 3.2 of this file lists the differences: no boundary
   bumping, a different treatment of components, and a different bookkeeping
   in Theorem 5.1. So the kernel check certifies the *statements*. It does not
   certify that each written step of the paper is correct, although no wrong
   step was met while translating.
5. **Items 3 and 4 of Section 5.3 were avoided, not solved.** Cells are sets,
   not positions, and there are no parent maps: a level is a finite set of
   gaps and a branch is a choice function through the levels.
6. **Still unverified by machine:** Examples 7.1, 7.2, 7.3 and all remarks.
   Their status is the one given in Section 5.2 (re-derived on paper by an AI
   system).
7. **Still unreviewed by a human:** the paper's proofs, and the claim that the
   Lean statements say what the paper says. The second claim is easier to
   check than the first: it needs only `Challenge.lean` (about 300 lines) and
   Section 2 of this file.
