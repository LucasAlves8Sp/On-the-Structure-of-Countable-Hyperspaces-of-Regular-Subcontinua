# Architecture of the formalization (as built)

This file replaces the earlier plan. It describes the proof development that
exists and compiles. Lean `v4.35.0-rc2`, Mathlib tag `v4.35.0-rc2`
(commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`).

## 1. Modules

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

## 2. Where the Lean proofs differ from the written proofs

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

## 3. Mathlib results the development relies on

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

## 4. What is not formalized

See `docs/CORRESPONDENCE.md`, second table: Examples 7.1 to 7.3 and the
remarks. Example 7.3 would need the Knaster buckethandle continuum and a proof
that it is indecomposable; neither was found in Mathlib.
