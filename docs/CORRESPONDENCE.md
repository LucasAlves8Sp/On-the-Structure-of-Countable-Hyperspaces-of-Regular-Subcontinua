# Correspondence between the paper and the Lean declarations

Paper: *On the structure of countable hyperspaces of regular subcontinua*, 20-page version of 11 November 2026. All Lean names are in the
namespace `RegularSubcontinua`. Statements are in `Challenge.lean`; the same
names are proved in `Solution.lean`; the proofs are in `RegularSubcontinua/`.

The status columns are independent:

- **Math**: re-derived in the pre-formalization audit (`docs/AUDIT.md`).
- **Compiles**: the statement is accepted by Lean.
- **Re-audited**: after compiling, the statement was read back against the
  paper (by the AI system that wrote it; no human has done this).
- **Proved**: a `sorry`-free proof compiles, `#print axioms` reports only
  `propext`, `Classical.choice`, `Quot.sound`, and the local Comparator run
  described in `README.md` accepted it. The Comparator run was made
  **without the sandbox**; see `README.md`.

## Results covered

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

## Preliminaries of Section 2

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

## New claims of the paper that are NOT covered

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

## Definitions

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
