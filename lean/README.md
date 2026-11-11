# RegularSubcontinua: countable hyperspaces of regular subcontinua

A Lean 4 / Mathlib formalization of the theorems of the paper

> Lucas Alves de Almeida, *On the structure of countable hyperspaces of regular subcontinua*,
> preprint, Zenodo, [doi:10.5281/zenodo.24144776](https://doi.org/10.5281/zenodo.24144776);
> also [aiXiv:2611.01165](https://aixiv.online/abs/2611.01165).

The paper, its LaTeX source and the AI disclosure are at the root of
[the repository](https://github.com/LucasAlves8Sp/On-the-Structure-of-Countable-Hyperspaces-of-Regular-Subcontinua).
The project is laid out as the [Palomar registry](https://palomar-registry.org/) requires:
`Challenge.lean` states the results using only Mathlib, `Solution.lean` proves them, and
`comparator.json` tells `lake comparator` how to compare them. The provenance and the other metadata
are in `formalization.yaml`. It is registered in Palomar as
[PALOMAR-2026-11-11-000007 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-11-11-000007&version=1),
from commit `959fb91` of the branch `palomar`, which has this project at its root.

## The theorem

For a metric continuum `X` (a nonempty compact connected metric space), a subcontinuum is
*regular* if it equals the closure of its interior in `X`. `𝒟(X)` is the hyperspace of regular
subcontinua with the Hausdorff metric. Ramírez Angarita (2023, Pregunta 3.2.14) and Camargo,
Ordoñez and Ramírez (Appl. Gen. Topol. 25 (2024), Question 3.26) asked whether `𝒟(X)` can be
homeomorphic to the rationals or to the irrationals. The paper answers the rational case.

**Theorem 1.2.** If `𝒟(X)` is countable, then it is a `G_δ` subset of `C(X)`; hence it is
completely metrizable and scattered, and its isolated points are dense. In particular `𝒟(X)` is
never homeomorphic to `ℚ`.

The compared statements (`Challenge.lean`) are

```lean
theorem main_theorem (X : Type u) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] (hcount : (regular X).Countable) :
    IsGδ (regular X) ∧ IsCompletelyMetrizableSpace ↥(regular X) ∧
    IsScattered ↥(regular X) ∧
    Dense {K : ↥(regular X) | IsOpen ({K} : Set ↥(regular X))}

theorem no_continuum_with_regular_hyperspace_rat :
    ¬ ∃ (X : Type u) (_ : MetricSpace X) (_ : CompactSpace X)
      (_ : ConnectedSpace X), Nonempty (↥(regular X) ≃ₜ ℚ)
```

together with 21 further statements, one for each numbered result of the paper that is covered.

* `Subcontinua X` is the subtype of connected members of `TopologicalSpace.NonemptyCompacts X`.
  Mathlib gives that type the Vietoris topology, and its Hausdorff-metric instance is built to have
  the same topology.
* `regular X : Set (Subcontinua X)` is the set of those `K` with `closure (interior K) = K`.
* `IsScattered` (every nonempty subset has an isolated point) is defined in `Challenge.lean`,
  because Mathlib has no such notion.

There is no `sorry` outside `Challenge.lean` and no added axiom. Every compared result uses only the
axioms `propext`, `Classical.choice` and `Quot.sound` (`lake env lean CheckAxioms.lean`).

## How the proof goes

1. **Counting** (`Counting.lean`). An independent family, or an infinite family of disjoint
   "blisters", gives `𝔠` regular subcontinua (Lemma 3.2, Theorem 3.4).
2. **Complements** (`Complement.lean`). When `𝒟(X)` is countable, regularised differences of
   regular subcontinua have finitely many components, each regular (Lemma 4.1, Proposition 4.3);
   minimal elements absorb (Theorem 4.4).
3. **Decreasing intersections** (`Decreasing.lean`, Lemma 4.6).
4. **Density** (`Density.lean`, Theorem 5.1). Successive refinements of `X` by regular
   subcontinua, organised as levels of nested pairs, and Baire category show that the minimal
   elements have dense union of interiors.
5. **Atoms and `G_δ`** (`Atomic.lean`). An atomic family codes `𝒟(X)`; then `𝒟(X)` is `G_δ` in
   `C(X)` (Lemma 6.2, Proposition 6.3, Theorem 1.5).
6. **The main theorem** (`Main.lean`). `C(X)` is closed in the hyperspace of compact sets, a `G_δ`
   subset of a Polish space is Polish, and a countable completely metrizable space is scattered, so
   it has isolated points, while `ℚ` has none. Also Theorem 1.4 and Proposition 7.5.
7. **The dichotomy** (`Dichotomy.lean`, Corollary 6.5). `𝒟(X)` is Borel in `C(X)`, so it is
   countable or of size `𝔠`.

The proofs differ from the written ones in a few places: no boundary bumping, a different treatment
of components, and different bookkeeping in Theorem 5.1. See Section 3.2 of
`REVIEW_AND_VERIFICATION.md` at the repository root.

## Files

| File | Content |
| --- | --- |
| `Challenge.lean` | 13 definitions and the 23 compared statements, each closed by `sorry`; imports Mathlib only |
| `Solution.lean` | the same 23 statements, each proved by one call to the library |
| `RegularSubcontinua/Defs.lean` | the definitions of `Challenge.lean`, verbatim |
| `RegularSubcontinua/Basic.lean` | regular closed sets, closed separations, nested intersections, relatively clopen sets |
| `RegularSubcontinua/Counting.lean` | thinning, cardinality of `𝒟(X)`, Lemma 3.2, Theorem 3.4 |
| `RegularSubcontinua/Complement.lean` | regularised differences, Lemma 4.1, Proposition 4.3, Theorem 4.4, Corollary 4.5 |
| `RegularSubcontinua/Decreasing.lean` | Lemma 4.6 |
| `RegularSubcontinua/Density.lean` | Theorem 5.1 |
| `RegularSubcontinua/Atomic.lean` | Lemma 6.2, Proposition 6.3, Theorem 1.5 |
| `RegularSubcontinua/Main.lean` | Polish and scattered spaces, Theorems 1.4 and 1.2, Proposition 7.5 |
| `RegularSubcontinua/Dichotomy.lean` | Borel property of `𝒟(X)`, Corollary 6.5 |
| `CheckAxioms.lean` | `#print axioms` for every compared result |
| `comparator.json`, `formalization.yaml` | comparator configuration and Palomar metadata |
| `scripts/` | Palomar's source check, metadata validator and sandboxed comparator script |
| `checks/` | logs of the checks; see `checks/README.md` |

Lemma 4.6 (`decreasing_intersection`) and Theorem 5.1 (`dense_interior_minimal`) are standalone
comparator targets.

## Building

With Lean `v4.35.0-rc2` (installed by `elan` from `lean-toolchain`) and Mathlib at the tag
`v4.35.0-rc2`:

```
lake exe cache get
lake build
lake env lean CheckAxioms.lean
./scripts/verify-comparator.sh   # needs bubblewrap
```

## Provenance

All Lean code, statements and proofs, was written by Claude Fable 5.2 (Anthropic) at the author's
request. No human has yet compared the Lean statements with the paper. See `formalization.yaml` and
`AI_DISCLOSURE.md` at the repository root.

## Licence

Apache-2.0, see `LICENSE`.
