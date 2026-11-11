# On the structure of countable hyperspaces of regular subcontinua

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24144776.svg)](https://doi.org/10.5281/zenodo.24144776)
[![aiXiv](https://img.shields.io/badge/aiXiv-2611.01165-4b5563.svg)](https://aixiv.online/abs/2611.01165)
[![Hexagon](https://img.shields.io/badge/hexagon-2611.00342_(in_moderation)-9ca3af.svg)](https://hexagonmath.org/)
[![Lean 4](https://img.shields.io/badge/Lean_4-all_theorems_formalized-2f6f4f.svg)](lean/)
[![Palomar](https://img.shields.io/badge/Palomar-submitted-9ca3af.svg)](https://palomar-registry.org/)

**Lucas Alves de Almeida** (independent researcher)

**Main result.** If $X$ is a metric continuum whose hyperspace $\mathcal D(X)$ of regular subcontinua is countable, then $\mathcal D(X)$ is a $G_\delta$ subset of $C(X)$, hence completely metrizable and scattered, with dense isolated points. In particular **$\mathcal D(X)$ is never homeomorphic to the rationals**. This answers the rational case of a question of Ramírez Angarita (2023, Pregunta 3.2.14) and of Camargo, Ordoñez and Ramírez (Appl. Gen. Topol. 25 (2024), Question 3.26); the irrational case was answered in [the companion repository](https://github.com/LucasAlves8Sp/A-CONTINUUM-WHOSE-HYPERSPACE-OF-REGULAR-SUBCONTINUA-IS-HOMEOMORPHIC-TO-THE-IRRATIONALS). **Every theorem of the paper is formalized in Lean 4 with Mathlib**; the examples and remarks are not.

| | |
| --- | --- |
| Paper (PDF) | [`paper/countable-hyperspaces-regular-subcontinua.pdf`](paper/countable-hyperspaces-regular-subcontinua.pdf) |
| Zenodo | [doi:10.5281/zenodo.24144777](https://doi.org/10.5281/zenodo.24144777) (all versions: [10.5281/zenodo.24144776](https://doi.org/10.5281/zenodo.24144776)) |
| aiXiv preprint | [aiXiv:2611.01165](https://aixiv.online/abs/2611.01165) [math.GN] |
| Hexagon preprint | hexagon:2611.00342, submitted 11 November 2026, awaiting moderation |
| Lean formalization | [`lean/`](lean/), with the main theorem `RegularSubcontinua.no_continuum_with_regular_hyperspace_rat` |
| Review and verification | [`REVIEW_AND_VERIFICATION.md`](REVIEW_AND_VERIFICATION.md) |
| Palomar registry | submitted 11 November 2026 from commit [`959fb91`](https://github.com/LucasAlves8Sp/On-the-Structure-of-Countable-Hyperspaces-of-Regular-Subcontinua/tree/959fb91b14b6eaf038f9042183ed2f021904e0ce) of the branch [`palomar`](https://github.com/LucasAlves8Sp/On-the-Structure-of-Countable-Hyperspaces-of-Regular-Subcontinua/tree/palomar); mechanical verification passed; not yet registered |

## Abstract

Let $X$ be a metric continuum and let $\mathcal D(X)$ be its hyperspace of regular subcontinua, that is, of the subcontinua of $X$ which are the closure of their interior. We prove that if $\mathcal D(X)$ is countable, then the interiors of its minimal elements are dense in $X$, and every regular subcontinuum is determined by the minimal elements it contains. We further establish that $\mathcal D(X)$ is a $G_\delta$ subset of the hyperspace $C(X)$ of subcontinua whenever $X$ admits a family of regular subcontinua whose interiors have dense union and which satisfies an absorption property. Consequently, every countable $\mathcal D(X)$ is completely metrizable and scattered. In particular, $\mathcal D(X)$ is never homeomorphic to the rational numbers, which answers a question of Ramírez Angarita and of Camargo, Ordoñez and Ramírez. The theorems of the paper are formalized in Lean 4.

## Contents

| Path | Description |
| --- | --- |
| [`paper/countable-hyperspaces-regular-subcontinua.pdf`](paper/countable-hyperspaces-regular-subcontinua.pdf) | The paper (PDF, 20 pages) |
| [`paper/countable-hyperspaces-regular-subcontinua.tex`](paper/countable-hyperspaces-regular-subcontinua.tex), [`paper/refs.bib`](paper/refs.bib) | LaTeX source (`amsart`, figures in TikZ) and bibliography |
| [`lean/`](lean/) | Lean 4 / Mathlib formalization of every theorem of the paper; see [`lean/README.md`](lean/README.md) |
| [`lean/checks/`](lean/checks/) | Logs of the build, axiom, comparator and negative-control runs |
| [`REVIEW_AND_VERIFICATION.md`](REVIEW_AND_VERIFICATION.md) | Mathematical audit; coverage of the paper by the Lean code; how the Lean proofs differ from the written ones; the checks performed |
| [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md) | The AI disclosure and the formalization statement, as they appear in the paper |
| [`prompt/first-prompt.md`](prompt/first-prompt.md) | The full first prompt given to start the research, unedited |
| [`LICENSE.md`](LICENSE.md) | CC BY 4.0 for the paper and texts; Apache-2.0 for the Lean code |

## The Lean formalization

The folder [`lean/`](lean/) contains a Lean 4 / Mathlib development that proves **every numbered theorem, lemma, proposition and corollary of Sections 1 and 3–6 of the paper, and Proposition 7.5**, with the paper's hypotheses and no additional one. It uses Lean `v4.35.0-rc2` and Mathlib at the tag of the same name, has about 2,800 lines of proofs in 9 files, and uses the Lean module system throughout. There is no `sorry` outside `Challenge.lean` and no added axiom; `lean/CheckAxioms.lean` reports only `propext`, `Classical.choice` and `Quot.sound` for all 23 compared results. The answer to the question is

```lean
theorem RegularSubcontinua.no_continuum_with_regular_hyperspace_rat :
    ¬ ∃ (X : Type u) (_ : MetricSpace X) (_ : CompactSpace X)
      (_ : ConnectedSpace X), Nonempty (↥(regular X) ≃ₜ ℚ)
```

and the main theorem is

```lean
theorem RegularSubcontinua.main_theorem (X : Type u) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] (hcount : (regular X).Countable) :
    IsGδ (regular X) ∧ IsCompletelyMetrizableSpace ↥(regular X) ∧
    IsScattered ↥(regular X) ∧
    Dense {K : ↥(regular X) | IsOpen ({K} : Set ↥(regular X))}
```

Here `regular X` is the set of points of `C(X)` (connected members of Mathlib's `NonemptyCompacts X`, whose topology is that of the Hausdorff metric) that equal the closure of their interior.

**What is formalized:**

- the two counting principles: independent families (Lemma 3.2) and the blister theorem (Theorem 3.4);
- the complement lemma (Lemma 4.1), the algebra of finite unions (Proposition 4.3), absorption (Theorem 4.4, Corollary 4.5) and **decreasing intersections (Lemma 4.6)**;
- **density of the minimal elements (Theorem 5.1)**;
- atomic families (Lemma 6.2, Proposition 6.3), the $G_\delta$ theorem (Theorem 1.5), the structure theorem (Theorem 1.4), the main theorem (Theorem 1.2) and the dichotomy (Corollary 6.5);
- Proposition 7.5 (no chain of the order type of $\mathbb Q$);
- the known results used along the way, built in the repository: a $G_\delta$ subset of a Polish space is Polish, countable completely metrizable spaces are scattered, $C(X)$ is closed in the hyperspace of compact sets, and $\mathcal D(X)$ is a Borel subset of $C(X)$.

Lemma 4.6 and Theorem 5.1 are standalone comparator targets.

**What is not formalized:** Examples 7.1–7.3 (7.3 is a new example of the paper), the remarks, and Lemmas 2.3 and 2.4 in the form stated in the paper. So the theorems of the paper are formalized, but not the whole paper.

**The Lean proofs differ from the written ones** in three places: they do not use boundary bumping (connectedness is handled through closed separations); components are handled through one dichotomy instead of Lemma 2.3; and Theorem 5.1 uses levels of nested pairs instead of a tree of ordered covers. They also prove the Borel property that the paper cites. Details are in [`REVIEW_AND_VERIFICATION.md`](REVIEW_AND_VERIFICATION.md).

**Checks** (logs in [`lean/checks/`](lean/checks/)):

| Check | Result |
| --- | --- |
| `lake build` against the pinned Mathlib | no errors; the only `sorry` warnings are the deliberate ones in `Challenge.lean` |
| `CheckAxioms.lean` (all 23 compared results) | only `propext`, `Classical.choice`, `Quot.sound` |
| `lake comparator`, `Solution` against `Challenge`, in the `bubblewrap` sandbox (GitHub Actions, and Palomar's own run) | accepted by the Lean kernel, nanoda and con-ron |
| `lake comparator --paranoid` (local, unsandboxed) | also accepted by the paranoid Lean kernel, lean4lean and con-leche |
| negative control: one statement of `Solution.lean` deliberately weakened | rejected, as it should be |

**Palomar.** The formalization was submitted to the [Palomar registry](https://palomar-registry.org/) of Lean-verified mathematics on 11 November 2026. Palomar requires the Lean project and a single licence file at the repository root, so the submitted snapshot is commit [`959fb91`](https://github.com/LucasAlves8Sp/On-the-Structure-of-Countable-Hyperspaces-of-Regular-Subcontinua/tree/959fb91b14b6eaf038f9042183ed2f021904e0ce) of the branch [`palomar`](https://github.com/LucasAlves8Sp/On-the-Structure-of-Countable-Hyperspaces-of-Regular-Subcontinua/tree/palomar). It holds the same Lean files as `lean/`, with Palomar's template CI. Palomar's sandboxed mechanical verification passed; the automated statement review and the registration are pending.

## Building

**Paper.** In `paper/`, run `latexmk -pdf countable-hyperspaces-regular-subcontinua.tex` (or `pdflatex`, `bibtex`, `pdflatex` twice).

**Lean.** In `lean/`, with Lean `v4.35.0-rc2` (installed by `elan` from `lean-toolchain`):

```
lake exe cache get
lake build
lake env lean CheckAxioms.lean
./scripts/verify-comparator.sh   # Challenge vs Solution; needs bubblewrap
```

## How to cite

Lucas Alves de Almeida, *On the structure of countable hyperspaces of regular subcontinua*, preprint, Zenodo, 2026. [doi:10.5281/zenodo.24144776](https://doi.org/10.5281/zenodo.24144776). Also available as [aiXiv:2611.01165](https://aixiv.online/abs/2611.01165).

The concept DOI above always resolves to the latest version.

| Version | Content | DOI |
| --- | --- | --- |
| v1 | paper (PDF), 11 November 2026 | [10.5281/zenodo.24144777](https://doi.org/10.5281/zenodo.24144777) |

```bibtex
@misc{AlvesdeAlmeida2026countable,
  author    = {Alves de Almeida, Lucas},
  title     = {On the structure of countable hyperspaces of regular subcontinua},
  year      = {2026},
  publisher = {Zenodo},
  note      = {Preprint, aiXiv:2611.01165},
  doi       = {10.5281/zenodo.24144776},
  url       = {https://doi.org/10.5281/zenodo.24144776}
}
```

## Status

No independent expert has yet verified the proofs, and no human has yet compared the Lean statements with the paper. The Lean formalization proves every theorem of the paper against the definitions in `lean/Challenge.lean`; the examples and remarks are not formalized. The Palomar registration and the Hexagon moderation are pending.
