# On the Structure of Countable Hyperspaces of Regular Subcontinua

Paper by Lucas Alves de Almeida (20-page version of 11 November 2026, in
`paper/`) and its Lean 4 formalization.

For a metric continuum `X`, `D(X)` is the hyperspace of subcontinua `A` of `X`
with `A = cl int A`. The main theorem: if `D(X)` is countable, it is a `G_δ`
subset of `C(X)`, hence completely metrizable and scattered with dense isolated
points; so `D(X)` is never homeomorphic to `ℚ`.

## Status

**All theorems of the paper are proved in Lean and pass the sandboxed
Comparator job in CI. The paper as a whole is only partially formalized: its
examples and remarks are not covered.**

| Item | Status |
| --- | --- |
| Theorems 1.2, 1.4, 1.5, 3.4, 4.4, 5.1; Lemmas 3.2, 4.1, 4.6, 6.2; Propositions 4.3, 6.3, 7.5; Corollaries 4.5, 6.5 | Proved. 21 compared declarations, plus 2 auxiliary ones (23 in all). |
| Examples 7.1, 7.2, 7.3 | **Not formalized.** Example 7.3 is a new example of the paper. |
| Remarks (1.3, 3.3, 3.5, 5.2, 6.4, 6.6, 7.4) | **Not formalized.** |
| Lemmas 2.3 and 2.4 of the preliminaries, as stated | **Not formalized.** The Lean proofs do not use boundary bumping and treat components differently (`docs/BLUEPRINT.md`, Section 2). |
| `sorry`, `admit`, `native_decide`, new axioms in `Solution.lean` and `RegularSubcontinua/` | None. |
| Axioms of every compared theorem | `propext`, `Classical.choice`, `Quot.sound` only. |
| `lake build` | Succeeds, locally (Mathlib built from source) and in CI on a fresh checkout (Mathlib cache). |
| `./scripts/verify-comparator.sh` as shipped (sandboxed with `bubblewrap`; Lean kernel + nanoda + con-ron) | **Accepts**, in GitHub Actions on commit `49a57d8` ([run](https://github.com/LucasAlves8Sp/On-the-Structure-of-Countable-Hyperspaces-of-Regular-Subcontinua/actions/runs/43079572098)). |
| `lake comparator`, same kernels, local run | Accepts; run with `--inadvisably-no-sandbox` because `bubblewrap` was not installed where the code was written. |
| `lake comparator --paranoid` (adds leanchecker-paranoid, lean4lean, con-leche), local run | Accepts; also without the sandbox. |
| Negative control | With one statement of `Solution.lean` deliberately weakened, Comparator rejected it ("theorem statement do not match"). The file was then restored. |
| CI on commit `49a57d8` | Metadata and licence, submission link, build, Comparator: pass. **API documentation job: failed** with "not enough memory" on the runner while doc-gen4 was processing dependencies; it does not involve the proofs. See the Actions tab for later commits. |
| Human review of the Lean statements | **None.** |
| Human refereeing of the paper | **None.** |
| Palomar Registry | Submitted by the author on 11 November 2026; not registered at the time of writing. |

The logs of the local commands are in `docs/verification/`; the CI logs are in
the Actions tab.

### What the kernel check does and does not establish

It establishes that the 23 statements in `Challenge.lean` follow from the
axioms of Lean with Mathlib's definitions. It does not establish that those
statements say what the paper says: that is a reading task, for which
`Challenge.lean` (about 300 lines) and `docs/CORRESPONDENCE.md` are the
material, and no human has done it yet. It also does not certify the written
proofs of the paper step by step, because the Lean proofs take a different
route in places.

## Two standing rules

1. **Lemma 4.6 and Theorem 5.1 are standalone Comparator targets**
   (`RegularSubcontinua.decreasing_intersection`,
   `RegularSubcontinua.dense_interior_minimal`).
2. **"The main theorem is formalized" and "the paper is formalized" are
   different claims.** The first is true here, subject to the caveats in the
   table. The second is not: see the rows marked "Not formalized".

## Layout

- `Challenge.lean`: 13 definitions and 23 statements, each closed by `sorry`.
  Imports Mathlib only.
- `Solution.lean`: the same 23 statements, proved from the library.
- `RegularSubcontinua/`: the proof development (about 2,800 lines); module
  list in `docs/BLUEPRINT.md`.
- `comparator.json`: the 23 theorem names. `definition_names` is empty on
  purpose: the definitions are not holes to be filled by the solution, so
  Comparator requires them to be identical in `Challenge` and `Solution`.
- `formalization.yaml`: metadata (v0.4).
- `docs/AUDIT.md`: mathematical audit before the formalization, and what the
  formalization found.
- `docs/CORRESPONDENCE.md`: paper result ↔ Lean declaration; what is not
  covered.
- `docs/BLUEPRINT.md`: architecture, and where the Lean proofs differ from the
  written ones.
- `docs/verification/`: command logs.
- `docs/research-prompt.md`: the prompt that started the research, verbatim.
- `paper/`: the paper (`problemQ.pdf`, `problemQ.tex`, `refs.bib`).
- `lean-toolchain`, `lake-manifest.json`, `scripts/`, `.github/`, `docbuild/`,
  `LICENSE`: from
  [PalomarRegistry/PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate)
  at commit `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. The two manifests were
  edited by hand only to rename the root package.

Pins: Lean `leanprover/lean4:v4.35.0-rc2`; Mathlib tag `v4.35.0-rc2`
(commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`).

## Reproducing

```text
lake exe cache get        # or let lake build Mathlib from source
lake build
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # needs bubblewrap
```

Before any submission, check that CI is green on the exact commit to be
submitted. Submission goes through
<https://submit.palomar-registry.org/> with the full 40-character commit SHA,
by the responsible maintainer.

## How this was produced

All Lean code was written by an AI system (Claude Fable 5.2) in one session on
11 November 2026, under a prompt written by the author of the paper. The
mathematics of the paper was itself developed with extensive AI assistance:
as the paper declares, the models involved were Opus 5.5, Fable 5.2 and
ChatGPT-Astra, with Fable 5.2 carrying out the main research, ChatGPT-Astra
rechecking the arguments, comparing them with the literature and re-deriving
the results, and the author directing the investigation and editing and
checking the text. See
`formalization.yaml`, section `automation`.

## Licence

Apache-2.0, see `LICENSE`.
