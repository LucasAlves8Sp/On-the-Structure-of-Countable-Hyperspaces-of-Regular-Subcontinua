# Verification logs

Output of the commands run on 11 November 2026 on the sources in this
repository, in a cloud container (Linux x86_64). Long build output is filtered
to warnings and errors; nothing else was edited.

| File | Command | Result |
| --- | --- | --- |
| `versions.txt` | `lean --version`, `lake --version`, Mathlib commit | Lean 4.35.0-rc2; Mathlib `0653561` |
| `lake-build.txt` | `lake build` | Build completed successfully. 41 warnings: 23 are the intended `sorry` of `Challenge.lean`, the rest are style linters. |
| `forbidden-constructs.txt` | `grep` for `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern` in `Solution.lean` and the library | No match. |
| `axioms.txt` | `#print axioms` for each of the 23 compared theorems | Each: `propext`, `Classical.choice`, `Quot.sound`. |
| `source-checks.txt` | `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb`, line counts | Both exit 0. |
| `comparator-no-sandbox.txt` | `lake comparator --inadvisably-no-sandbox`, with nanoda and con-ron | "Your solution is okay!" |
| `comparator-no-sandbox-paranoid.txt` | the same with `--paranoid` | "Your solution is okay!" (Lean default and paranoid kernels, lean4lean, nanoda, con-leche, con-ron) |
| `comparator-negative-control.txt` | the same on a deliberately altered `Solution.lean` | Rejected, as expected. |

## What these logs are not

- **Not a sandboxed Comparator run.** `bubblewrap` was not installed, so every
  Comparator run used `--inadvisably-no-sandbox`, and Comparator itself prints
  "this run is not trustworthy" for such runs. `scripts/verify-comparator.sh`
  was not run as shipped.
- **Not a fresh-checkout build.** The build directory was reused across the
  session, and Mathlib was compiled from source because its cache server could
  not be reached.
- **Not CI.** These logs were made before the first push. CI results, including
  the sandboxed Comparator job, are in the Actions tab of the repository.

`comparator-negative-control.txt` was made before a comment-only change to the
header of `Challenge.lean` (new title of the paper); all other logs were made
after it.
