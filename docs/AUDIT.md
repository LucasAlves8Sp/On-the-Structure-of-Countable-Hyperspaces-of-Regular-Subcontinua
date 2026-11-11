# Mathematical audit

Audited text: `problemQ.pdf`, 19-page version of 11 November 2026, then titled
"The hyperspace of regular subcontinua is never homeomorphic to the rationals".
The current 20-page version differs from it only in the title, the abstract, and
the two unnumbered sections at the end (formalization, AI declaration).
Auditor: Claude Fable 5.2 (AI), 11 November 2026. This is the same system that
wrote much of the paper, so it is a re-derivation, not an independent review.
No human referee has examined the proofs.

Sections 1 to 5 are the audit made **before** any Lean code was written and
are kept as they were. Section 6 records what the formalization found
afterwards.

Result classes: **V** = every inference re-derived and found valid;
**V\*** = valid, but the written proof needs a more explicit form in Lean
(listed in Section 3); **K** = known result, cited; **OUT** = not audited to
formalization standard.

## 1. Dependency graph

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

## 2. Status of every statement

| Result | Class | Notes |
| --- | --- | --- |
| Lemma 2.2 (a)–(f) | V | Each identity re-derived. (f) uses that `G`, `G₁`, `G₂` are closed. |
| Lemma 2.3 (a)–(c) | V | (a) rests on components = quasi-components in compact Hausdorff spaces. |
| Lemma 2.4 boundary bumping | V | Checked that the clopen set `V` is open in `Z` (open in `cl W` and inside `W`). |
| Lemma 2.5 | K | Standard. |
| Lemma 2.6 | V | |
| Lemma 2.7 thinning | V | |
| Lemma 3.2 | V | Upper bound uses `|C(X)| ≤ 𝔠`. |
| Remark 3.3 (arc) | V | **Corrected in the paper**, see 4.1 below. |
| Theorem 3.4 blister | V | Covering claim (1) and the regularity step re-derived. |
| Lemma 4.1 | V | Part (2) needs `A ∪ B = A ∪ R`; checked. |
| Proposition 4.3 | V\* | Cases `F = ∅`, `G = ∅` are implicit. |
| Theorem 4.4, Corollary 4.5 | V | |
| Lemma 4.6 | V\* | Re-derived in full: openness of `O_i`, both cases of connectedness, regularity near `K` and away from `K`. `R = ∅` (i.e. `K = X`) is implicit. |
| Theorem 5.1 | V\* | Re-derived in full, including: well-definedness and transitivity of the order on branches; `L_b ⊆ P^n_i` for levels below and above `n`; the map `b ↦ L_b` is at most two-to-one; Step 4. |
| Remark 5.2 | V | **Corrected in the paper**, see 4.2 below. |
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

## 3. Places where Lean will require more than the paper writes

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

## 4. Corrections made to the paper as a result of this audit

1. **Remark 3.3.** The reason given for "the arc has no infinite blister
   family" was garbled. Replaced by a correct one: if `A = [a, b]` and
   `A \ O` is a subinterval, the nonempty set `O` contains `a` or `b`, so a
   pairwise disjoint family of such sets has at most two members.
2. **Remark 5.2.** It said that countability is essential in the density proof
   only in Steps 3 and 5. That was wrong: the enumeration on which the whole
   construction rests (Steps 1 and 4) also needs it. The remark now says so.

Neither change affects a theorem or a proof.

## 5. Scope decisions for the formalization

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

## 6. After the formalization

The statements of Section 5 "in scope" were all proved in Lean 4 on
11 November 2026 (see `README.md` for exactly what was run).

1. **No mathematical gap was found.** Every in-scope statement was proved as
   stated in the paper, with the paper's hypotheses and no additional one.
2. **No statement had to be changed.** The two remarks corrected in Section 4
   were found by reading, before the formalization.
3. **One hypothesis is unnecessary.** Proposition 4.3 (2) holds without
   "D(X) countable" (already suspected in Section 3; now confirmed by the Lean
   proof, which does not use it).
4. **The Lean proofs do not follow the written proofs line by line.**
   `docs/BLUEPRINT.md`, Section 2, lists the differences: no boundary
   bumping, a different treatment of components, and a different bookkeeping
   in Theorem 5.1. So the kernel check certifies the *statements*. It does not
   certify that each written step of the paper is correct, although no wrong
   step was met while translating.
5. **Items 3 and 4 of Section 3 were avoided, not solved.** Cells are sets,
   not positions, and there are no parent maps: a level is a finite set of
   gaps and a branch is a choice function through the levels.
6. **Still unverified by machine:** Examples 7.1, 7.2, 7.3 and all remarks.
   Their status is the one given in Section 2 (re-derived on paper by an AI
   system).
7. **Still unreviewed by a human:** the paper's proofs, and the claim that the
   Lean statements say what the paper says. The second claim is easier to
   check than the first: it needs only `Challenge.lean` (about 300 lines) and
   `docs/CORRESPONDENCE.md`.

