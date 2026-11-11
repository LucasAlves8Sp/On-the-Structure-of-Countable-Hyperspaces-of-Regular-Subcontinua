# Research prompt: Problem Q — can the hyperspace of regular subcontinua be homeomorphic to the rationals?

## 0. Role, objective and stopping rule

Act as a research mathematician in continuum theory, hyperspace topology and descriptive set theory.

Your only objective is **Problem Q**:

> Does there exist a metric continuum $X$ such that $\mathcal D(X)$ is homeomorphic to $\mathbb Q$?

You may stop **only** in one of three situations:

1. **Positive solution.** You have constructed an explicit continuum $X$ and proved, with every step written out, that $\mathcal D(X)\cong\mathbb Q$.
2. **Negative solution.** You have proved that no continuum $X$ satisfies $\mathcal D(X)\cong\mathbb Q$.
3. **Honest partial result.** After serious and repeated attempts at both 1 and 2, you state the **strongest theorem you actually proved** (labelled PROVED), the exact point where each attempt broke, and concrete new lines of attack.

Never declare the problem solved unless the construction or the impossibility proof is complete. A plausible construction whose regular subcontinua have not all been found is not a solution.

## 1. Scope rules (read before anything else)

- Work **only** on Problem Q. Problem I (irrationals) is already solved (Section 4.4 below); do not revisit it.
- **Do not classify.** Do not try to classify all possible $\mathcal D(X)$, all countable $\mathcal D(X)$, all scattered types, finite cardinalities, meager composants or filament composants. Use a result from those areas only when it directly proves or refutes $\mathcal D(X)\cong\mathbb Q$.
- **Do not re-derive known results.** Cite them (Section 4) with the exact theorem number. Re-prove something only when your argument needs a variant of it, and then prove only the variant.
- Do not change the problem: no extra set-theoretic axioms, no non-metric continua, no "homeomorphic to $\mathbb Q$ minus a point" or "contains a copy of $\mathbb Q$" substitutes, unless you present them explicitly as partial results under case 3.
- Do not spend the investigation summarizing literature. The literature section below is already done for you; verify it only where you rely on it.

## 2. Exact definitions

- A **continuum** is a nonempty compact connected metric space.
- $C(X)$ is the hyperspace of nonempty subcontinua of $X$ with the Hausdorff metric
  $d_H(A,B)=\max\{\sup_{a\in A}d(a,B),\ \sup_{b\in B}d(b,A)\}$.
- A subcontinuum $A\subseteq X$ is **regular** if $A=\operatorname{cl}_X\operatorname{int}_X A$ (equivalently, $A$ is regular closed in $X$).
- $\mathcal D(X)=\{A\in C(X): A=\operatorname{cl}_X\operatorname{int}_XA\}$ with the topology inherited from $C(X)$. Note $X\in\mathcal D(X)$ always.
- **Target characterization (Sierpiński).** A nonempty countable metrizable space without isolated points is homeomorphic to $\mathbb Q$ (Kechris, *Classical Descriptive Set Theory*, Exercise 7.12).

So Problem Q is equivalent to: find $X$ such that $\mathcal D(X)$ is **countably infinite** and has **no isolated points**. (Metrizability is automatic.)

## 3. Where the problem comes from

- Posed by D. A. Ramírez Angarita, *Los hiperespacios de subcontinuos regulares y subcontinuos magros*, undergraduate thesis, Universidad Industrial de Santander, 2023, **Pregunta 3.2.14**. https://noesis.uis.edu.co/entities/publication/cd4f0fe6-ec75-47d8-8e0a-617149375321
- Repeated in J. Camargo, N. Ordoñez, D. Ramírez, *On the hyperspaces of meager and regular continua*, Appl. Gen. Topol. 25 (2024), no. 2, 385–406, **Question 3.26**. https://doi.org/10.4995/agt.2024.20116 (open PDF: https://polipapers.upv.es/index.php/AGT/article/view/20116)
- Status: the irrational half is answered positively in L. Alves de Almeida, *A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals* (preprint, 2026), which explicitly leaves Problem Q open: https://github.com/LucasAlves8Sp/A-CONTINUUM-WHOSE-HYPERSPACE-OF-REGULAR-SUBCONTINUA-IS-HOMEOMORPHIC-TO-THE-IRRATIONALS (paper in `paper/`, Lean formalization in `lean/`).

Before starting, run one literature search for later work citing the 2024 paper or stating $\mathcal D(X)\cong\mathbb Q$, record the date, and say whether anything changes the status. Then move on.

## 4. What is already known (cite, do not re-prove)

### 4.1 Foundations — N. Ordoñez, *The hyperspace of regular subcontinua*, Topology Appl. 234 (2018), 415–427, https://doi.org/10.1016/j.topol.2017.11.038

- If $X$ is locally connected, $\mathcal D(X)$ is dense in $C(X)$, contractible and arcwise connected (Theorem 3.6). **Consequence: an example for Q is not locally connected.**
- If $X$ is indecomposable, $\mathcal D(X)=\{X\}$ (Theorem 3.7). **Consequence: an example is decomposable.**
- $\mathcal D(X)$ is compact iff finite (Corollary 4.13).
- Chains, cycles and bouquets of $n$ indecomposable continua give $n(n+1)/2$, $n(n-1)+1$, $2^n-1$ regular subcontinua (Proposition 4.15).

Also: N. Ordoñez, *Hyperspaces through regular and meager subcontinua*, Topology Appl. 300 (2021), 107760, https://doi.org/10.1016/j.topol.2021.107760 (Lemma 6.3: adding a closed set with empty interior does not change the interior).

### 4.2 Camargo–Ordoñez–Ramírez (2024)

- Finite $\mathcal D(X)$ is determined by its minimal elements, which have pairwise disjoint interiors and cover $X$ (Theorem 3.16; Proposition 3.15).
- $|\mathcal D(X)|\notin\{2,4,5,8,9\}$ (Proposition 3.18).
- **$\mathcal D(X)$ is never homeomorphic to $\mathbb N$** (Theorem 3.25; also Ramírez, Teorema 3.2.13). Read this proof carefully: it is the closest existing result to Problem Q, since it is an obstruction for a countable target.

### 4.3 Ramírez thesis (2023)

- $\mathcal D(X)$ is always a $\Pi^0_3$ subset of $C(X)$ (Teorema 2.0.2).
- **Null chain example:** $\mathcal D(X)\cong\omega^2$ (Ejemplo 3.2.1). Countable, but with isolated points.
- $\mathcal D([0,1]^2)$ is not $G_\delta$ in $C([0,1]^2)$ (p. 23): both regular and empty-interior continua are dense, and Baire category applies. **This is the only known mechanism making $\mathcal D(X)$ non-$G_\delta$**, and a Q-example needs exactly that (Section 5, N3).
- Finite unions of copies of the null chain joined at a point (Section 3.2.1).

### 4.4 The author's previous work (use the techniques, do not redo them)

**(a) All finite cardinalities** — https://github.com/LucasAlves8Sp/ALL-FINITE-CARDINALITIES-OF-THE-HYPERSPACE-OF-REGULAR-SUBCONTINUA
- $|\mathcal D(X)|=k$ is possible iff $k\notin\{2,4,5,8,9,16\}$; finite $\mathcal D(X)$ corresponds to connected induced subgraphs of a finite graph, realized by Knaster continua glued at points. Formally verified in Lean.
- Reusable tool, the **key lemma**: a regular subcontinuum meeting the interior of an indecomposable piece contains the whole piece (boundary bumping plus indecomposability).

**(b) The irrational case** — repository above. Theorem A: there is $X\subseteq\ell^2$ with $\mathcal D(X)\cong\mathbb N^{\mathbb N}\cong\mathbb I$. Tools you may cite directly (from the paper `regular-subcontinua-irrationals.tex`):
- *Unions lemma (§2):* the closure of any union of regular closed sets is regular closed.
- *Fact on meager sets (§2):* if $\operatorname{int}B=\emptyset$ and $A,B$ closed, then $\operatorname{int}(A\cup B)=\operatorname{int}A$.
- *Null tree construction (§3):* pieces are scaled Knaster continua in pairwise orthogonal planes of $\ell^2$, indexed by a rooted tree; non-root pieces meet their parent in one point; attaching points on a piece lie in distinct composants. **Blocks** have dense interior; **spines** have empty interior and carry densely attached child blocks.
- *Retractions and crossing lemma (§4):* a subcontinuum meeting two branches at a piece $M$ contains $M$. *Pieces are atoms:* a subcontinuum whose interior meets a piece contains it.
- *Description theorem (Theorem 4.6):* $F=\{P: P\subseteq A\}$ for some $A\in\mathcal D(X)$ iff $F$ contains a block, is convex in the tree, and at each included spine the included children are attached densely. The coding $A\mapsto F$ is a homeomorphism onto a $G_\delta$ subset of $2^{\mathcal P}$ (Propositions 5.2–5.3).
- *Non-local-compactness (Proposition 5.4):* near every $A$ there are $A_k\in\mathcal D(X)$ converging in $C(X)$ to a **non-regular** continuum $A^*$ (adding a spine with a tail of its children, or deleting finitely many child subtrees of an included spine).
- *Null fan example (§2):* $n$ shrinking indecomposable pieces at one point give $\mathcal D(X)\cong 2^{\mathbb N}\setminus\{\emptyset\}$.

## 5. Necessary conditions for a Q-example (use them to discard candidates fast)

Let $X$ satisfy $\mathcal D(X)\cong\mathbb Q$. Each item is either cited or a short argument you must check and then use.

- **N1.** $X$ is decomposable and not locally connected (4.1).
- **N2.** $\mathcal D(X)$ is countably infinite with no isolated points. In particular $X$ itself is a Hausdorff limit of proper regular subcontinua.
- **N3 (descriptive complexity).** $\mathcal D(X)$ is countable, hence $F_\sigma$ in $C(X)$, but not completely metrizable, hence **not $G_\delta$** in $C(X)$ (Alves de Almeida, §6.1). Therefore **any coding of $\mathcal D(X)$ as an open/closed/density-type ($G_\delta$) subset of a Cantor cube cannot work.** The admissible codes must form a countable, dense-in-itself, non-Polish set, i.e. regularity must enforce a **global finiteness** condition (an $F_\sigma$, non-$G_\delta$ condition), not only local conditions.
- **N4 (nowhere local compactness).** $\mathbb Q$ has no compact neighborhoods, so in every neighborhood of every $A\in\mathcal D(X)$ there must be a sequence of regular subcontinua whose $C(X)$-limit is **not regular** (as in Proposition 5.4 of the irrationals paper).
- **N5 (no independent fans; generalizes Remark 6.1 "Independent fans" of the irrationals paper).** If $A\subsetneq A_n\in\mathcal D(X)$, $A_n\to A$, and there are points $x_n\in A_n\setminus\operatorname{cl}\bigcup_{m\neq n}A_m$, then $\Theta\mapsto\operatorname{cl}\bigcup_{n\in\Theta}A_n$ injects $2^{\mathbb N}$ into every neighborhood of $A$ (by the unions lemma these sets are regular, and they are connected because each contains $A$). **So upward perturbations of any $A$ must not have separated private parts**: they must be nested, overlapping, or forced together.
- **N6 (increasing limits stay regular).** If $A_1\subseteq A_2\subseteq\cdots$ in $\mathcal D(X)$, then $A_n\to\operatorname{cl}\bigcup_nA_n\in\mathcal D(X)$ (unions lemma plus connectedness of increasing unions). So a non-regular limit as required by N4 must come from **non-monotone or decreasing** approximations.
- **N7 (Theorem 3.25 of CORa).** Read its proof and record exactly which property of a countable discrete $\mathcal D(X)$ it contradicts; check whether the same argument, or a refinement, forbids every countable dense-in-itself $\mathcal D(X)$. If it does, that is a negative solution.

## 6. Strategies that have already failed (do not repeat them; learn from them)

From the irrationals paper (§6) and its development history:

1. **Tree coding with convexity + density (the irrational construction).** Produces a $G_\delta$ code space, hence a Polish $\mathcal D(X)$; violates N3. Moreover dense independent attachments give $2^{\aleph_0}$ regular subcontinua in every open set; violates N5.
2. **All-block trees (no spines).** Code space = nonempty convex subsets of the tree, closed in $2^{\mathcal P}\setminus\{\emptyset\}$, hence locally compact; violates N4.
3. **Leaf blocks.** A block without children is isolated in $\mathcal D(X)$; violates N2.
4. **Null fans** ($2^{\mathbb N}\setminus\{\emptyset\}$): uncountable and locally compact.
5. **Nested approximation along a null chain** (Ramírez, Ejemplo 3.2.1): countable ($\omega^2$) but every finite sub-chain $F_{n,m}$ is isolated; violates N2. Finite unions of such chains at a point stay scattered.
6. **"Core-protection" conjecture** of an earlier draft: false, refuted by the null chain of Ejemplo 3.2.1. Do not reintroduce it.
7. **Strategies tried in the earlier chat** (https://claude.ai/share/aa7e10e9-2f8e-40fa-b0eb-8bb558f80d3a):
   *[TO BE FILLED IN: list each strategy tried there and the exact reason it failed.]*

**The central tension** (the summary in §6.4 of the irrationals paper): nested approximation keeps $\mathcal D(X)$ countable but leaves isolated points; independent dense attachment removes isolated points but creates continuum many nearby regular subcontinua and a Polish code space. A Q-example needs a third mechanism: every regular subcontinuum must be approximable (no isolated points), the approximations must be **dependent** (N5), and the admissible configurations must be **finitely describable** (N3).

## 7. Lines of attack (heuristics, all UNVERIFIED — test them, do not assume them)

**Positive direction.**
- **Target code spaces.** Both the finite nonempty subsets of $\mathbb N$ and the cofinite subsets of $\mathbb N$, with the product topology, are countable without isolated points, hence $\cong\mathbb Q$. A natural goal: a continuum whose regular subcontinua are coded by "finitely many deviations from a canonical configuration". By N3, the finiteness must be forced **globally** by regularity or connectedness; find a geometric mechanism that makes "infinitely many deviations" produce a non-regular or disconnected set (note the unions lemma makes closures of unions of regular sets regular, so the mechanism must break **connectedness** or act through **intersections/deletions**, compare N6).
- **Dependent perturbations.** Look for structures where the small regular continua near $A$ are nested tails (as in the null chain, where $T_n\supseteq T_{n+1}$) rather than independent blades, and where every finite configuration also receives such tails, so that nothing is isolated. Example to test first: a null chain hanging from a piece $K$ whose links converge back to a point of $K$ (a "loop chain"); then $K\cup$(tail) $\to K$ decreasingly. Check carefully whether iterating this to remove all isolated points re-creates an independent fan (N5); a quick analysis suggests it does if every small loop structure is regular on its own, so look for versions where the small structures are regular **only together with** something larger (e.g. connected through empty-interior pieces, as spines are in the irrationals paper).
- **Non-$G_\delta$ mechanism.** Ramírez's square argument (4.3) is the only known source of non-$G_\delta$ behavior: regular and empty-interior continua are both dense in an open region of $C(X)$. Investigate whether a controlled version (inside one piece, combined with indecomposable "atoms" that keep the count countable) can produce the required $F_\sigma$, non-$G_\delta$ hyperspace.
- Other admissible tools: inverse limits with controlled bonding maps; decompositions of the null tree; gluing along composants. For each, prove the exhaustive list of regular subcontinua before computing any topology.

**Negative direction.**
- Try to prove: *if $\mathcal D(X)$ is countable, then $\mathcal D(X)$ has an isolated point* (or is scattered). This would solve Q negatively. Natural tools: N5–N6, Baire category in the compact space $\operatorname{cl}_{C(X)}\mathcal D(X)$, the $\Pi^0_3$ bound, boundary bumping, and the proof of CORa Theorem 3.25. Pay attention to the maximal element $X$ and to minimal regular subcontinua (do they exist when $\mathcal D(X)$ is countable?).

Alternate between the two directions: when a construction fails, extract the failure as a lemma and try to turn it into an impossibility theorem; when an impossibility proof stalls, extract the configuration that escapes it and try to build it.

## 8. Verification requirements for any candidate $X$

1. $X$ is a continuum (compact, connected, metric); give an explicit realization (for example in $\ell^2$ as in the irrationals paper).
2. The **complete** list of regular subcontinua, with a proof of exhaustiveness.
3. Countability of $\mathcal D(X)$.
4. For each $A\in\mathcal D(X)$, an explicit sequence of **distinct** regular subcontinua converging to $A$ in $d_H$.
5. Conclusion via Sierpiński's theorem.
6. Adversarial check: search for extra regular subcontinua, isolated points, independent fans (N5) and uncountable families before claiming success. Keep counterexamples to your own lemmas; they are results.

## 9. Final report: format (university exam style)

Write the report as a model solution to an exam, readable by a strong graduate student.

1. **Problem statement**: exact statement, source, and current status with the date of your literature check.
2. **Answer in one paragraph**: what you proved (solution, impossibility, or strongest partial result).
3. **Definitions**: every definition (old or new) is followed by
   - *Intuition*: what the object looks like;
   - *Purpose*: what it is meant to accomplish in the argument.
4. **Results**: every lemma, proposition and theorem has
   - *Motivation*: why it is needed and where it is used;
   - *Statement*;
   - *Proof*, complete, with every cited result given by source and number;
   - *Remark* (when useful): what goes wrong without each hypothesis.
5. **Main theorem and proof**, assembled from the results above.
6. **Proof ledger**: every claim labelled PROVED, KNOWN FROM THE LITERATURE (with citation), CONJECTURAL, or UNRESOLVED.
7. If not fully solved: the strongest result obtained, the precise obstruction met by each attempt, and **new lines of attack**, each with one narrow, checkable next lemma and an explanation of how proving it would advance Problem Q.
8. **References** actually used, with links and what each one contributes.