# AI disclosure

*This is the AI disclosure of the paper and its section on the Lean formalization, reproduced as they appear there. Theorem numbers refer to the paper.*

## Declaration of AI assistance

The author used Fable 5.2 (Claude Fable 5.2, Anthropic) and ChatGPT-Astra extensively during the development of this work. These systems assisted with mathematical exploration, the formulation and development of proofs, theorem verification, proofreading, manuscript drafting, and editorial revision. In particular, the statements and proofs in this paper were proposed, developed and cross-checked in interaction with these systems, and the manuscript was drafted with their assistance.

The models involved in obtaining the results were Opus 5.5, Fable 5.2 and ChatGPT-Astra. Fable 5.2 carried out the main research. ChatGPT-Astra rechecked the arguments, compared them with the literature and re-derived the results. The author conducted the investigation: he chose the questions to be answered in view of the obstructions met in proving the result, redirected the search for results, and edited and checked the text. The literature search underlying the statements about prior work was carried out with the same assistance on November 10, 2026; it found no earlier resolution of the rational case of Question 1.1.

The Lean code of the formalization described in the next section, both statements and proofs, was written by Fable 5.2 at the author's request.

The author takes responsibility for the content of the paper.

## Formalization in Lean 4

The theorems of this paper have been formalized in Lean 4 with the library Mathlib. The development is in [`lean/`](lean/) and was compiled with Lean `v4.35.0-rc2` and the Mathlib release of the same tag.

*What is formalized.* Theorems 1.2, 1.4 and 1.5, Lemma 3.2, Theorem 3.4, Lemma 4.1, Proposition 4.3, Theorem 4.4, Corollary 4.5, Lemma 4.6, Theorem 5.1, Lemma 6.2, Proposition 6.3, Corollary 6.5 and Proposition 7.5, each with the hypotheses stated in the paper and no additional one. In particular the file `Challenge.lean` contains the statement that there is no metric continuum $X$ with $\mathcal D(X)$ homeomorphic to $\mathbb Q$. The hyperspace $C(X)$ is modelled as the subspace of connected members of Mathlib's hyperspace of nonempty compact sets, whose topology is that of the Hausdorff metric. Every formal proof is complete, uses no axiom beyond the three standard ones of Lean with classical logic (`propext`, `Classical.choice`, `Quot.sound`), and was accepted by the Lean kernel and by the independent proof checkers run through the tool Comparator. The repository records exactly which checks were run and under which conditions.

*What is not formalized.* Examples 7.1, 7.2 and 7.3, the remarks, and Lemmas 2.3 and 2.4 in the form stated in the paper. The correspondence between the formal statements and the statements of the paper has so far been checked only by the AI system that wrote them.

*Relation to the written proofs.* The formal proofs establish the statements above, but they do not follow the written proofs step by step. They do not use boundary bumping (Lemma 2.4): connectedness is handled through separations by closed sets. Lemma 2.3 is replaced by a single dichotomy: a closed set is a finite union of connected relatively clopen subsets, or it contains infinitely many pairwise disjoint nonempty relatively clopen subsets. In Theorem 5.1 the tree of ordered covers is replaced by a sequence of finite families of pairs $P\subseteq P'$ of nested sets. The fact that $\mathcal D(X)$ is a Borel subset of $C(X)$, cited from Ramírez Angarita's thesis in the proof of Corollary 6.5, is proved in the formalization. The formalization also shows that Proposition 4.3(2) does not need the hypothesis that $\mathcal D(X)$ is countable.
