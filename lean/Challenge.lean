module

public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Rat
public import Mathlib.SetTheory.Cardinal.Continuum

@[expose] public section

/-!
# On the structure of countable hyperspaces of regular subcontinua

Statement surface for the paper of the same title by Lucas Alves de Almeida
(numbering below is that of the paper, 20-page version of 11 November 2026).

This file compiles with Lean `v4.35.0-rc2` and Mathlib at tag `v4.35.0-rc2`.
Every statement below is closed by `sorry` here and proved, under the same name,
in `Solution.lean`.

Conventions.

* A *continuum* is a nonempty compact connected metric space: the standing
  hypotheses `[MetricSpace X] [CompactSpace X] [ConnectedSpace X]`
  (`ConnectedSpace` includes nonemptiness). No other hypothesis is used.
* `C(X)` is `Subcontinua X`, a subtype of Mathlib's
  `TopologicalSpace.NonemptyCompacts X`. Its topology is the subspace topology
  of the Vietoris topology, which Mathlib identifies by construction with the
  topology of the Hausdorff metric on `NonemptyCompacts X`.
* `D(X)` is `regular X : Set (Subcontinua X)`, with the subspace topology.
* "`D(X)` is countable" is `(regular X).Countable`; this includes finite.
* Structural statements are about subsets `A : Set X` satisfying
  `IsRegSubcontinuum A`. The first theorem below ties this predicate to
  membership in `regular X`.
* Interiors and closures are always taken in `X`.
-/

open Set Function TopologicalSpace
open scoped Cardinal

universe u

namespace RegularSubcontinua

section Definitions

variable {X : Type u} [TopologicalSpace X]

/-- A set is regular closed if it is the closure of its interior. -/
def IsRegularClosed (s : Set X) : Prop :=
  closure (interior s) = s

/-- A regular subcontinuum of `X`, as a subset: compact, connected (hence
nonempty) and regular closed. -/
def IsRegSubcontinuum (A : Set X) : Prop :=
  IsCompact A ∧ IsConnected A ∧ IsRegularClosed A

variable (X) in
/-- The hyperspace `C(X)` of subcontinua of `X`. -/
abbrev Subcontinua : Type u :=
  {K : NonemptyCompacts X // IsConnected (K : Set X)}

variable (X) in
/-- The hyperspace `D(X)` of regular subcontinua, as a subset of `C(X)`. -/
def regular : Set (Subcontinua X) :=
  {K | IsRegularClosed (K.1 : Set X)}

/-- Definition 3.1. The sequence `C` is independent over `A`: each `C n` meets
`A` and is not contained in the closure of `A` together with the other
members. (In Lemma 3.2 the sets are regular subcontinua.) -/
def IsIndependentOver (A : Set X) (C : ℕ → Set X) : Prop :=
  ∀ n, (C n ∩ A).Nonempty ∧ ¬ C n ⊆ closure (A ∪ ⋃ (m : ℕ) (_ : m ≠ n), C m)

/-- Definition 2.1. The regularised difference `F ⊖ G`. -/
def regDiff (F G : Set X) : Set X :=
  closure (interior F \ G)

/-- Definition 2.1. The regularised meet `F ∧ G`. -/
def regMeet (F G : Set X) : Set X :=
  closure (interior F ∩ interior G)

/-- Definition 4.2. Membership in `𝓕(X)`: the empty set and the finite unions
of regular subcontinua. -/
def IsFiniteUnion (F : Set X) : Prop :=
  ∃ S : Set (Set X), S.Finite ∧ (∀ A ∈ S, IsRegSubcontinuum A) ∧ F = ⋃₀ S

/-- The set of connected components of the subspace `F`, as subsets of `X`. -/
def components (F : Set X) : Set (Set X) :=
  connectedComponentIn F '' F

/-- A minimal element of `D(X)` under inclusion. -/
def IsMinimalReg (N : Set X) : Prop :=
  IsRegSubcontinuum N ∧ ∀ B : Set X, IsRegSubcontinuum B → B ⊆ N → B = N

/-- Definition 6.1. An atomic family: regular subcontinua with the absorption
property (A1) whose interiors have dense union (A2). Pairwise disjointness of
the interiors is *not* assumed. -/
def IsAtomicFamily (P : Set (Set X)) : Prop :=
  (∀ p ∈ P, IsRegSubcontinuum p) ∧
  (∀ A : Set X, IsRegSubcontinuum A → ∀ p ∈ P,
    (interior A ∩ interior p).Nonempty → p ⊆ A) ∧
  Dense (⋃ p ∈ P, interior p)

variable (X) in
/-- Definition 6.1. `X` is `D`-atomic if it has an atomic family. -/
def IsDAtomic : Prop :=
  ∃ P : Set (Set X), IsAtomicFamily P

/-- A topological space is scattered if every nonempty subset has a point that
is isolated in that subset. -/
def IsScattered (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ S : Set Y, S.Nonempty → ∃ x ∈ S, ∃ U : Set Y, IsOpen U ∧ U ∩ S = {x}

end Definitions

section Results

variable {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- Bridge between the two descriptions of `D(X)`: a subset of `X` is a regular
subcontinuum iff it is the underlying set of a member of `regular X`. -/
theorem isRegSubcontinuum_iff_exists_mem_regular (A : Set X) :
    IsRegSubcontinuum A ↔ ∃ K ∈ regular X, (K.1 : Set X) = A := by
  sorry

/-- Lemma 3.2 (independent families). -/
theorem card_eq_continuum_of_independent {A : Set X} {C : ℕ → Set X}
    (hA : IsRegSubcontinuum A) (hC : ∀ n, IsRegSubcontinuum (C n))
    (h : IsIndependentOver A C) : #(↥(regular X)) = 𝔠 := by
  sorry

/-- Theorem 3.4 (blister theorem). -/
theorem card_eq_continuum_of_blisters {A : Set X} {O : ℕ → Set X}
    (hA : IsRegSubcontinuum A) (hopen : ∀ n, IsOpen (O n))
    (hne : ∀ n, (O n).Nonempty) (hsub : ∀ n, O n ⊆ A)
    (hdisj : Pairwise (Disjoint on O))
    (hfin : ∀ F : Finset ℕ, IsRegSubcontinuum (A \ ⋃ n ∈ F, O n)) :
    #(↥(regular X)) = 𝔠 := by
  sorry

/-- Lemma 4.1 (complement lemma), with `R = regDiff B A`. -/
theorem complement_lemma (hcount : (regular X).Countable) {A B : Set X}
    (hA : IsRegSubcontinuum A) (hB : IsRegSubcontinuum B)
    (hAB : (A ∩ B).Nonempty) (hBA : ¬ B ⊆ A) :
    (regDiff B A).Nonempty ∧ IsRegularClosed (regDiff B A) ∧ regDiff B A ⊆ B ∧
    Disjoint (regDiff B A) (interior A) ∧ A ∪ B = A ∪ regDiff B A ∧
    (∀ C ∈ components (regDiff B A), (C ∩ A).Nonempty) ∧
    (components (regDiff B A)).Finite ∧
    (∀ C ∈ components (regDiff B A), IsRegSubcontinuum C) := by
  sorry

/-- Proposition 4.3 (1). -/
theorem isFiniteUnion_operations (hcount : (regular X).Countable) {F G : Set X}
    (hF : IsFiniteUnion F) (hG : IsFiniteUnion G) :
    IsFiniteUnion (F ∪ G) ∧ IsFiniteUnion (regDiff F G) ∧
    IsFiniteUnion (regMeet F G) := by
  sorry

/-- Proposition 4.3 (2). -/
theorem components_of_isFiniteUnion (hcount : (regular X).Countable) {F : Set X}
    (hF : IsFiniteUnion F) :
    (components F).Finite ∧ ∀ C ∈ components F, IsRegSubcontinuum C := by
  sorry

/-- Theorem 4.4 (absorption). -/
theorem absorption (hcount : (regular X).Countable) {N A : Set X}
    (hN : IsMinimalReg N) (hA : IsRegSubcontinuum A) :
    N ⊆ A ∨ Disjoint N (interior A) := by
  sorry

/-- Corollary 4.5. -/
theorem minimal_disjoint_interior (hcount : (regular X).Countable) {N N' : Set X}
    (hN : IsMinimalReg N) (hN' : IsMinimalReg N') (hne : N ≠ N') :
    Disjoint N (interior N') := by
  sorry

/-- Lemma 4.6 (decreasing intersections), with `K = ⋂ n, A n`. -/
theorem decreasing_intersection (hcount : (regular X).Countable) {A : ℕ → Set X}
    (hA : ∀ n, IsRegSubcontinuum (A n)) (hanti : Antitone A) :
    IsFiniteUnion (closure ((⋂ n, A n)ᶜ)) ∧
    IsFiniteUnion (closure (interior (⋂ n, A n))) ∧
    ((interior (⋂ n, A n)).Nonempty →
      ∃ B : Set X, IsRegSubcontinuum B ∧ B ⊆ ⋂ n, A n) := by
  sorry

/-- Theorem 5.1 (density of the minimal elements). -/
theorem dense_interior_minimal (hcount : (regular X).Countable) :
    Dense (⋃ (N : Set X) (_ : IsMinimalReg N), interior N) := by
  sorry

/-- Lemma 6.2 (a), (b), (c). -/
theorem atomicFamily_basic {P : Set (Set X)} (hP : IsAtomicFamily P) :
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (interior p) (interior q)) ∧
    P.Countable ∧
    (∀ A : Set X, IsRegSubcontinuum A →
      (∃ p ∈ P, p ⊆ A) ∧ A = closure (⋃₀ {p | p ∈ P ∧ p ⊆ A})) ∧
    P = {N | IsMinimalReg N} := by
  sorry

/-- Proposition 6.3 (a): `A ↦ P(A)` is a bijection from `D(X)` onto the
nonempty sets of atoms with connected closed union, with inverse
`S ↦ closure (⋃₀ S)`. -/
theorem atomicFamily_coding {P : Set (Set X)} (hP : IsAtomicFamily P) :
    Set.BijOn (fun A : Set X => {p | p ∈ P ∧ p ⊆ A}) {A | IsRegSubcontinuum A}
      {S | S ⊆ P ∧ S.Nonempty ∧ IsConnected (closure (⋃₀ S))} ∧
    ∀ S : Set (Set X), S ⊆ P → S.Nonempty → IsConnected (closure (⋃₀ S)) →
      {p | p ∈ P ∧ p ⊆ closure (⋃₀ S)} = S := by
  sorry

/-- Proposition 6.3 (b), first part. -/
theorem atomicFamily_open_of_mem {P : Set (Set X)} (hP : IsAtomicFamily P)
    {p : Set X} (hp : p ∈ P) :
    IsOpen {K : ↥(regular X) | ((K.1.1 : Set X) ∩ interior p).Nonempty} ∧
    {K : ↥(regular X) | ((K.1.1 : Set X) ∩ interior p).Nonempty} =
      {K : ↥(regular X) | p ⊆ (K.1.1 : Set X)} ∧
    ∀ q ∈ P, q ≠ p → Disjoint q (interior p) := by
  sorry

/-- Proposition 6.3 (b), second part: the atoms form a discrete subspace. -/
theorem atomicFamily_discrete {P : Set (Set X)} (hP : IsAtomicFamily P) :
    DiscreteTopology ↥{K : ↥(regular X) | (K.1.1 : Set X) ∈ P} := by
  sorry

/-- Theorem 1.5. -/
theorem isGdelta_regular_of_isDAtomic (h : IsDAtomic X) : IsGδ (regular X) := by
  sorry

/-- Theorem 1.4 (structure theorem), parts (1)-(4). -/
theorem structure_theorem (hcount : (regular X).Countable) :
    (∀ A N : Set X, IsRegSubcontinuum A → IsMinimalReg N →
      N ⊆ A ∨ Disjoint N (interior A)) ∧
    (∀ N N' : Set X, IsMinimalReg N → IsMinimalReg N' → N ≠ N' →
      Disjoint (interior N) (interior N')) ∧
    Dense (⋃ (N : Set X) (_ : IsMinimalReg N), interior N) ∧
    (∀ A : Set X, IsRegSubcontinuum A →
      A = closure (⋃₀ {N | IsMinimalReg N ∧ N ⊆ A}) ∧
      ∃ N : Set X, IsMinimalReg N ∧ N ⊆ A) := by
  sorry

/-- Proposition 7.5: no chain of `D(X)` has the order type of `ℚ`. -/
theorem no_rational_chain (hcount : (regular X).Countable) :
    ¬ ∃ f : ℚ → Set X, (∀ q, IsRegSubcontinuum (f q)) ∧ StrictMono f := by
  sorry

end Results

/-- Theorem 1.2 (Main Theorem). If `X` is a metric continuum and `D(X)` is
countable, then `D(X)` is a `G_δ` subset of `C(X)`, it is completely
metrizable and scattered, and its isolated points are dense. -/
theorem main_theorem (X : Type u) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] (hcount : (regular X).Countable) :
    IsGδ (regular X) ∧ IsCompletelyMetrizableSpace ↥(regular X) ∧
    IsScattered ↥(regular X) ∧
    Dense {K : ↥(regular X) | IsOpen ({K} : Set ↥(regular X))} := by
  sorry

/-- Theorem 1.2, last assertion: for a metric continuum `X`, `D(X)` is not
homeomorphic to `ℚ`. -/
theorem not_homeomorphic_rat (X : Type u) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] : IsEmpty (↥(regular X) ≃ₜ ℚ) := by
  sorry

/-- The same assertion with the continuum quantified explicitly. -/
theorem no_continuum_with_regular_hyperspace_rat :
    ¬ ∃ (X : Type u) (_ : MetricSpace X) (_ : CompactSpace X)
      (_ : ConnectedSpace X), Nonempty (↥(regular X) ≃ₜ ℚ) := by
  sorry

/-- Corollary 6.5 (dichotomy). The two alternatives exclude each other because
`ℵ₀ < 𝔠`. -/
theorem dichotomy (X : Type u) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] :
    #(↥(regular X)) = 𝔠 ∨
    ((regular X).Countable ∧ IsScattered ↥(regular X) ∧
      IsCompletelyMetrizableSpace ↥(regular X) ∧ IsDAtomic X) := by
  sorry

/-- Corollary 6.5, exclusiveness: the two alternatives of `dichotomy` exclude
each other. -/
theorem dichotomy_exclusive (X : Type u) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] (h : #(↥(regular X)) = 𝔠) : ¬ (regular X).Countable := by
  sorry

/-- Not in the paper. The hypothesis "`D(X)` is countable" of the main theorem
is satisfiable: some metric continuum has countable `D(X)`. -/
theorem countable_hypothesis_satisfiable :
    ∃ (X : Type u) (_ : MetricSpace X) (_ : CompactSpace X)
      (_ : ConnectedSpace X), (regular X).Countable := by
  sorry

end RegularSubcontinua
