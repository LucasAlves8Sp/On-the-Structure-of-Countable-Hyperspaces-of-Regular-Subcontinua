module

public import RegularSubcontinua

public section

/-!
# Proved solution

Every declaration below has the same name and the same statement as its
counterpart in `Challenge.lean`. The proofs are in the `RegularSubcontinua`
library; this file only restates the results. The definitions used in the
statements are those of `RegularSubcontinua/Defs.lean`, which are copied
verbatim from `Challenge.lean`.
-/

open Set Function TopologicalSpace
open scoped Cardinal

universe u

namespace RegularSubcontinua

section Results

variable {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- Bridge between the two descriptions of `D(X)`: a subset of `X` is a regular
subcontinuum iff it is the underlying set of a member of `regular X`. -/
theorem isRegSubcontinuum_iff_exists_mem_regular (A : Set X) :
    IsRegSubcontinuum A ↔ ∃ K ∈ regular X, (K.1 : Set X) = A :=
  isRegSubcontinuum_iff_exists A

/-- Lemma 3.2 (independent families). -/
theorem card_eq_continuum_of_independent {A : Set X} {C : ℕ → Set X}
    (hA : IsRegSubcontinuum A) (hC : ∀ n, IsRegSubcontinuum (C n))
    (h : IsIndependentOver A C) : #(↥(regular X)) = 𝔠 :=
  card_of_independent hA hC h

/-- Theorem 3.4 (blister theorem). -/
theorem card_eq_continuum_of_blisters {A : Set X} {O : ℕ → Set X}
    (hA : IsRegSubcontinuum A) (hopen : ∀ n, IsOpen (O n))
    (hne : ∀ n, (O n).Nonempty) (hsub : ∀ n, O n ⊆ A)
    (hdisj : Pairwise (Disjoint on O))
    (hfin : ∀ F : Finset ℕ, IsRegSubcontinuum (A \ ⋃ n ∈ F, O n)) :
    #(↥(regular X)) = 𝔠 :=
  card_of_blisters hA hopen hne hsub hdisj hfin

/-- Lemma 4.1 (complement lemma), with `R = regDiff B A`. -/
theorem complement_lemma (hcount : (regular X).Countable) {A B : Set X}
    (hA : IsRegSubcontinuum A) (hB : IsRegSubcontinuum B)
    (hAB : (A ∩ B).Nonempty) (hBA : ¬ B ⊆ A) :
    (regDiff B A).Nonempty ∧ IsRegularClosed (regDiff B A) ∧ regDiff B A ⊆ B ∧
    Disjoint (regDiff B A) (interior A) ∧ A ∪ B = A ∪ regDiff B A ∧
    (∀ C ∈ components (regDiff B A), (C ∩ A).Nonempty) ∧
    (components (regDiff B A)).Finite ∧
    (∀ C ∈ components (regDiff B A), IsRegSubcontinuum C) :=
  complement_lemma' hcount hA hB hAB hBA

/-- Proposition 4.3 (1). -/
theorem isFiniteUnion_operations (hcount : (regular X).Countable) {F G : Set X}
    (hF : IsFiniteUnion F) (hG : IsFiniteUnion G) :
    IsFiniteUnion (F ∪ G) ∧ IsFiniteUnion (regDiff F G) ∧
    IsFiniteUnion (regMeet F G) :=
  ⟨hF.union hG, isFiniteUnion_regDiff hcount hF hG, isFiniteUnion_regMeet hcount hF hG⟩

/-- Proposition 4.3 (2). -/
theorem components_of_isFiniteUnion (hcount : (regular X).Countable) {F : Set X}
    (hF : IsFiniteUnion F) :
    (components F).Finite ∧ ∀ C ∈ components F, IsRegSubcontinuum C :=
  components_of_isFiniteUnion' hF

/-- Theorem 4.4 (absorption). -/
theorem absorption (hcount : (regular X).Countable) {N A : Set X}
    (hN : IsMinimalReg N) (hA : IsRegSubcontinuum A) :
    N ⊆ A ∨ Disjoint N (interior A) :=
  absorption' hcount hN hA

/-- Corollary 4.5. -/
theorem minimal_disjoint_interior (hcount : (regular X).Countable) {N N' : Set X}
    (hN : IsMinimalReg N) (hN' : IsMinimalReg N') (hne : N ≠ N') :
    Disjoint N (interior N') :=
  minimal_disjoint_interior' hcount hN hN' hne

/-- Lemma 4.6 (decreasing intersections), with `K = ⋂ n, A n`. -/
theorem decreasing_intersection (hcount : (regular X).Countable) {A : ℕ → Set X}
    (hA : ∀ n, IsRegSubcontinuum (A n)) (hanti : Antitone A) :
    IsFiniteUnion (closure ((⋂ n, A n)ᶜ)) ∧
    IsFiniteUnion (closure (interior (⋂ n, A n))) ∧
    ((interior (⋂ n, A n)).Nonempty →
      ∃ B : Set X, IsRegSubcontinuum B ∧ B ⊆ ⋂ n, A n) :=
  decreasing_intersection' hcount hA hanti

/-- Theorem 5.1 (density of the minimal elements). -/
theorem dense_interior_minimal (hcount : (regular X).Countable) :
    Dense (⋃ (N : Set X) (_ : IsMinimalReg N), interior N) :=
  dense_interior_minimal' hcount

/-- Lemma 6.2 (a), (b), (c). -/
theorem atomicFamily_basic {P : Set (Set X)} (hP : IsAtomicFamily P) :
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (interior p) (interior q)) ∧
    P.Countable ∧
    (∀ A : Set X, IsRegSubcontinuum A →
      (∃ p ∈ P, p ⊆ A) ∧ A = closure (⋃₀ {p | p ∈ P ∧ p ⊆ A})) ∧
    P = {N | IsMinimalReg N} :=
  atomicFamily_basic' hP

/-- Proposition 6.3 (a): `A ↦ P(A)` is a bijection from `D(X)` onto the
nonempty sets of atoms with connected closed union, with inverse
`S ↦ closure (⋃₀ S)`. -/
theorem atomicFamily_coding {P : Set (Set X)} (hP : IsAtomicFamily P) :
    Set.BijOn (fun A : Set X => {p | p ∈ P ∧ p ⊆ A}) {A | IsRegSubcontinuum A}
      {S | S ⊆ P ∧ S.Nonempty ∧ IsConnected (closure (⋃₀ S))} ∧
    ∀ S : Set (Set X), S ⊆ P → S.Nonempty → IsConnected (closure (⋃₀ S)) →
      {p | p ∈ P ∧ p ⊆ closure (⋃₀ S)} = S :=
  atomicFamily_coding' hP

/-- Proposition 6.3 (b), first part. -/
theorem atomicFamily_open_of_mem {P : Set (Set X)} (hP : IsAtomicFamily P)
    {p : Set X} (hp : p ∈ P) :
    IsOpen {K : ↥(regular X) | ((K.1.1 : Set X) ∩ interior p).Nonempty} ∧
    {K : ↥(regular X) | ((K.1.1 : Set X) ∩ interior p).Nonempty} =
      {K : ↥(regular X) | p ⊆ (K.1.1 : Set X)} ∧
    ∀ q ∈ P, q ≠ p → Disjoint q (interior p) :=
  atomicFamily_open_of_mem' hP hp

/-- Proposition 6.3 (b), second part: the atoms form a discrete subspace. -/
theorem atomicFamily_discrete {P : Set (Set X)} (hP : IsAtomicFamily P) :
    DiscreteTopology ↥{K : ↥(regular X) | (K.1.1 : Set X) ∈ P} :=
  atomicFamily_discrete' hP

/-- Theorem 1.5. -/
theorem isGdelta_regular_of_isDAtomic (h : IsDAtomic X) : IsGδ (regular X) :=
  isGδ_regular_of_isDAtomic' h

/-- Theorem 1.4 (structure theorem), parts (1)-(4). -/
theorem structure_theorem (hcount : (regular X).Countable) :
    (∀ A N : Set X, IsRegSubcontinuum A → IsMinimalReg N →
      N ⊆ A ∨ Disjoint N (interior A)) ∧
    (∀ N N' : Set X, IsMinimalReg N → IsMinimalReg N' → N ≠ N' →
      Disjoint (interior N) (interior N')) ∧
    Dense (⋃ (N : Set X) (_ : IsMinimalReg N), interior N) ∧
    (∀ A : Set X, IsRegSubcontinuum A →
      A = closure (⋃₀ {N | IsMinimalReg N ∧ N ⊆ A}) ∧
      ∃ N : Set X, IsMinimalReg N ∧ N ⊆ A) :=
  structure_theorem' hcount

/-- Proposition 7.5: no chain of `D(X)` has the order type of `ℚ`. -/
theorem no_rational_chain (hcount : (regular X).Countable) :
    ¬ ∃ f : ℚ → Set X, (∀ q, IsRegSubcontinuum (f q)) ∧ StrictMono f :=
  no_rational_chain' hcount

end Results

/-- Theorem 1.2 (Main Theorem). If `X` is a metric continuum and `D(X)` is
countable, then `D(X)` is a `G_δ` subset of `C(X)`, it is completely
metrizable and scattered, and its isolated points are dense. -/
theorem main_theorem (X : Type u) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] (hcount : (regular X).Countable) :
    IsGδ (regular X) ∧ IsCompletelyMetrizableSpace ↥(regular X) ∧
    IsScattered ↥(regular X) ∧
    Dense {K : ↥(regular X) | IsOpen ({K} : Set ↥(regular X))} :=
  main_theorem' hcount

/-- Theorem 1.2, last assertion: for a metric continuum `X`, `D(X)` is not
homeomorphic to `ℚ`. -/
theorem not_homeomorphic_rat (X : Type u) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] : IsEmpty (↥(regular X) ≃ₜ ℚ) :=
  not_homeomorphic_rat'

/-- The same assertion with the continuum quantified explicitly. -/
theorem no_continuum_with_regular_hyperspace_rat :
    ¬ ∃ (X : Type u) (_ : MetricSpace X) (_ : CompactSpace X)
      (_ : ConnectedSpace X), Nonempty (↥(regular X) ≃ₜ ℚ) := by
  rintro ⟨X, _, _, _, ⟨e⟩⟩
  exact (not_homeomorphic_rat' (X := X)).false e

/-- Corollary 6.5 (dichotomy). The two alternatives exclude each other because
`ℵ₀ < 𝔠`. -/
theorem dichotomy (X : Type u) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] :
    #(↥(regular X)) = 𝔠 ∨
    ((regular X).Countable ∧ IsScattered ↥(regular X) ∧
      IsCompletelyMetrizableSpace ↥(regular X) ∧ IsDAtomic X) :=
  dichotomy'

/-- Corollary 6.5, exclusiveness: the two alternatives of `dichotomy` exclude
each other. -/
theorem dichotomy_exclusive (X : Type u) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] (h : #(↥(regular X)) = 𝔠) : ¬ (regular X).Countable :=
  not_countable_of_card_eq_continuum h

/-- Not in the paper. The hypothesis "`D(X)` is countable" of the main theorem
is satisfiable: some metric continuum has countable `D(X)`. -/
theorem countable_hypothesis_satisfiable :
    ∃ (X : Type u) (_ : MetricSpace X) (_ : CompactSpace X)
      (_ : ConnectedSpace X), (regular X).Countable :=
  ⟨PUnit.{u + 1}, inferInstance, inferInstance, connectedSpace_punit, countable_regular_punit⟩

end RegularSubcontinua
