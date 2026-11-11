module

public import RegularSubcontinua.Main
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.MetricSpace.Perfect

@[expose] public section

/-!
# Corollary 6.5 (dichotomy)

`D(X)` is a Borel subset of `C(X)`, hence it is countable or has cardinality `𝔠`.
-/

open Set Function TopologicalSpace Topology
open scoped Cardinal

universe u

namespace RegularSubcontinua

variable {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- `D(X)` is a Borel subset of `C(X)`. -/
theorem measurableSet_regular [MeasurableSpace (Subcontinua X)] [BorelSpace (Subcontinua X)] :
    MeasurableSet (regular X) := by
  classical
  have hb : IsTopologicalBasis (countableBasis X) := isBasis_countableBasis X
  have : Countable ↥(countableBasis X) := (countable_countableBasis X).to_subtype
  let C : ℕ → Finset ↥(countableBasis X) → Set (Subcontinua X) := fun m S =>
    (⋂ U ∈ S, {K : Subcontinua X | (U : Set X) ⊆ (K.1 : Set X)}) ∩
      {K : Subcontinua X |
        (K.1 : Set X) ⊆ Metric.thickening (1 / ((m : ℝ) + 1)) (⋃ U ∈ S, (U : Set X))}
  have hmem : ∀ (m : ℕ) (S : Finset ↥(countableBasis X)) (K : Subcontinua X), K ∈ C m S ↔
      (∀ U ∈ S, (U : Set X) ⊆ (K.1 : Set X)) ∧
      (K.1 : Set X) ⊆ Metric.thickening (1 / ((m : ℝ) + 1)) (⋃ U ∈ S, (U : Set X)) := by
    intro m S K
    simp only [C, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  have hC : ∀ m S, MeasurableSet (C m S) := by
    intro m S
    refine MeasurableSet.inter ?_ ?_
    · have hcl : IsClosed (⋂ U ∈ S, {K : Subcontinua X | (U : Set X) ⊆ (K.1 : Set X)}) :=
        isClosed_biInter fun (U : ↥(countableBasis X)) _ => isClosed_setOf_subset (U : Set X)
      exact hcl.measurableSet
    · exact ((NonemptyCompacts.isOpen_subsets_of_isOpen
        Metric.isOpen_thickening).preimage continuous_subtype_val).measurableSet
  have heq : regular X = ⋂ m : ℕ, ⋃ S : Finset ↥(countableBasis X), C m S := by
    ext K
    simp only [mem_iInter, mem_iUnion, hmem]
    constructor
    · intro hK m
      have hA : IsRegSubcontinuum (K.1 : Set X) := isRegSubcontinuum_coe ⟨K, hK⟩
      have hδ : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      have hcover : (K.1 : Set X) ⊆
          ⋃ U ∈ {U : ↥(countableBasis X) | (U : Set X) ⊆ (K.1 : Set X)},
            Metric.thickening (1 / ((m : ℝ) + 1)) (U : Set X) := by
        intro x hx
        have hx' : x ∈ closure (interior (K.1 : Set X)) := by
          rw [hA.isRegularClosed.eq]; exact hx
        obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.1 hx' _ hδ
        obtain ⟨U, hUb, hzU, hUsub⟩ := hb.exists_subset_of_mem_open hz isOpen_interior
        refine mem_iUnion₂.2 ⟨⟨U, hUb⟩, hUsub.trans interior_subset, ?_⟩
        exact Metric.mem_thickening_iff.2 ⟨z, hzU, hdist⟩
      obtain ⟨b', hb', hfin, hsub⟩ := hA.isCompact.elim_finite_subcover_image
        (fun U _ => Metric.isOpen_thickening) hcover
      refine ⟨hfin.toFinset, fun U hU => hb' (hfin.mem_toFinset.1 hU), ?_⟩
      intro x hx
      obtain ⟨U, hU, hxU⟩ := mem_iUnion₂.1 (hsub hx)
      exact Metric.thickening_subset_of_subset _
        (subset_iUnion₂ (s := fun (V : ↥(countableBasis X)) (_ : V ∈ hfin.toFinset) =>
          (V : Set X)) U (hfin.mem_toFinset.2 hU)) hxU
    · intro h
      have hKcl : IsClosed (K.1 : Set X) := K.1.isCompact.isClosed
      show closure (interior (K.1 : Set X)) = (K.1 : Set X)
      apply Subset.antisymm (closure_minimal interior_subset hKcl)
      intro x hx
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      obtain ⟨S, hS, hSsub⟩ := h m
      obtain ⟨z, hzS, hdist⟩ := Metric.mem_thickening_iff.1 (hSsub hx)
      obtain ⟨U, hUS, hzU⟩ := mem_iUnion₂.1 hzS
      exact ⟨z, interior_maximal (hS U hUS) (hb.isOpen U.2) hzU, hdist.trans hm⟩
  rw [heq]
  exact MeasurableSet.iInter fun m => MeasurableSet.iUnion fun S => hC m S

/-- Perfect set property for `D(X)`: if it is uncountable it has cardinality at least `𝔠`. -/
theorem continuum_le_of_not_countable (h : ¬ (regular X).Countable) :
    𝔠 ≤ #(↥(regular X)) := by
  classical
  have : PolishSpace (Subcontinua X) := polishSpace_subcontinua
  borelize (Subcontinua X)
  have hmeas : MeasurableSet (regular X) := measurableSet_regular
  obtain ⟨t', -, hpol, hcl, -⟩ := hmeas.isClopenable'
  obtain ⟨f, hrange, -, hinj⟩ :=
    @IsClosed.exists_nat_bool_injection_of_not_countable _ t' hpol _ hcl h
  refine continuum_le_card_regular
    (F := fun T : Set ℕ => ((f fun n => decide (n ∈ T)).1 : Set X)) ?_ ?_
  · intro T
    exact isRegSubcontinuum_coe ⟨_, hrange (mem_range_self _)⟩
  · intro T T' hTT'
    have h1 : (f fun n => decide (n ∈ T)) = f fun n => decide (n ∈ T') :=
      Subtype.ext (SetLike.coe_injective hTT')
    have h2 := hinj h1
    ext n
    have h3 := congrFun h2 n
    simpa using h3

/-- Corollary 6.5 (dichotomy). -/
theorem dichotomy' :
    #(↥(regular X)) = 𝔠 ∨
    ((regular X).Countable ∧ IsScattered ↥(regular X) ∧
      IsCompletelyMetrizableSpace ↥(regular X) ∧ IsDAtomic X) := by
  by_cases h : (regular X).Countable
  · obtain ⟨-, hcm, hsc, -⟩ := main_theorem' h
    exact Or.inr ⟨h, hsc, hcm, isDAtomic_of_countable h⟩
  · exact Or.inl (le_antisymm card_regular_le_continuum (continuum_le_of_not_countable h))

end RegularSubcontinua
