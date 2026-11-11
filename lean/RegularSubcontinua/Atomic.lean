module

public import RegularSubcontinua.Density
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Separation.GDelta

@[expose] public section

/-!
# `D`-atomic continua: Lemma 6.2, Proposition 6.3, Theorem 1.5
-/

open Set Function TopologicalSpace Topology
open scoped Cardinal

universe u

namespace RegularSubcontinua

variable {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

section Atoms

variable {P : Set (Set X)}

theorem IsAtomicFamily.reg (hP : IsAtomicFamily P) {p : Set X} (hp : p ∈ P) :
    IsRegSubcontinuum p := hP.1 p hp

theorem IsAtomicFamily.absorb (hP : IsAtomicFamily P) {A p : Set X} (hA : IsRegSubcontinuum A)
    (hp : p ∈ P) (h : (interior A ∩ interior p).Nonempty) : p ⊆ A := hP.2.1 A hA p hp h

theorem IsAtomicFamily.eq_of_inter (hP : IsAtomicFamily P) {p q : Set X} (hp : p ∈ P)
    (hq : q ∈ P) (h : (interior p ∩ interior q).Nonempty) : p = q :=
  Subset.antisymm (hP.absorb (hP.reg hq) hp (by rwa [inter_comm])) (hP.absorb (hP.reg hp) hq h)

theorem IsAtomicFamily.disjoint_interior (hP : IsAtomicFamily P) {p q : Set X} (hp : p ∈ P)
    (hq : q ∈ P) (hne : p ≠ q) : Disjoint (interior p) (interior q) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra h
  exact hne (hP.eq_of_inter hp hq (nonempty_iff_ne_empty.2 h))

/-- A distinct atom misses the interior of an atom. -/
theorem IsAtomicFamily.disjoint_atom (hP : IsAtomicFamily P) {p q : Set X} (hp : p ∈ P)
    (hq : q ∈ P) (hne : q ≠ p) : Disjoint q (interior p) :=
  ((hP.reg hq).isRegularClosed.disjoint_of_disjoint_interior isOpen_interior
    (hP.disjoint_interior hp hq (Ne.symm hne))).symm

theorem IsAtomicFamily.countable (hP : IsAtomicFamily P) : P.Countable :=
  Set.PairwiseDisjoint.countable_of_isOpen (s := fun p : Set X => interior p) (a := P)
    (fun _ hp _ hq hne => hP.disjoint_interior hp hq hne) (fun _ _ => isOpen_interior)
    (fun _ hp => (hP.reg hp).interior_nonempty)

theorem IsAtomicFamily.exists_atom (hP : IsAtomicFamily P) {A : Set X}
    (hA : IsRegSubcontinuum A) {U : Set X} (hU : IsOpen U) (hUA : (A ∩ U).Nonempty) :
    ∃ p ∈ P, p ⊆ A ∧ (U ∩ p).Nonempty := by
  have h1 : (interior A ∩ U).Nonempty := hA.isRegularClosed.inter_interior_nonempty hU hUA
  obtain ⟨z, ⟨hzA, hzU⟩, hzP⟩ :=
    dense_iff_inter_open.1 hP.2.2 _ (isOpen_interior.inter hU) h1
  obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hzP
  exact ⟨p, hp, hP.absorb hA hp ⟨z, hzA, hzp⟩, z, hzU, interior_subset hzp⟩

theorem IsAtomicFamily.eq_closure (hP : IsAtomicFamily P) {A : Set X}
    (hA : IsRegSubcontinuum A) : A = closure (⋃₀ {p | p ∈ P ∧ p ⊆ A}) := by
  apply Subset.antisymm
  · intro x hx
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨p, hp, hpA, z, hzo, hzp⟩ := hP.exists_atom hA ho ⟨x, hx, hxo⟩
    exact ⟨z, hzo, p, ⟨hp, hpA⟩, hzp⟩
  · exact closure_minimal (sUnion_subset fun p hp => hp.2) hA.isClosed

/-- Lemma 6.2. -/
theorem atomicFamily_basic' (hP : IsAtomicFamily P) :
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (interior p) (interior q)) ∧
    P.Countable ∧
    (∀ A : Set X, IsRegSubcontinuum A →
      (∃ p ∈ P, p ⊆ A) ∧ A = closure (⋃₀ {p | p ∈ P ∧ p ⊆ A})) ∧
    P = {N | IsMinimalReg N} := by
  have hb1 : ∀ A : Set X, IsRegSubcontinuum A → ∃ p ∈ P, p ⊆ A := by
    intro A hA
    obtain ⟨p, hp, hpA, -⟩ := hP.exists_atom hA isOpen_univ (by simpa using hA.nonempty)
    exact ⟨p, hp, hpA⟩
  refine ⟨fun p hp q hq hne => hP.disjoint_interior hp hq hne, hP.countable,
    fun A hA => ⟨hb1 A hA, hP.eq_closure hA⟩, ?_⟩
  ext N
  constructor
  · intro hN
    refine ⟨hP.reg hN, fun B hB hBN => ?_⟩
    obtain ⟨q, hq, hqB⟩ := hb1 B hB
    have hqN : q = N := by
      by_contra hne
      obtain ⟨z, hz⟩ := (hP.reg hq).interior_nonempty
      exact Set.disjoint_left.1 (hP.disjoint_atom hq hN (Ne.symm hne)) (hBN (hqB (interior_subset hz))) hz
    exact Subset.antisymm hBN (hqN ▸ hqB)
  · intro hN
    obtain ⟨p, hp, hpN⟩ := hb1 N hN.1
    rw [← hN.2 p (hP.reg hp) hpN]
    exact hp

theorem IsAtomicFamily.atoms_of_closure (hP : IsAtomicFamily P) {S : Set (Set X)}
    (hS : S ⊆ P) : {p | p ∈ P ∧ p ⊆ closure (⋃₀ S)} = S := by
  ext p
  constructor
  · rintro ⟨hp, hpS⟩
    by_contra hpnS
    have hd : Disjoint (interior p) (⋃₀ S) := by
      rw [Set.disjoint_left]
      rintro z hz ⟨q, hq, hzq⟩
      have hne : q ≠ p := fun h => hpnS (h ▸ hq)
      exact Set.disjoint_left.1 (hP.disjoint_atom hp (hS hq) hne) hzq hz
    obtain ⟨z, hz⟩ := (hP.reg hp).interior_nonempty
    exact Set.disjoint_left.1 (hd.symm.closure_left isOpen_interior) (hpS (interior_subset hz)) hz
  · intro hp
    exact ⟨hS hp, (subset_sUnion_of_mem hp).trans subset_closure⟩

/-- Proposition 6.3 (a). -/
theorem atomicFamily_coding' (hP : IsAtomicFamily P) :
    Set.BijOn (fun A : Set X => {p | p ∈ P ∧ p ⊆ A}) {A | IsRegSubcontinuum A}
      {S | S ⊆ P ∧ S.Nonempty ∧ IsConnected (closure (⋃₀ S))} ∧
    ∀ S : Set (Set X), S ⊆ P → S.Nonempty → IsConnected (closure (⋃₀ S)) →
      {p | p ∈ P ∧ p ⊆ closure (⋃₀ S)} = S := by
  refine ⟨⟨?_, ?_, ?_⟩, fun S hS _ _ => hP.atoms_of_closure hS⟩
  · intro A hA
    refine ⟨fun p hp => hp.1, ?_, ?_⟩
    · obtain ⟨p, hp, hpA, -⟩ := hP.exists_atom hA isOpen_univ (by simpa using hA.nonempty)
      exact ⟨p, hp, hpA⟩
    · show IsConnected (closure (⋃₀ {p | p ∈ P ∧ p ⊆ A}))
      rw [← hP.eq_closure hA]
      exact hA.isConnected
  · intro A hA B hB hAB
    have hAB' : {p | p ∈ P ∧ p ⊆ A} = {p | p ∈ P ∧ p ⊆ B} := hAB
    rw [hP.eq_closure hA, hP.eq_closure hB, hAB']
  · rintro S ⟨hSP, hSne, hSconn⟩
    refine ⟨closure (⋃₀ S), ?_, hP.atoms_of_closure hSP⟩
    exact isRegSubcontinuum_of_isClosed isClosed_closure hSconn
      (isRegularClosed_closure_sUnion fun p hp => (hP.reg (hSP hp)).isRegularClosed)

theorem continuous_coe_regular :
    Continuous fun K : ↥(regular X) => (K.1.1 : NonemptyCompacts X) :=
  continuous_subtype_val.comp continuous_subtype_val

/-- Proposition 6.3 (b), first part. -/
theorem atomicFamily_open_of_mem' (hP : IsAtomicFamily P) {p : Set X} (hp : p ∈ P) :
    IsOpen {K : ↥(regular X) | ((K.1.1 : Set X) ∩ interior p).Nonempty} ∧
    {K : ↥(regular X) | ((K.1.1 : Set X) ∩ interior p).Nonempty} =
      {K : ↥(regular X) | p ⊆ (K.1.1 : Set X)} ∧
    ∀ q ∈ P, q ≠ p → Disjoint q (interior p) := by
  refine ⟨?_, ?_, fun q hq hne => hP.disjoint_atom hp hq hne⟩
  · exact (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
      (isOpen_interior (s := p))).preimage continuous_coe_regular
  · ext K
    constructor
    · intro h
      have hK := isRegSubcontinuum_coe K
      exact hP.absorb hK hp (hK.isRegularClosed.inter_interior_nonempty isOpen_interior h)
    · intro h
      obtain ⟨z, hz⟩ := (hP.reg hp).interior_nonempty
      exact ⟨z, h (interior_subset hz), hz⟩

/-- Proposition 6.3 (b), second part. -/
theorem atomicFamily_discrete' (hP : IsAtomicFamily P) :
    DiscreteTopology ↥{K : ↥(regular X) | (K.1.1 : Set X) ∈ P} := by
  rw [discreteTopology_iff_isOpen_singleton]
  rintro ⟨K, hK⟩
  have hK' : (K.1.1 : Set X) ∈ P := hK
  have hopen := (atomicFamily_open_of_mem' hP hK').1
  have : ({⟨K, hK⟩} : Set ↥{K : ↥(regular X) | (K.1.1 : Set X) ∈ P}) =
      Subtype.val ⁻¹' {L : ↥(regular X) | ((L.1.1 : Set X) ∩ interior (K.1.1 : Set X)).Nonempty} := by
    ext ⟨L, hL⟩
    have hL' : (L.1.1 : Set X) ∈ P := hL
    simp only [mem_singleton_iff, mem_preimage, mem_ofPred_eq, Subtype.mk.injEq]
    constructor
    · intro h
      rw [h]
      obtain ⟨z, hz⟩ := (hP.reg hK').interior_nonempty
      exact ⟨z, interior_subset hz, hz⟩
    · rintro ⟨z, hzL, hzK⟩
      by_contra hne
      have hne' : (L.1.1 : Set X) ≠ (K.1.1 : Set X) := fun h => hne (coe_injective_regular h)
      exact Set.disjoint_left.1 (hP.disjoint_atom hK' hL' hne') hzL hzK
  rw [this]
  exact hopen.preimage continuous_subtype_val

end Atoms

/-! ### Theorem 1.5 -/

theorem isClosed_setOf_subset (p : Set X) :
    IsClosed {K : Subcontinua X | p ⊆ (K.1 : Set X)} := by
  have : {K : Subcontinua X | p ⊆ (K.1 : Set X)} =
      ⋂ a ∈ p, (fun K : Subcontinua X => K.1) ⁻¹'
        {K : NonemptyCompacts X | ((K : Set X) ∩ {a}).Nonempty} := by
    ext K
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, Set.inter_singleton_nonempty]
    rfl
  rw [this]
  exact isClosed_biInter fun a _ =>
    (NonemptyCompacts.isClosed_inter_nonempty_of_isClosed isClosed_singleton).preimage
      continuous_subtype_val

theorem isClosed_setOf_disjoint {U : Set X} (hU : IsOpen U) :
    IsClosed {K : Subcontinua X | Disjoint (K.1 : Set X) U} := by
  have : {K : Subcontinua X | Disjoint (K.1 : Set X) U} =
      (fun K : Subcontinua X => K.1) ⁻¹' {K : NonemptyCompacts X | (K : Set X) ⊆ Uᶜ} := by
    ext K
    simp only [mem_ofPred_eq, mem_preimage, Set.subset_compl_iff_disjoint_right]
  rw [this]
  exact (NonemptyCompacts.isClosed_subsets_of_isClosed hU.isClosed_compl).preimage
    continuous_subtype_val

/-- Theorem 1.5: for a `D`-atomic continuum, `D(X)` is a `G_δ` subset of `C(X)`. -/
theorem isGδ_regular_of_isDAtomic' (h : IsDAtomic X) : IsGδ (regular X) := by
  classical
  obtain ⟨P, hP⟩ := h
  let H : Set (Subcontinua X) :=
    ⋂ p ∈ P, ({K : Subcontinua X | p ⊆ (K.1 : Set X)} ∪
      {K : Subcontinua X | Disjoint (K.1 : Set X) (interior p)})
  let O : ℕ → Set (Subcontinua X) := fun m =>
    ⋃ S ∈ {S : Finset (Set X) | ∀ p ∈ S, p ∈ P},
      (⋂ p ∈ S, {K : Subcontinua X | ((K.1 : Set X) ∩ interior p).Nonempty}) ∩
        {K : Subcontinua X | (K.1 : Set X) ⊆ Metric.thickening (1 / ((m : ℝ) + 1)) (⋃ p ∈ S, p)}
  have hHcl : IsClosed H := isClosed_biInter fun p _ =>
    (isClosed_setOf_subset p).union (isClosed_setOf_disjoint isOpen_interior)
  have hOo : ∀ m, IsOpen (O m) := by
    intro m
    refine isOpen_biUnion fun S _ => IsOpen.inter (isOpen_biInter_finset fun p _ => ?_) ?_
    · exact (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
        (isOpen_interior (s := p))).preimage continuous_subtype_val
    · exact (NonemptyCompacts.isOpen_subsets_of_isOpen
        Metric.isOpen_thickening).preimage continuous_subtype_val
  have hmemH : ∀ K : Subcontinua X, K ∈ H ↔
      ∀ p ∈ P, p ⊆ (K.1 : Set X) ∨ Disjoint (K.1 : Set X) (interior p) := by
    intro K
    simp only [H, mem_iInter, mem_union, mem_ofPred_eq]
  have hmemO : ∀ (m : ℕ) (K : Subcontinua X), K ∈ O m ↔ ∃ S : Finset (Set X),
      (∀ p ∈ S, p ∈ P) ∧ (∀ p ∈ S, ((K.1 : Set X) ∩ interior p).Nonempty) ∧
      (K.1 : Set X) ⊆ Metric.thickening (1 / ((m : ℝ) + 1)) (⋃ p ∈ S, p) := by
    intro m K
    simp only [O, mem_iUnion, mem_inter_iff, mem_iInter, mem_ofPred_eq, exists_prop]
  have heq : regular X = H ∩ ⋂ m, O m := by
    ext K
    constructor
    · intro hK
      have hA : IsRegSubcontinuum (K.1 : Set X) := isRegSubcontinuum_coe ⟨K, hK⟩
      refine ⟨(hmemH K).2 fun p hp => ?_, mem_iInter.2 fun m => (hmemO m K).2 ?_⟩
      · by_cases hd : Disjoint (K.1 : Set X) (interior p)
        · exact Or.inr hd
        · rw [Set.not_disjoint_iff_nonempty_inter] at hd
          exact Or.inl (hP.absorb hA hp
            (hA.isRegularClosed.inter_interior_nonempty isOpen_interior hd))
      · have hδ : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        have hcover : (K.1 : Set X) ⊆
            ⋃ p ∈ {p | p ∈ P ∧ p ⊆ (K.1 : Set X)}, Metric.thickening (1 / ((m : ℝ) + 1)) p := by
          intro x hx
          have hx' : x ∈ closure (⋃₀ {p | p ∈ P ∧ p ⊆ (K.1 : Set X)}) := by
            rw [← hP.eq_closure hA]; exact hx
          have := Metric.closure_subset_thickening hδ _ hx'
          rw [sUnion_eq_biUnion, Metric.thickening_biUnion] at this
          exact this
        obtain ⟨b', hb', hfin, hsub⟩ := hA.isCompact.elim_finite_subcover_image
          (fun p _ => Metric.isOpen_thickening) hcover
        refine ⟨hfin.toFinset, fun p hp => (hb' (hfin.mem_toFinset.1 hp)).1, fun p hp => ?_, ?_⟩
        · obtain ⟨z, hz⟩ := (hP.reg (hb' (hfin.mem_toFinset.1 hp)).1).interior_nonempty
          exact ⟨z, (hb' (hfin.mem_toFinset.1 hp)).2 (interior_subset hz), hz⟩
        · intro x hx
          obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (hsub hx)
          exact Metric.thickening_subset_of_subset _
            (subset_iUnion₂ (s := fun q (_ : q ∈ hfin.toFinset) => q) p (hfin.mem_toFinset.2 hp)) hxp
    · rintro ⟨hKH, hKO⟩
      rw [hmemH] at hKH
      have hKcl : IsClosed (K.1 : Set X) := K.1.isCompact.isClosed
      have hsubT : closure (⋃₀ {p | p ∈ P ∧ p ⊆ (K.1 : Set X)}) ⊆ (K.1 : Set X) :=
        closure_minimal (sUnion_subset fun p hp => hp.2) hKcl
      have hTsub : (K.1 : Set X) ⊆ closure (⋃₀ {p | p ∈ P ∧ p ⊆ (K.1 : Set X)}) := by
        intro x hx
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
        obtain ⟨S, hSP, hSne, hSsub⟩ := (hmemO m K).1 (mem_iInter.1 hKO m)
        obtain ⟨z, hzS, hdist⟩ := Metric.mem_thickening_iff.1 (hSsub hx)
        obtain ⟨p, hpS, hzp⟩ := mem_iUnion₂.1 hzS
        have hpK : p ⊆ (K.1 : Set X) := by
          rcases hKH p (hSP p hpS) with h | h
          · exact h
          · exact absurd (hSne p hpS) (Set.not_nonempty_iff_eq_empty.2 h.inter_eq)
        exact ⟨z, ⟨p, ⟨hSP p hpS, hpK⟩, hzp⟩, hdist.trans hm⟩
      have hKeq : (K.1 : Set X) = closure (⋃₀ {p | p ∈ P ∧ p ⊆ (K.1 : Set X)}) :=
        Subset.antisymm hTsub hsubT
      show IsRegularClosed (K.1 : Set X)
      rw [hKeq]
      exact isRegularClosed_closure_sUnion fun p hp => (hP.reg hp.1).isRegularClosed
  rw [heq]
  exact hHcl.isGδ.inter (IsGδ.iInter_of_isOpen hOo)

end RegularSubcontinua
