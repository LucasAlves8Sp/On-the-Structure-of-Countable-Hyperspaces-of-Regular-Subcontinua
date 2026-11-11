module

public import RegularSubcontinua.Decreasing
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable

@[expose] public section

/-!
# Density of the minimal elements (Theorem 5.1)

A *gap* is a pair `(P, P')` of sets with `P ⊆ P'`; its region is `P' \ P` and its cell is
`regDiff P' P`. A *level* is a family of gaps whose regions partition `X` and which is linearly
ordered (`g.2 ⊆ h.1` or `h.2 ⊆ g.1`). This is the ordered cover of the paper, recorded through
its initial unions: `g.1` is the union of the cells placed before the cell of `g`, and `g.2`
is `g.1` together with that cell.
-/

open Set Function TopologicalSpace Topology
open scoped Cardinal

universe u

namespace RegularSubcontinua

section Peel

variable {X : Type*} [TopologicalSpace X]

theorem regDiff_union_self {P S : Set X} (hS : IsRegularClosed S)
    (hd : Disjoint (interior S) P) : regDiff (P ∪ S) P = S := by
  apply Subset.antisymm
  · apply closure_minimal _ hS.isClosed
    rintro z ⟨hz, hzP⟩
    exact (interior_subset hz).resolve_left hzP
  · calc S = closure (interior S) := hS.eq.symm
      _ ⊆ regDiff (P ∪ S) P := closure_mono fun z hz =>
          ⟨interior_mono subset_union_right hz, fun hzP => Set.disjoint_left.1 hd hz hzP⟩

/-- Ordering of finitely many cells with connected initial unions (Step 1 of Theorem 5.1). -/
theorem exists_peel : ∀ (k : ℕ) (P : Set X) (𝒮 : Finset (Set X)), 𝒮.card = k →
    (P = ∅ ∨ IsRegSubcontinuum P) →
    (∀ S ∈ 𝒮, IsRegSubcontinuum S) →
    (∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ≠ S' → Disjoint (interior S) S') →
    (∀ S ∈ 𝒮, Disjoint (interior S) P) → IsPreconnected (P ∪ ⋃ S ∈ 𝒮, S) →
    ∃ 𝒢 : Set (Set X × Set X),
      (∀ h ∈ 𝒢, P ⊆ h.1 ∧ h.1 ⊆ h.2 ∧ h.2 ⊆ P ∪ ⋃ S ∈ 𝒮, S ∧
        (h.1 = ∅ ∨ IsRegSubcontinuum h.1) ∧ IsRegSubcontinuum h.2 ∧ regDiff h.2 h.1 ∈ 𝒮) ∧
      (∀ g ∈ 𝒢, ∀ h ∈ 𝒢, g ≠ h → g.2 ⊆ h.1 ∨ h.2 ⊆ g.1) ∧
      (∀ x, (∃ S ∈ 𝒮, x ∈ S) → x ∉ P → ∃ h ∈ 𝒢, x ∈ h.2 ∧ x ∉ h.1) := by
  classical
  intro k
  induction k with
  | zero =>
    intro P 𝒮 hcard _ _ _ _ _
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    exact ⟨∅, by simp, by simp, by simp⟩
  | succ k ih =>
    intro P 𝒮 hcard hP hreg hpair hdP hconn
    have hPcl : IsClosed P := by
      rcases hP with h | h
      · rw [h]; exact isClosed_empty
      · exact h.isClosed
    -- choose a cell touching `P`
    have hex : ∃ S₀ ∈ 𝒮, P = ∅ ∨ (P ∩ S₀).Nonempty := by
      have hne : 𝒮.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨S₁, hS₁⟩ := hne
      rcases hP with h | h
      · exact ⟨S₁, hS₁, Or.inl h⟩
      · by_contra hcon
        push Not at hcon
        have hUcl : IsClosed (⋃ S ∈ 𝒮, S) :=
          isClosed_biUnion_finset fun S hS => (hreg S hS).isClosed
        have hd : Disjoint P (⋃ S ∈ 𝒮, S) := by
          rw [Set.disjoint_left]
          intro z hzP hzU
          obtain ⟨S, hS, hzS⟩ := mem_iUnion₂.1 hzU
          have := (hcon S hS).2
          have hz : z ∈ P ∩ S := ⟨hzP, hzS⟩
          rw [this] at hz
          exact hz
        obtain ⟨p, hp⟩ := h.nonempty
        obtain ⟨s, hs⟩ := (hreg S₁ hS₁).nonempty
        rcases hconn.subset_or_subset_of_closed hPcl hUcl Subset.rfl hd with h1 | h1
        · exact Set.disjoint_left.1 hd (h1 (Or.inr (mem_iUnion₂.2 ⟨S₁, hS₁, hs⟩)))
            (mem_iUnion₂.2 ⟨S₁, hS₁, hs⟩)
        · exact Set.disjoint_left.1 hd hp (h1 (Or.inl hp))
    obtain ⟨S₀, hS₀, hPS₀⟩ := hex
    have hS₀reg := hreg S₀ hS₀
    have hP₁ : IsRegSubcontinuum (P ∪ S₀) := by
      rcases hP with h | h
      · rw [h, empty_union]; exact hS₀reg
      · rcases hPS₀ with h' | h'
        · rw [h', empty_union]; exact hS₀reg
        · exact h.union hS₀reg h'
    have hcard' : (𝒮.erase S₀).card = k := by
      rw [Finset.card_erase_of_mem hS₀, hcard]; rfl
    have hunion : P ∪ S₀ ∪ ⋃ S ∈ 𝒮.erase S₀, S = P ∪ ⋃ S ∈ 𝒮, S := by
      ext z
      simp only [mem_union, mem_iUnion, Finset.mem_erase, exists_prop]
      constructor
      · rintro ((h | h) | ⟨S, ⟨_, hS⟩, hz⟩)
        · exact Or.inl h
        · exact Or.inr ⟨S₀, hS₀, h⟩
        · exact Or.inr ⟨S, hS, hz⟩
      · rintro (h | ⟨S, hS, hz⟩)
        · exact Or.inl (Or.inl h)
        · by_cases hSS : S = S₀
          · exact Or.inl (Or.inr (hSS ▸ hz))
          · exact Or.inr ⟨S, ⟨hSS, hS⟩, hz⟩
    obtain ⟨𝒢₁, ha, hb, hc⟩ := ih (P ∪ S₀) (𝒮.erase S₀) hcard' (Or.inr hP₁)
      (fun S hS => hreg S (Finset.mem_of_mem_erase hS))
      (fun S hS S' hS' hne => hpair S (Finset.mem_of_mem_erase hS) S'
        (Finset.mem_of_mem_erase hS') hne)
      (fun S hS => by
        rw [Set.disjoint_union_right]
        exact ⟨hdP S (Finset.mem_of_mem_erase hS),
          hpair S (Finset.mem_of_mem_erase hS) S₀ hS₀ (Finset.ne_of_mem_erase hS)⟩)
      (by rw [hunion]; exact hconn)
    refine ⟨insert (P, P ∪ S₀) 𝒢₁, ?_, ?_, ?_⟩
    · rintro h (rfl | hh)
      · refine ⟨Subset.rfl, subset_union_left, ?_, hP, hP₁, ?_⟩
        · exact union_subset_union_right P fun z hz => mem_iUnion₂.2 ⟨S₀, hS₀, hz⟩
        · show regDiff (P ∪ S₀) P ∈ 𝒮
          rw [regDiff_union_self hS₀reg.isRegularClosed (hdP S₀ hS₀)]
          exact hS₀
      · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ha h hh
        refine ⟨subset_union_left.trans h1, h2, ?_, h4, h5, Finset.mem_of_mem_erase h6⟩
        rw [← hunion]; exact h3
    · rintro g (rfl | hg) h (rfl | hh) hne
      · exact absurd rfl hne
      · exact Or.inl (ha h hh).1
      · exact Or.inr (ha g hg).1
      · exact hb g hg h hh hne
    · rintro x ⟨S, hS, hxS⟩ hxP
      by_cases hxS₀ : x ∈ S₀
      · exact ⟨(P, P ∪ S₀), mem_insert _ _, Or.inr hxS₀, hxP⟩
      · have hSne : S ≠ S₀ := fun h => hxS₀ (h ▸ hxS)
        obtain ⟨h, hh, hx1, hx2⟩ := hc x ⟨S, Finset.mem_erase.2 ⟨hSne, hS⟩, hxS⟩
          (fun hx => hx.elim hxP hxS₀)
        exact ⟨h, mem_insert_of_mem _ hh, hx1, hx2⟩

theorem disjoint_of_mem_components {R C C' : Set X} (hC : C ∈ components R)
    (hC' : C' ∈ components R) (hne : C ≠ C') : Disjoint C C' := by
  obtain ⟨x, _, rfl⟩ := hC
  obtain ⟨y, _, rfl⟩ := hC'
  rw [Set.disjoint_left]
  intro z hzx hzy
  exact hne ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

end Peel

section Levels

variable {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- A level: an ordered family of gaps whose regions cover `X` and whose cells are regular
subcontinua. -/
structure IsLevel (𝒢 : Set (Set X × Set X)) : Prop where
  cover : ∀ x : X, ∃ g ∈ 𝒢, x ∈ g.2 ∧ x ∉ g.1
  ordered : ∀ g ∈ 𝒢, ∀ h ∈ 𝒢, g ≠ h → g.2 ⊆ h.1 ∨ h.2 ⊆ g.1
  subset : ∀ g ∈ 𝒢, g.1 ⊆ g.2
  lower : ∀ g ∈ 𝒢, g.1 = ∅ ∨ IsRegSubcontinuum g.1
  upper : ∀ g ∈ 𝒢, IsRegSubcontinuum g.2
  cell : ∀ g ∈ 𝒢, IsRegSubcontinuum (regDiff g.2 g.1)

theorem IsLevel.unique {𝒢 : Set (Set X × Set X)} (h𝒢 : IsLevel 𝒢) {g h : Set X × Set X}
    (hg : g ∈ 𝒢) (hh : h ∈ 𝒢) {x : X} (hx1 : x ∈ g.2) (hx2 : x ∉ g.1) (hx3 : x ∈ h.2)
    (hx4 : x ∉ h.1) : g = h := by
  by_contra hne
  rcases h𝒢.ordered g hg h hh hne with h1 | h1
  · exact hx4 (h1 hx1)
  · exact hx2 (h1 hx3)

theorem IsLevel.isClosed_lower {𝒢 : Set (Set X × Set X)} (h𝒢 : IsLevel 𝒢)
    {g : Set X × Set X} (hg : g ∈ 𝒢) : IsClosed g.1 := by
  rcases h𝒢.lower g hg with h | h
  · rw [h]; exact isClosed_empty
  · exact h.isClosed

theorem IsLevel.isRegularClosed_lower {𝒢 : Set (Set X × Set X)} (h𝒢 : IsLevel 𝒢)
    {g : Set X × Set X} (hg : g ∈ 𝒢) : IsRegularClosed g.1 := by
  rcases h𝒢.lower g hg with h | h
  · rw [h]; exact isRegularClosed_empty
  · exact h.isRegularClosed

theorem isLevel_init : IsLevel ({((∅ : Set X), (univ : Set X))} : Set (Set X × Set X)) := by
  refine ⟨fun x => ⟨(∅, univ), rfl, mem_univ x, notMem_empty x⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro g rfl h rfl hne
    exact absurd rfl hne
  · rintro g rfl; exact empty_subset _
  · rintro g rfl; exact Or.inl rfl
  · rintro g rfl; exact isRegSubcontinuum_univ
  · rintro g rfl
    have : regDiff (univ : Set X) ∅ = univ := by simp [regDiff]
    show IsRegSubcontinuum (regDiff (univ : Set X) ∅)
    rw [this]; exact isRegSubcontinuum_univ

/-- Refinement of a level along a regular subcontinuum `D`. -/
theorem exists_refinement (hcount : (regular X).Countable) {𝒢 : Set (Set X × Set X)}
    (h𝒢 : IsLevel 𝒢) {D : Set X} (hD : IsRegSubcontinuum D) :
    ∃ 𝒢' : Set (Set X × Set X), IsLevel 𝒢' ∧
      (∀ h ∈ 𝒢', ∃ g ∈ 𝒢, g.1 ⊆ h.1 ∧ h.2 ⊆ g.2) ∧
      (∀ h ∈ 𝒢', regDiff h.2 h.1 ⊆ D ∨ regDiff h.2 h.1 ⊆ closure Dᶜ) := by
  classical
  have hloc : ∀ g ∈ 𝒢, ∃ 𝒢g : Set (Set X × Set X),
      (∀ h ∈ 𝒢g, g.1 ⊆ h.1 ∧ h.1 ⊆ h.2 ∧ h.2 ⊆ g.2 ∧ (h.1 = ∅ ∨ IsRegSubcontinuum h.1) ∧
        IsRegSubcontinuum h.2 ∧ IsRegSubcontinuum (regDiff h.2 h.1) ∧
        (regDiff h.2 h.1 ⊆ D ∨ regDiff h.2 h.1 ⊆ closure Dᶜ)) ∧
      (∀ h ∈ 𝒢g, ∀ h' ∈ 𝒢g, h ≠ h' → h.2 ⊆ h'.1 ∨ h'.2 ⊆ h.1) ∧
      (∀ x, x ∈ g.2 → x ∉ g.1 → ∃ h ∈ 𝒢g, x ∈ h.2 ∧ x ∉ h.1) := by
    intro g hg
    have hC := h𝒢.cell g hg
    set C : Set X := regDiff g.2 g.1 with hCdef
    have hM := isFiniteUnion_regMeet hcount hC.isFiniteUnion hD.isFiniteUnion
    have hN := isFiniteUnion_regDiff hcount hC.isFiniteUnion hD.isFiniteUnion
    obtain ⟨hMfin, hMreg⟩ := components_of_isFiniteUnion' hM
    obtain ⟨hNfin, hNreg⟩ := components_of_isFiniteUnion' hN
    let 𝒮 : Finset (Set X) := hMfin.toFinset ∪ hNfin.toFinset
    have hmem : ∀ S, S ∈ 𝒮 ↔ S ∈ components (regMeet C D) ∨ S ∈ components (regDiff C D) := by
      intro S
      simp only [𝒮, Finset.mem_union, Set.Finite.mem_toFinset]
    have hsubM : ∀ S ∈ components (regMeet C D), S ⊆ regMeet C D := by
      rintro S ⟨y, _, rfl⟩; exact connectedComponentIn_subset _ y
    have hsubN : ∀ S ∈ components (regDiff C D), S ⊆ regDiff C D := by
      rintro S ⟨y, _, rfl⟩; exact connectedComponentIn_subset _ y
    have hSreg : ∀ S ∈ 𝒮, IsRegSubcontinuum S := by
      intro S hS
      rcases (hmem S).1 hS with h | h
      · exact hMreg S h
      · exact hNreg S h
    have hSC : ∀ S ∈ 𝒮, S ⊆ C := by
      intro S hS
      rcases (hmem S).1 hS with h | h
      · exact (hsubM S h).trans (regMeet_subset_left hC.isClosed)
      · exact (hsubN S h).trans (regDiff_subset_left hC.isClosed)
    have hside : ∀ S ∈ 𝒮, S ⊆ D ∨ S ⊆ closure Dᶜ := by
      intro S hS
      rcases (hmem S).1 hS with h | h
      · exact Or.inl ((hsubM S h).trans (regMeet_subset_right hD.isClosed))
      · exact Or.inr ((hsubN S h).trans regDiff_subset_closure_compl)
    have hpair : ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ≠ S' → Disjoint (interior S) S' := by
      intro S hS S' hS' hne
      rcases (hmem S).1 hS with h | h <;> rcases (hmem S').1 hS' with h' | h'
      · exact (disjoint_of_mem_components h h' hne).mono_left interior_subset
      · exact (disjoint_interior_regMeet_regDiff hD.isClosed).mono
          (interior_mono (hsubM S h)) (hsubN S' h')
      · exact disjoint_interior_regDiff_regMeet.mono (interior_mono (hsubN S h)) (hsubM S' h')
      · exact (disjoint_of_mem_components h h' hne).mono_left interior_subset
    have hdP : ∀ S ∈ 𝒮, Disjoint (interior S) g.1 := by
      intro S hS
      apply (h𝒢.isRegularClosed_lower hg).disjoint_of_disjoint_interior isOpen_interior
      exact (disjoint_regDiff_interior.mono_left (interior_subset.trans (hSC S hS)))
    have hunionS : ⋃ S ∈ 𝒮, S = C := by
      apply Subset.antisymm
      · exact iUnion₂_subset fun S hS => hSC S hS
      · intro z hz
        rw [← regMeet_union_regDiff hC.isRegularClosed hD.isClosed] at hz
        rcases hz with h | h
        · rw [← sUnion_components (regMeet C D)] at h
          obtain ⟨S, hS, hzS⟩ := h
          exact mem_iUnion₂.2 ⟨S, (hmem S).2 (Or.inl hS), hzS⟩
        · rw [← sUnion_components (regDiff C D)] at h
          obtain ⟨S, hS, hzS⟩ := h
          exact mem_iUnion₂.2 ⟨S, (hmem S).2 (Or.inr hS), hzS⟩
    have hPC : g.1 ∪ C = g.2 := by
      apply Subset.antisymm
      · exact union_subset (h𝒢.subset g hg) (regDiff_subset_left (h𝒢.upper g hg).isClosed)
      · intro z hz
        by_cases hz1 : z ∈ g.1
        · exact Or.inl hz1
        · exact Or.inr (diff_subset_regDiff (h𝒢.upper g hg).isRegularClosed
            (h𝒢.isClosed_lower hg) ⟨hz, hz1⟩)
    have hconn : IsPreconnected (g.1 ∪ ⋃ S ∈ 𝒮, S) := by
      rw [hunionS, hPC]; exact (h𝒢.upper g hg).isPreconnected
    obtain ⟨𝒢g, ha, hb, hc⟩ := exists_peel 𝒮.card g.1 𝒮 rfl (h𝒢.lower g hg) hSreg hpair hdP hconn
    refine ⟨𝒢g, ?_, hb, ?_⟩
    · intro h hh
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ha h hh
      refine ⟨h1, h2, ?_, h4, h5, hSreg _ h6, hside _ h6⟩
      rw [hunionS, hPC] at h3; exact h3
    · intro x hx2 hx1
      have hxC : x ∈ C := diff_subset_regDiff (h𝒢.upper g hg).isRegularClosed
        (h𝒢.isClosed_lower hg) ⟨hx2, hx1⟩
      rw [← hunionS] at hxC
      obtain ⟨S, hS, hxS⟩ := mem_iUnion₂.1 hxC
      exact hc x ⟨S, hS, hxS⟩ hx1
  choose! Φ hΦa hΦb hΦc using hloc
  refine ⟨⋃ g ∈ 𝒢, Φ g, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x
    obtain ⟨g, hg, hx2, hx1⟩ := h𝒢.cover x
    obtain ⟨h, hh, hx3, hx4⟩ := hΦc g hg x hx2 hx1
    exact ⟨h, mem_iUnion₂.2 ⟨g, hg, hh⟩, hx3, hx4⟩
  · intro h hh h' hh' hne
    obtain ⟨g, hg, hhg⟩ := mem_iUnion₂.1 hh
    obtain ⟨g', hg', hhg'⟩ := mem_iUnion₂.1 hh'
    by_cases hgg : g = g'
    · subst hgg
      exact hΦb g hg h hhg h' hhg' hne
    · rcases h𝒢.ordered g hg g' hg' hgg with h1 | h1
      · exact Or.inl (((hΦa g hg h hhg).2.2.1.trans h1).trans (hΦa g' hg' h' hhg').1)
      · exact Or.inr (((hΦa g' hg' h' hhg').2.2.1.trans h1).trans (hΦa g hg h hhg).1)
  · intro h hh
    obtain ⟨g, hg, hhg⟩ := mem_iUnion₂.1 hh
    exact (hΦa g hg h hhg).2.1
  · intro h hh
    obtain ⟨g, hg, hhg⟩ := mem_iUnion₂.1 hh
    exact (hΦa g hg h hhg).2.2.2.1
  · intro h hh
    obtain ⟨g, hg, hhg⟩ := mem_iUnion₂.1 hh
    exact (hΦa g hg h hhg).2.2.2.2.1
  · intro h hh
    obtain ⟨g, hg, hhg⟩ := mem_iUnion₂.1 hh
    exact (hΦa g hg h hhg).2.2.2.2.2.1
  · intro h hh
    obtain ⟨g, hg, hhg⟩ := mem_iUnion₂.1 hh
    exact ⟨g, hg, (hΦa g hg h hhg).1, (hΦa g hg h hhg).2.2.1⟩
  · intro h hh
    obtain ⟨g, hg, hhg⟩ := mem_iUnion₂.1 hh
    exact (hΦa g hg h hhg).2.2.2.2.2.2

/-- Theorem 5.1 (density of the minimal elements). -/
theorem dense_interior_minimal' (hcount : (regular X).Countable) :
    Dense (⋃ (N : Set X) (_ : IsMinimalReg N), interior N) := by
  classical
  -- enumeration of the regular subcontinua
  have hcS := countable_setOf_isRegSubcontinuum hcount
  obtain ⟨D, hD⟩ := hcS.exists_eq_range ⟨univ, (isRegSubcontinuum_univ : IsRegSubcontinuum (univ : Set X))⟩
  have hDreg : ∀ m, IsRegSubcontinuum (D m) := fun m => by
    have : D m ∈ {A : Set X | IsRegSubcontinuum A} := hD ▸ mem_range_self m
    exact this
  have hDsurj : ∀ B : Set X, IsRegSubcontinuum B → ∃ m, D m = B := fun B hB => by
    have : B ∈ range D := hD ▸ hB
    exact this
  -- the sequence of levels
  let T := {𝒢 : Set (Set X × Set X) // IsLevel 𝒢}
  have step : ∀ (m : ℕ) (t : T), ∃ t' : T,
      (∀ h ∈ t'.1, ∃ g ∈ t.1, g.1 ⊆ h.1 ∧ h.2 ⊆ g.2) ∧
      (∀ h ∈ t'.1, regDiff h.2 h.1 ⊆ D m ∨ regDiff h.2 h.1 ⊆ closure (D m)ᶜ) := by
    rintro m ⟨𝒢, h𝒢⟩
    obtain ⟨𝒢', h1, h2, h3⟩ := exists_refinement hcount h𝒢 (hDreg m)
    exact ⟨⟨𝒢', h1⟩, h2, h3⟩
  choose next hnext1 hnext2 using step
  let L : ℕ → T := fun n => Nat.rec (⟨_, isLevel_init⟩ : T) (fun m t => next m t) n
  have hL_succ : ∀ m, L (m + 1) = next m (L m) := fun m => rfl
  have hcov : ∀ (n : ℕ) (x : X), ∃ g ∈ (L n).1, x ∈ g.2 ∧ x ∉ g.1 := fun n x => (L n).2.cover x
  choose g hg1 hg2 hg3 using hcov
  -- nesting
  have hnest : ∀ n x, (g n x).1 ⊆ (g (n + 1) x).1 ∧ (g (n + 1) x).2 ⊆ (g n x).2 := by
    intro n x
    have hmem : g (n + 1) x ∈ (next n (L n)).1 := hL_succ n ▸ hg1 (n + 1) x
    obtain ⟨g', hg', h1, h2⟩ := hnext1 n (L n) _ hmem
    have : g' = g n x := (L n).2.unique hg' (hg1 n x) (h2 (hg2 (n + 1) x))
      (fun hx => hg3 (n + 1) x (h1 hx)) (hg2 n x) (hg3 n x)
    rw [← this]; exact ⟨h1, h2⟩
  have hlow_mono : ∀ x, Monotone fun n => (g n x).1 := fun x =>
    monotone_nat_of_le_succ fun n => (hnest n x).1
  have hup_anti : ∀ x, Antitone fun n => (g n x).2 := fun x =>
    antitone_nat_of_succ_le fun n => (hnest n x).2
  have hlow_up : ∀ x m n, (g m x).1 ⊆ (g n x).2 := by
    intro x m n
    rcases le_total m n with h | h
    · exact (hlow_mono x h).trans ((L n).2.subset _ (hg1 n x))
    · exact ((L m).2.subset _ (hg1 m x)).trans (hup_anti x h)
  -- cells
  let cell : ℕ → X → Set X := fun n x => regDiff (g n x).2 (g n x).1
  have hcell_reg : ∀ n x, IsRegSubcontinuum (cell n x) := fun n x => (L n).2.cell _ (hg1 n x)
  have hcell_anti : ∀ x, Antitone fun n => cell n x := fun x =>
    antitone_nat_of_succ_le fun n => regDiff_mono (hnest n x).2 (hnest n x).1
  have hcell_mem : ∀ n x, x ∈ cell n x := fun n x =>
    diff_subset_regDiff ((L n).2.upper _ (hg1 n x)).isRegularClosed
      ((L n).2.isClosed_lower (hg1 n x)) ⟨hg2 n x, hg3 n x⟩
  have hside : ∀ m x, cell (m + 1) x ⊆ D m ∨ cell (m + 1) x ⊆ closure (D m)ᶜ := by
    intro m x
    have hmem : g (m + 1) x ∈ (next m (L m)).1 := hL_succ m ▸ hg1 (m + 1) x
    exact hnext2 m (L m) _ hmem
  -- branch intersections
  let Kf : X → Set X := fun x => ⋂ n, cell n x
  have hKcl : ∀ x, IsClosed (Kf x) := fun x => isClosed_iInter fun n => (hcell_reg n x).isClosed
  have hxK : ∀ x, x ∈ Kf x := fun x => mem_iInter.2 fun n => hcell_mem n x
  -- Step 4: a branch intersection with nonempty interior is minimal
  have hmin : ∀ x, (interior (Kf x)).Nonempty → IsMinimalReg (Kf x) := by
    intro x hne
    obtain ⟨-, -, hB⟩ := decreasing_intersection' hcount (fun n => hcell_reg n x) (hcell_anti x)
    obtain ⟨B, hBreg, hBsub⟩ := hB hne
    have key : ∀ B' : Set X, IsRegSubcontinuum B' → B' ⊆ Kf x → B' = Kf x := by
      intro B' hB' hsub
      obtain ⟨m, rfl⟩ := hDsurj B' hB'
      have hKc : Kf x ⊆ cell (m + 1) x := iInter_subset _ (m + 1)
      rcases hside m x with h | h
      · exact Subset.antisymm hsub (hKc.trans h)
      · exfalso
        obtain ⟨z, hz⟩ := hB'.interior_nonempty
        have hzcl : z ∈ closure (D m)ᶜ := h (hKc (hsub (interior_subset hz)))
        obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hzcl _ isOpen_interior hz
        exact hw2 (interior_subset hw1)
    have hKB : B = Kf x := key B hBreg hBsub
    exact ⟨hKB ▸ hBreg, fun B' hB' hsub => key B' hB' hsub⟩
  -- Step 3: countably many branches
  let β : X → ℕ → Set X × Set X := fun x n => g n x
  let Lf : (ℕ → Set X × Set X) → Set X := fun b => closure (⋃ n, (b n).1)
  have hLf_mem : ∀ x, Lf (β x) ∈ insert (∅ : Set X) {A : Set X | IsRegSubcontinuum A} := by
    intro x
    by_cases hall : ∀ n, (g n x).1 = ∅
    · left
      show closure (⋃ n, (g n x).1) = ∅
      simp [hall]
    · right
      rw [not_forall] at hall
      obtain ⟨n₀, hn₀⟩ := hall
      obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.2 hn₀
      have hregn : ∀ k, IsRegSubcontinuum (g (n₀ + k) x).1 := by
        intro k
        rcases (L (n₀ + k)).2.lower _ (hg1 (n₀ + k) x) with h | h
        · have : p ∈ (g (n₀ + k) x).1 := hlow_mono x (Nat.le_add_right n₀ k) hp
          rw [h] at this
          exact absurd this (notMem_empty p)
        · exact h
      have hUeq : ⋃ n, (g n x).1 = ⋃ k, (g (n₀ + k) x).1 := by
        apply Subset.antisymm
        · exact iUnion_subset fun n => (hlow_mono x (Nat.le_add_left n n₀)).trans
            (subset_iUnion (fun k => (g (n₀ + k) x).1) n)
        · exact iUnion_subset fun k => subset_iUnion (fun n => (g n x).1) (n₀ + k)
      have hpre : IsPreconnected (⋃ k, (g (n₀ + k) x).1) :=
        isPreconnected_iUnion
          ⟨p, mem_iInter.2 fun k => hlow_mono x (Nat.le_add_right n₀ k) hp⟩
          fun k => (hregn k).isPreconnected
      show IsRegSubcontinuum (closure (⋃ n, (g n x).1))
      refine isRegSubcontinuum_of_isClosed isClosed_closure ⟨?_, ?_⟩
        (isRegularClosed_closure_iUnion fun n => (L n).2.isRegularClosed_lower (hg1 n x))
      · exact ⟨p, subset_closure (mem_iUnion.2 ⟨n₀, hp⟩)⟩
      · rw [hUeq]; exact hpre.closure
  have hLf_sub : ∀ x n, Lf (β x) ⊆ (g n x).2 := fun x n =>
    closure_minimal (iUnion_subset fun m => hlow_up x m n) ((L n).2.upper _ (hg1 n x)).isClosed
  have hLf_sup : ∀ x n, (g n x).1 ⊆ Lf (β x) := fun x n =>
    (subset_iUnion (fun m => (g m x).1) n).trans subset_closure
  have hpersist : ∀ x y n, g n x ≠ g n y → ∀ m, n ≤ m → g m x ≠ g m y := by
    intro x y n hne m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact hne
    | succ m _ ih =>
      intro heq
      apply ih
      have hy2 : y ∈ (g m x).2 := (hnest m x).2 (heq ▸ hg2 (m + 1) y)
      have hy1 : y ∉ (g m x).1 := fun hy => hg3 (m + 1) y (heq ▸ (hnest m x).1 hy)
      exact (L m).2.unique (hg1 m x) (hg1 m y) hy2 hy1 (hg2 m y) (hg3 m y)
  have hcore : ∀ (n : ℕ) (p q r : X), (g n p).2 ⊆ (g n q).1 → (g n q).2 ⊆ (g n r).1 →
      Lf (β p) = Lf (β r) → False := by
    intro n p q r h1 h2 hL
    have : q ∈ (g n q).1 :=
      h1 (hLf_sub p n (hL ▸ hLf_sup r n (h2 (hg2 n q))))
    exact hg3 n q this
  have hthree : ∀ x y z : X, β x ≠ β y → β y ≠ β z → β x ≠ β z →
      Lf (β x) = Lf (β y) → Lf (β y) = Lf (β z) → False := by
    intro x y z hxy hyz hxz hL1 hL2
    have hdiff : ∀ a c : X, β a ≠ β c → ∃ n, g n a ≠ g n c := by
      intro a c hac
      by_contra hcon
      push Not at hcon
      exact hac (funext hcon)
    obtain ⟨n1, hn1⟩ := hdiff x y hxy
    obtain ⟨n2, hn2⟩ := hdiff y z hyz
    obtain ⟨n3, hn3⟩ := hdiff x z hxz
    let n := max n1 (max n2 n3)
    have h1 : g n x ≠ g n y := hpersist x y n1 hn1 n (le_max_left _ _)
    have h2 : g n y ≠ g n z :=
      hpersist y z n2 hn2 n ((le_max_left _ _).trans (le_max_right _ _))
    have h3 : g n x ≠ g n z :=
      hpersist x z n3 hn3 n ((le_max_right _ _).trans (le_max_right _ _))
    have hL3 : Lf (β x) = Lf (β z) := hL1.trans hL2
    rcases (L n).2.ordered _ (hg1 n x) _ (hg1 n y) h1 with hxy' | hyx' <;>
    rcases (L n).2.ordered _ (hg1 n y) _ (hg1 n z) h2 with hyz' | hzy' <;>
    rcases (L n).2.ordered _ (hg1 n x) _ (hg1 n z) h3 with hxz' | hzx'
    · exact hcore n x y z hxy' hyz' hL3
    · exact hcore n x y z hxy' hyz' hL3
    · exact hcore n x z y hxz' hzy' hL1
    · exact hcore n z x y hzx' hxy' hL2.symm
    · exact hcore n y x z hyx' hxz' hL2
    · exact hcore n y z x hyz' hzx' hL1.symm
    · exact hcore n z y x hzy' hyx' hL3.symm
    · exact hcore n z y x hzy' hyx' hL3.symm
  have hT : (insert (∅ : Set X) {A : Set X | IsRegSubcontinuum A}).Countable := hcS.insert ∅
  have hβ : (range β).Countable := by
    have hsub : range β ⊆ ⋃ A ∈ insert (∅ : Set X) {A : Set X | IsRegSubcontinuum A},
        {b | b ∈ range β ∧ Lf b = A} := by
      rintro b ⟨x, rfl⟩
      exact mem_iUnion₂.2 ⟨Lf (β x), hLf_mem x, ⟨x, rfl⟩, rfl⟩
    refine (hT.biUnion fun A _ => ?_).mono hsub
    apply Set.Finite.countable
    by_contra hinf
    have hinf' : {b | b ∈ range β ∧ Lf b = A}.Infinite := hinf
    obtain ⟨b1, ⟨x, rfl⟩, hb1⟩ := hinf'.nonempty
    obtain ⟨b2, ⟨⟨y, rfl⟩, hb2⟩, hne2⟩ := (hinf'.sdiff (finite_singleton (β x))).nonempty
    obtain ⟨b3, ⟨⟨z, rfl⟩, hb3⟩, hne3⟩ :=
      (hinf'.sdiff ((finite_singleton (β x)).insert (β y))).nonempty
    have hxy : β x ≠ β y := fun h => hne2 h.symm
    have hyz : β y ≠ β z := fun h => hne3 (Or.inl h.symm)
    have hxz : β x ≠ β z := fun h => hne3 (Or.inr h.symm)
    exact hthree x y z hxy hyz hxz (hb1.trans hb2.symm) (hb2.trans hb3.symm)
  have hKβ : ∀ x y, β x = β y → Kf x = Kf y := by
    intro x y h
    have : ∀ n, g n x = g n y := fun n => congrFun h n
    show (⋂ n, regDiff (g n x).2 (g n x).1) = ⋂ n, regDiff (g n y).2 (g n y).1
    simp only [this]
  have hKcount : (range Kf).Countable := by
    have : range Kf ⊆ (fun b : ℕ → Set X × Set X => ⋂ n, regDiff (b n).2 (b n).1) '' range β := by
      rintro K ⟨x, rfl⟩
      exact ⟨β x, ⟨x, rfl⟩, rfl⟩
    exact (hβ.image _).mono this
  -- Step 5: Baire category
  have : Countable ↥(range Kf) := hKcount.to_subtype
  have hdense : Dense (⋃ i : ↥(range Kf), interior (i : Set X)) := by
    apply dense_iUnion_interior_of_closed
    · rintro ⟨K, x, rfl⟩; exact hKcl x
    · apply eq_univ_of_forall
      intro x
      exact mem_iUnion.2 ⟨⟨Kf x, x, rfl⟩, hxK x⟩
  apply hdense.mono
  intro z hz
  obtain ⟨⟨K, x, rfl⟩, hzK⟩ := mem_iUnion.1 hz
  exact mem_iUnion₂.2 ⟨Kf x, hmin x ⟨z, hzK⟩, hzK⟩

end Levels

end RegularSubcontinua
