module

public import RegularSubcontinua.Counting

@[expose] public section

/-!
# Regularised operations (Lemma 2.2), the complement lemma (Lemma 4.1), the algebra of finite
unions (Proposition 4.3), absorption (Theorem 4.4, Corollary 4.5)
-/

open Set Function TopologicalSpace Topology
open scoped Cardinal

universe u

namespace RegularSubcontinua

section Ops

variable {X : Type*} [TopologicalSpace X] {F G F₁ F₂ G₁ G₂ : Set X}

theorem regDiff_subset_left (hF : IsClosed F) : regDiff F G ⊆ F :=
  closure_minimal (sdiff_subset.trans interior_subset) hF

theorem isRegularClosed_regDiff (hG : IsClosed G) : IsRegularClosed (regDiff F G) :=
  isRegularClosed_closure_of_isOpen (isOpen_interior.sdiff hG)

theorem isClosed_regDiff : IsClosed (regDiff F G) := isClosed_closure

theorem disjoint_regDiff_interior : Disjoint (regDiff F G) (interior G) := by
  apply Disjoint.closure_left _ isOpen_interior
  rw [Set.disjoint_left]
  rintro z ⟨_, hzG⟩ hz
  exact hzG (interior_subset hz)

theorem diff_subset_regDiff (hF : IsRegularClosed F) (hG : IsClosed G) : F \ G ⊆ regDiff F G := by
  rintro x ⟨hxF, hxG⟩
  rw [← hF.eq] at hxF
  rw [regDiff, mem_closure_iff]
  intro o ho hxo
  obtain ⟨z, ⟨hzo, hzG⟩, hzF⟩ :=
    mem_closure_iff.1 hxF (o ∩ Gᶜ) (ho.inter hG.isOpen_compl) ⟨hxo, hxG⟩
  exact ⟨z, hzo, hzF, hzG⟩

theorem regDiff_subset_closure_compl : regDiff F G ⊆ closure Gᶜ :=
  closure_mono fun _ hz => hz.2

theorem regDiff_mono (h : F₁ ⊆ F₂) (h' : G₂ ⊆ G₁) : regDiff F₁ G₁ ⊆ regDiff F₂ G₂ :=
  closure_mono fun _ hz => ⟨interior_mono h hz.1, fun hz' => hz.2 (h' hz')⟩

theorem regMeet_subset_left (hF : IsClosed F) : regMeet F G ⊆ F :=
  closure_minimal (inter_subset_left.trans interior_subset) hF

theorem regMeet_subset_right (hG : IsClosed G) : regMeet F G ⊆ G :=
  closure_minimal (inter_subset_right.trans interior_subset) hG

theorem isRegularClosed_regMeet : IsRegularClosed (regMeet F G) :=
  isRegularClosed_closure_of_isOpen (isOpen_interior.inter isOpen_interior)

/-- Lemma 2.2 (e), first part. -/
theorem regMeet_union_regDiff (hF : IsRegularClosed F) (hG : IsClosed G) :
    regMeet F G ∪ regDiff F G = F := by
  apply Subset.antisymm
  · exact union_subset (regMeet_subset_left hF.isClosed) (regDiff_subset_left hF.isClosed)
  · intro x hx
    rw [← hF.eq] at hx
    rw [regMeet, regDiff, ← closure_union, mem_closure_iff]
    intro o ho hxo
    obtain ⟨w, hwo, hwF⟩ := mem_closure_iff.1 hx o ho hxo
    by_cases hsub : o ∩ interior F ⊆ G
    · have : o ∩ interior F ⊆ interior G := interior_maximal hsub (ho.inter isOpen_interior)
      exact ⟨w, hwo, Or.inl ⟨hwF, this ⟨hwo, hwF⟩⟩⟩
    · rw [not_subset] at hsub
      obtain ⟨z, ⟨hzo, hzF⟩, hzG⟩ := hsub
      exact ⟨z, hzo, Or.inr ⟨hzF, hzG⟩⟩

/-- Lemma 2.2 (e), second part, in the two forms used. -/
theorem disjoint_interior_regMeet_regDiff (hG : IsClosed G) :
    Disjoint (interior (regMeet F G)) (regDiff F G) :=
  (disjoint_regDiff_interior.mono_right (interior_mono (regMeet_subset_right hG))).symm

theorem disjoint_interior_regDiff_regMeet :
    Disjoint (interior (regDiff F G)) (regMeet F G) := by
  apply Disjoint.closure_right _ isOpen_interior
  rw [Set.disjoint_left]
  rintro z hz ⟨_, hzG⟩
  exact Set.disjoint_left.1 disjoint_regDiff_interior (interior_subset hz) hzG

/-- Lemma 2.2 (f), first identity. -/
theorem regDiff_union_left (hF₁ : IsRegularClosed F₁) (hF₂ : IsRegularClosed F₂)
    (hG : IsClosed G) : regDiff (F₁ ∪ F₂) G = regDiff F₁ G ∪ regDiff F₂ G := by
  apply Subset.antisymm
  · apply closure_minimal _ (isClosed_closure.union isClosed_closure)
    rintro x ⟨hxint, hxG⟩
    have key : ∀ F' : Set X, IsRegularClosed F' → x ∈ F' → x ∈ regDiff F' G := by
      intro F' hF' hxF'
      rw [← hF'.eq] at hxF'
      rw [regDiff, mem_closure_iff]
      intro o ho hxo
      obtain ⟨z, ⟨hzo, hzG⟩, hzF⟩ :=
        mem_closure_iff.1 hxF' (o ∩ Gᶜ) (ho.inter hG.isOpen_compl) ⟨hxo, hxG⟩
      exact ⟨z, hzo, hzF, hzG⟩
    rcases interior_subset hxint with h | h
    · exact Or.inl (key F₁ hF₁ h)
    · exact Or.inr (key F₂ hF₂ h)
  · exact union_subset (regDiff_mono subset_union_left Subset.rfl)
      (regDiff_mono subset_union_right Subset.rfl)

/-- Lemma 2.2 (f), second identity. -/
theorem regDiff_regDiff (hG₁ : IsClosed G₁) (hG₂ : IsClosed G₂) :
    regDiff (regDiff F G₁) G₂ = regDiff F (G₁ ∪ G₂) := by
  apply Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    rintro x ⟨hxint, hxG₂⟩
    show x ∈ closure (interior F \ (G₁ ∪ G₂))
    rw [mem_closure_iff]
    intro o ho hxo
    have hx : x ∈ closure (interior F \ G₁) := interior_subset hxint
    obtain ⟨z, ⟨hzo, hzG₂⟩, hzF, hzG₁⟩ :=
      mem_closure_iff.1 hx (o ∩ G₂ᶜ) (ho.inter hG₂.isOpen_compl) ⟨hxo, hxG₂⟩
    exact ⟨z, hzo, hzF, fun h => h.elim hzG₁ hzG₂⟩
  · apply closure_mono
    rintro z ⟨hzF, hzG⟩
    refine ⟨?_, fun h => hzG (Or.inr h)⟩
    have hop : IsOpen (interior F \ G₁) := isOpen_interior.sdiff hG₁
    exact interior_maximal subset_closure hop ⟨hzF, fun h => hzG (Or.inl h)⟩

/-- Lemma 2.2 (f), third identity. -/
theorem regMeet_eq_regDiff_regDiff : regMeet F G = regDiff F (regDiff F G) := by
  have : interior F ∩ interior G = interior F \ regDiff F G := by
    ext z
    constructor
    · rintro ⟨hzF, hzG⟩
      exact ⟨hzF, fun h => Set.disjoint_left.1 disjoint_regDiff_interior h hzG⟩
    · rintro ⟨hzF, hz⟩
      refine ⟨hzF, ?_⟩
      by_contra hzG
      apply hz
      rw [regDiff, mem_closure_iff]
      intro o ho hzo
      by_contra hne
      apply hzG
      apply interior_maximal _ (ho.inter isOpen_interior) ⟨hzo, hzF⟩
      rintro w ⟨hwo, hwF⟩
      by_contra hwG
      exact hne ⟨w, hwo, hwF, hwG⟩
  rw [regMeet, this]
  rfl

/-! ### Finite unions -/

theorem isFiniteUnion_empty : IsFiniteUnion (∅ : Set X) :=
  ⟨∅, finite_empty, by simp, by simp⟩

theorem IsRegSubcontinuum.isFiniteUnion {A : Set X} (hA : IsRegSubcontinuum A) :
    IsFiniteUnion A :=
  ⟨{A}, finite_singleton A, by
    intro B hB
    rw [mem_singleton_iff] at hB
    rw [hB]; exact hA, by simp⟩

theorem IsFiniteUnion.union (hF : IsFiniteUnion F) (hG : IsFiniteUnion G) :
    IsFiniteUnion (F ∪ G) := by
  obtain ⟨S, hS, hS', rfl⟩ := hF
  obtain ⟨T, hT, hT', rfl⟩ := hG
  refine ⟨S ∪ T, hS.union hT, ?_, (sUnion_union S T).symm⟩
  rintro A (hA | hA)
  · exact hS' A hA
  · exact hT' A hA

theorem IsFiniteUnion.isRegularClosed (hF : IsFiniteUnion F) : IsRegularClosed F := by
  obtain ⟨S, hS, hS', rfl⟩ := hF
  exact isRegularClosed_sUnion_of_finite hS fun A hA => (hS' A hA).isRegularClosed

theorem IsFiniteUnion.isClosed (hF : IsFiniteUnion F) : IsClosed F :=
  hF.isRegularClosed.isClosed

theorem isFiniteUnion_iff_finset : IsFiniteUnion F ↔
    ∃ S : Finset (Set X), (∀ A ∈ S, IsRegSubcontinuum A) ∧ F = ⋃ A ∈ S, A := by
  constructor
  · rintro ⟨S, hS, hS', rfl⟩
    refine ⟨hS.toFinset, fun A hA => hS' A (hS.mem_toFinset.1 hA), ?_⟩
    ext z
    simp only [mem_sUnion, mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
  · rintro ⟨S, hS, rfl⟩
    refine ⟨↑S, S.finite_toSet, fun A hA => hS A hA, ?_⟩
    ext z
    simp only [mem_sUnion, mem_iUnion, Finset.mem_coe, exists_prop]

end Ops

section Main

variable {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- Core of Lemma 4.1. -/
theorem complement_core (hcount : (regular X).Countable) {A B : Set X}
    (hA : IsRegSubcontinuum A) (hB : IsRegSubcontinuum B) (hAB : (A ∩ B).Nonempty) :
    FinClopenCover (regDiff B A) (regDiff B A) ∧
      ∀ V : Set X, IsRelClopen (regDiff B A) V → V.Nonempty → (V ∩ A).Nonempty := by
  have hRB : regDiff B A ⊆ B := regDiff_subset_left hB.isClosed
  have hRreg : IsRegularClosed (regDiff B A) := isRegularClosed_regDiff hA.isClosed
  have hunion : A ∪ B = A ∪ regDiff B A := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact Or.inl hx
      · by_cases hxA : x ∈ A
        · exact Or.inl hxA
        · exact Or.inr (diff_subset_regDiff hB.isRegularClosed hA.isClosed ⟨hx, hxA⟩)
    · exact union_subset_union_right A hRB
  have hmeet : ∀ V : Set X, IsRelClopen (regDiff B A) V → V.Nonempty → (V ∩ A).Nonempty := by
    intro V hV hVne
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hY : IsPreconnected (A ∪ B) := (hA.isConnected.union hAB hB.isConnected).isPreconnected
    have hsub : A ∪ B ⊆ V ∪ (A ∪ (regDiff B A \ V)) := by
      rw [hunion]
      rintro x (hx | hx)
      · exact Or.inr (Or.inl hx)
      · by_cases hxV : x ∈ V
        · exact Or.inl hxV
        · exact Or.inr (Or.inr ⟨hx, hxV⟩)
    have hd : Disjoint V (A ∪ (regDiff B A \ V)) := by
      rw [Set.disjoint_left]
      rintro x hxV (hxA | hx)
      · have : x ∈ V ∩ A := ⟨hxV, hxA⟩
        rw [hemp] at this; exact this
      · exact hx.2 hxV
    obtain ⟨a, ha⟩ := hA.nonempty
    obtain ⟨w, hw⟩ := hVne
    rcases hY.subset_or_subset_of_closed hV.isClosed (hA.isClosed.union hV.isClosed_diff)
      hsub hd with h | h
    · have : a ∈ V ∩ A := ⟨h (Or.inl ha), ha⟩
      rw [hemp] at this; exact this
    · have hwY : w ∈ A ∪ B := by rw [hunion]; exact Or.inr (hV.subset hw)
      exact Set.disjoint_left.1 hd hw (h hwY)
  refine ⟨?_, hmeet⟩
  rcases finClopenCover_or_seq (isClosed_regDiff (F := B) (G := A)) with h | ⟨V, hV, hdisj⟩
  · exact h
  exfalso
  have hVreg : ∀ n, IsRegularClosed (V n) := fun n => (hV n).2.isRegularClosed hRreg
  have hCconn : ∀ n, IsPreconnected (A ∪ V n) := by
    intro n
    apply isPreconnected_of_closed_sep (hA.isClosed.union (hV n).2.isClosed)
    have aux : ∀ u v : Set X, IsClosed u → IsClosed v → u ∪ v = A ∪ V n → Disjoint u v →
        A ⊆ u → v = ∅ := by
      intro u v hu hv huv hd hAu
      by_contra hvne
      have hvV : v ⊆ V n := by
        intro z hz
        have : z ∈ A ∪ V n := huv ▸ Or.inr hz
        rcases this with h | h
        · exact absurd hz (Set.disjoint_left.1 hd (hAu h))
        · exact h
      have hdiff : V n \ v = V n ∩ u := by
        ext z
        constructor
        · rintro ⟨hzV, hzv⟩
          have : z ∈ u ∪ v := huv ▸ Or.inr hzV
          exact ⟨hzV, this.resolve_right hzv⟩
        · rintro ⟨hzV, hzu⟩
          exact ⟨hzV, fun hzv => Set.disjoint_left.1 hd hzu hzv⟩
      have hrel : IsRelClopen (regDiff B A) v :=
        (hV n).2.trans ⟨hvV, hv, by rw [hdiff]; exact (hV n).2.isClosed.inter hu⟩
      obtain ⟨z, hzv, hzA⟩ := hmeet v hrel (nonempty_iff_ne_empty.2 hvne)
      exact Set.disjoint_left.1 hd (hAu hzA) hzv
    intro u v hu hv huv hd
    have hAuv : A ⊆ u ∪ v := huv ▸ subset_union_left
    rcases hA.isPreconnected.subset_or_subset_of_closed hu hv hAuv hd with h | h
    · exact Or.inr (aux u v hu hv huv hd h)
    · exact Or.inl (aux v u hv hu (by rw [union_comm]; exact huv) hd.symm h)
  have hC : ∀ n, IsRegSubcontinuum (A ∪ V n) := fun n =>
    isRegSubcontinuum_of_isClosed (hA.isClosed.union (hV n).2.isClosed)
      ⟨hA.nonempty.mono subset_union_left, hCconn n⟩ (hA.isRegularClosed.union (hVreg n))
  have hind : IsIndependentOver A fun n => A ∪ V n := by
    intro n
    refine ⟨?_, ?_⟩
    · obtain ⟨a, ha⟩ := hA.nonempty
      exact ⟨a, Or.inl ha, ha⟩
    · obtain ⟨x, hxV, hxint, hxA⟩ :=
        IsRelClopen.inter_nonempty_of_closure (O := interior B \ A) (hV n).2 (hV n).1
      intro hsub
      have hcl : IsClosed (A ∪ (regDiff B A \ V n)) := hA.isClosed.union (hV n).2.isClosed_diff
      have hle : A ∪ ⋃ (m : ℕ) (_ : m ≠ n), (A ∪ V m) ⊆ A ∪ (regDiff B A \ V n) := by
        rintro z (hz | hz)
        · exact Or.inl hz
        · obtain ⟨m, hmn, hzm⟩ := mem_iUnion₂.1 hz
          rcases hzm with h | h
          · exact Or.inl h
          · exact Or.inr ⟨(hV m).2.subset h, fun hzn =>
              Set.disjoint_left.1 (hdisj hmn) h hzn⟩
      have := closure_minimal hle hcl (hsub (Or.inr hxV))
      rcases this with h | h
      · exact hxA h
      · exact h.2 hxV
  exact not_countable_of_card_eq_continuum (card_of_independent hA hC hind) hcount

/-- Lemma 4.1 (complement lemma). -/
theorem complement_lemma' (hcount : (regular X).Countable) {A B : Set X}
    (hA : IsRegSubcontinuum A) (hB : IsRegSubcontinuum B)
    (hAB : (A ∩ B).Nonempty) (hBA : ¬ B ⊆ A) :
    (regDiff B A).Nonempty ∧ IsRegularClosed (regDiff B A) ∧ regDiff B A ⊆ B ∧
    Disjoint (regDiff B A) (interior A) ∧ A ∪ B = A ∪ regDiff B A ∧
    (∀ C ∈ components (regDiff B A), (C ∩ A).Nonempty) ∧
    (components (regDiff B A)).Finite ∧
    (∀ C ∈ components (regDiff B A), IsRegSubcontinuum C) := by
  have hRB : regDiff B A ⊆ B := regDiff_subset_left hB.isClosed
  have hRreg : IsRegularClosed (regDiff B A) := isRegularClosed_regDiff hA.isClosed
  obtain ⟨hcov, hmeet⟩ := complement_core hcount hA hB hAB
  obtain ⟨hfin, hcomp⟩ := hcov.components_spec
  rw [not_subset] at hBA
  obtain ⟨b, hbB, hbA⟩ := hBA
  have hsubR := diff_subset_regDiff hB.isRegularClosed hA.isClosed (F := B) (G := A)
  refine ⟨⟨b, hsubR ⟨hbB, hbA⟩⟩, hRreg, hRB, disjoint_regDiff_interior, ?_, ?_, hfin, ?_⟩
  · apply Subset.antisymm
    · rintro x (hx | hx)
      · exact Or.inl hx
      · by_cases hxA : x ∈ A
        · exact Or.inl hxA
        · exact Or.inr (hsubR ⟨hx, hxA⟩)
    · exact union_subset_union_right A hRB
  · intro C hC
    exact hmeet C (hcomp C hC).2 (hcomp C hC).1.nonempty
  · intro C hC
    exact isRegSubcontinuum_of_isClosed (hcomp C hC).2.isClosed (hcomp C hC).1
      ((hcomp C hC).2.isRegularClosed hRreg)

/-- Proposition 4.3 (2). No countability is needed. -/
theorem components_of_isFiniteUnion' {F : Set X} (hF : IsFiniteUnion F) :
    (components F).Finite ∧ ∀ C ∈ components F, IsRegSubcontinuum C := by
  have hFreg := hF.isRegularClosed
  obtain ⟨S, hS, hS', rfl⟩ := hF
  rcases finClopenCover_or_seq hFreg.isClosed with h | ⟨V, hV, hdisj⟩
  · obtain ⟨hfin, hcomp⟩ := h.components_spec
    exact ⟨hfin, fun C hC => isRegSubcontinuum_of_isClosed (hcomp C hC).2.isClosed
      (hcomp C hC).1 ((hcomp C hC).2.isRegularClosed hFreg)⟩
  · exfalso
    have hex : ∀ n, ∃ A ∈ S, A ⊆ V n := by
      intro n
      obtain ⟨x, hx⟩ := (hV n).1
      obtain ⟨A, hAS, hxA⟩ := (hV n).2.subset hx
      exact ⟨A, hAS, (hV n).2.subset_of_isPreconnected (hS' A hAS).isPreconnected
        (subset_sUnion_of_mem hAS) ⟨x, hxA, hx⟩⟩
    choose a haS haV using hex
    have hinj : Injective a := by
      intro n m hnm
      by_contra hne
      obtain ⟨z, hz⟩ := (hS' (a n) (haS n)).nonempty
      exact Set.disjoint_left.1 (hdisj hne) (haV n hz) (haV m (hnm ▸ hz))
    exact (infinite_of_injective_forall_mem hinj haS) hS

theorem isFiniteUnion_regDiff_of_reg (hcount : (regular X).Countable) {A B : Set X}
    (hB : IsRegSubcontinuum B) (hA : IsRegSubcontinuum A) : IsFiniteUnion (regDiff B A) := by
  by_cases h1 : B ⊆ A
  · have : regDiff B A = ∅ := by
      rw [regDiff, sdiff_eq_empty.2 (interior_subset.trans h1), closure_empty]
    rw [this]; exact isFiniteUnion_empty
  by_cases h2 : (A ∩ B).Nonempty
  · obtain ⟨-, -, -, -, -, -, hfin, hreg⟩ := complement_lemma' hcount hA hB h2 h1
    exact ⟨components (regDiff B A), hfin, hreg, (sUnion_components _).symm⟩
  · have : regDiff B A = B := by
      have hd : interior B \ A = interior B := by
        ext z
        constructor
        · exact fun hz => hz.1
        · exact fun hz => ⟨hz, fun hzA => h2 ⟨z, hzA, interior_subset hz⟩⟩
      rw [regDiff, hd, hB.isRegularClosed.eq]
    rw [this]; exact hB.isFiniteUnion

theorem isFiniteUnion_regDiff_reg (hcount : (regular X).Countable) {F A : Set X}
    (hF : IsFiniteUnion F) (hA : IsRegSubcontinuum A) : IsFiniteUnion (regDiff F A) := by
  classical
  obtain ⟨S, hS, rfl⟩ := isFiniteUnion_iff_finset.1 hF
  induction S using Finset.induction_on with
  | empty =>
    have : regDiff (⋃ B ∈ (∅ : Finset (Set X)), B) A = ∅ := by simp [regDiff]
    rw [this]; exact isFiniteUnion_empty
  | insert B S hBS ih =>
    have hS1 : ∀ C ∈ S, IsRegSubcontinuum C := fun C hC => hS C (Finset.mem_insert_of_mem hC)
    have hB : IsRegSubcontinuum B := hS B (Finset.mem_insert_self B S)
    have hFS : IsFiniteUnion (⋃ C ∈ S, C) := isFiniteUnion_iff_finset.2 ⟨S, hS1, rfl⟩
    rw [Finset.set_biUnion_insert,
      regDiff_union_left hB.isRegularClosed hFS.isRegularClosed hA.isClosed]
    exact (isFiniteUnion_regDiff_of_reg hcount hB hA).union (ih hS1 hFS)

theorem isFiniteUnion_regDiff (hcount : (regular X).Countable) {F G : Set X}
    (hF : IsFiniteUnion F) (hG : IsFiniteUnion G) : IsFiniteUnion (regDiff F G) := by
  classical
  obtain ⟨T, hT, rfl⟩ := isFiniteUnion_iff_finset.1 hG
  induction T using Finset.induction_on generalizing F with
  | empty =>
    have : regDiff F (⋃ B ∈ (∅ : Finset (Set X)), B) = F := by
      simp [regDiff, hF.isRegularClosed.eq]
    rw [this]; exact hF
  | insert A T hAT ih =>
    have hT1 : ∀ C ∈ T, IsRegSubcontinuum C := fun C hC => hT C (Finset.mem_insert_of_mem hC)
    have hA : IsRegSubcontinuum A := hT A (Finset.mem_insert_self A T)
    have hGT : IsFiniteUnion (⋃ C ∈ T, C) := isFiniteUnion_iff_finset.2 ⟨T, hT1, rfl⟩
    rw [Finset.set_biUnion_insert, ← regDiff_regDiff hA.isClosed hGT.isClosed]
    exact ih (isFiniteUnion_regDiff_reg hcount hF hA) hT1 hGT

theorem isFiniteUnion_regMeet (hcount : (regular X).Countable) {F G : Set X}
    (hF : IsFiniteUnion F) (hG : IsFiniteUnion G) : IsFiniteUnion (regMeet F G) := by
  rw [regMeet_eq_regDiff_regDiff]
  exact isFiniteUnion_regDiff hcount hF (isFiniteUnion_regDiff hcount hF hG)

/-- Theorem 4.4 (absorption). -/
theorem absorption' (hcount : (regular X).Countable) {N A : Set X}
    (hN : IsMinimalReg N) (hA : IsRegSubcontinuum A) :
    N ⊆ A ∨ Disjoint N (interior A) := by
  by_cases h1 : N ⊆ A
  · exact Or.inl h1
  right
  by_cases h2 : (A ∩ N).Nonempty
  · obtain ⟨⟨x, hx⟩, -, hRN, hdisj, -, -, -, hreg⟩ := complement_lemma' hcount hA hN.1 h2 h1
    have hC : connectedComponentIn (regDiff N A) x ∈ components (regDiff N A) := ⟨x, hx, rfl⟩
    have hCsub : connectedComponentIn (regDiff N A) x ⊆ N :=
      (connectedComponentIn_subset _ x).trans hRN
    have heq := hN.2 _ (hreg _ hC) hCsub
    have hNR : N ⊆ regDiff N A := by
      have h := connectedComponentIn_subset (regDiff N A) x
      rw [heq] at h
      exact h
    exact hdisj.mono_left hNR
  · rw [Set.disjoint_left]
    intro z hzN hzA
    exact h2 ⟨z, interior_subset hzA, hzN⟩

/-- Corollary 4.5. -/
theorem minimal_disjoint_interior' (hcount : (regular X).Countable) {N N' : Set X}
    (hN : IsMinimalReg N) (hN' : IsMinimalReg N') (hne : N ≠ N') :
    Disjoint N (interior N') := by
  rcases absorption' hcount hN hN'.1 with h | h
  · exact absurd (hN'.2 N hN.1 h) hne
  · exact h

end Main

end RegularSubcontinua
