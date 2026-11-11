module

public import RegularSubcontinua.Complement

@[expose] public section

/-!
# Decreasing intersections (Lemma 4.6)

The connectedness of the finite deletions is proved by closed separations; boundary bumping is
not needed.
-/

open Set Function TopologicalSpace Topology
open scoped Cardinal

universe u

namespace RegularSubcontinua

variable {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

theorem decreasing_core (hcount : (regular X).Countable) {A : ℕ → Set X}
    (hA : ∀ n, IsRegSubcontinuum (A n)) (hanti : Antitone A) :
    FinClopenCover (closure (⋂ n, A n)ᶜ) (closure (⋂ n, A n)ᶜ) := by
  classical
  set K : Set X := ⋂ n, A n with hKdef
  set R : Set X := closure Kᶜ with hRdef
  have hKconn : IsConnected K :=
    isConnected_iInter_of_antitone hanti (fun n => (hA n).isCompact) fun n => (hA n).isConnected
  have hKcl : IsClosed K := isClosed_iInter fun n => (hA n).isClosed
  have hKR : Kᶜ ⊆ R := subset_closure
  rcases finClopenCover_or_seq (isClosed_closure : IsClosed R) with h | ⟨V, hV, hdisj⟩
  · exact h
  exfalso
  have hex : ∀ i, ∃ x : X, ∃ n : ℕ, x ∈ V i ∧ x ∉ A n := by
    intro i
    obtain ⟨x, hxV, hxK⟩ := IsRelClopen.inter_nonempty_of_closure (O := Kᶜ) (hV i).2 (hV i).1
    have : ¬ ∀ n, x ∈ A n := fun h => hxK (mem_iInter.2 h)
    rw [not_forall] at this
    obtain ⟨n, hn⟩ := this
    exact ⟨x, n, hxV, hn⟩
  choose x n hxV hxA using hex
  let W : ℕ → Set X := fun i => (R \ V i)ᶜ
  have hWo : ∀ i, IsOpen (W i) := fun i => (hV i).2.isClosed_diff.isOpen_compl
  have hVW : ∀ i, V i ⊆ W i := fun i z hz hz' => hz'.2 hz
  have hWV : ∀ i z, z ∈ W i → z ∈ R → z ∈ V i := by
    intro i z hzW hzR
    by_contra hzV
    exact hzW ⟨hzR, hzV⟩
  let O : ℕ → Set X := fun i => W i \ A (n i)
  have hOo : ∀ i, IsOpen (O i) := fun i => (hWo i).sdiff (hA (n i)).isClosed
  have hOne : ∀ i, (O i).Nonempty := fun i => ⟨x i, hVW i (hxV i), hxA i⟩
  have hKA : ∀ m, K ⊆ A m := fun m => iInter_subset _ m
  have hOV : ∀ i, O i ⊆ V i := by
    rintro i z ⟨hzW, hzA⟩
    exact hWV i z hzW (hKR fun hzK => hzA (hKA _ hzK))
  have hVdis : ∀ i j, i ≠ j → ∀ z, z ∈ V i → z ∉ V j := fun i j hij z hzi hzj =>
    Set.disjoint_left.1 (hdisj hij) hzi hzj
  have hOdisj : Pairwise (Disjoint on O) := fun i j hij =>
    (hdisj hij).mono (hOV i) (hOV j)
  -- a point of `V i ∩ A (n i)` is not in any `O j`
  have hnotO : ∀ i z, z ∈ V i → z ∈ A (n i) → ∀ j, z ∉ O j := by
    intro i z hzV hzA j hzO
    by_cases hij : i = j
    · subst hij; exact hzO.2 hzA
    · exact hVdis i j hij z hzV (hOV j hzO)
  have hY : ∀ F : Finset ℕ, IsRegSubcontinuum (univ \ ⋃ i ∈ F, O i) := by
    intro F
    set Y : Set X := univ \ ⋃ i ∈ F, O i with hYdef
    have hmemY : ∀ z, z ∈ Y ↔ ∀ i ∈ F, z ∉ O i := by
      intro z
      simp only [hYdef, mem_sdiff, mem_univ, true_and, mem_iUnion, not_exists]
    have hYcl : IsClosed Y := isClosed_univ.sdiff (isOpen_biUnion fun i _ => hOo i)
    have hKY : K ⊆ Y := fun z hz => (hmemY z).2 fun i _ hzO => hzO.2 (hKA _ hz)
    obtain ⟨k₀, hk₀⟩ := hKconn.nonempty
    -- members of `V i ∩ Y` (`i ∈ F`) lie in `A (n i)`
    have hVY : ∀ i ∈ F, ∀ z, z ∈ V i → z ∈ Y → z ∈ A (n i) := by
      intro i hi z hzV hzY
      by_contra hzA
      exact (hmemY z).1 hzY i hi ⟨hVW i hzV, hzA⟩
    have aux : ∀ u v : Set X, IsClosed u → IsClosed v → u ∪ v = Y → Disjoint u v →
        K ⊆ u → v = ∅ := by
      intro u v hu hv huv hd hKu
      by_contra hvne
      obtain ⟨q, hqv⟩ := nonempty_iff_ne_empty.2 hvne
      have hqY : q ∈ Y := huv ▸ Or.inr hqv
      have hvK : ∀ z, z ∈ v → z ∉ K := fun z hzv hzK =>
        Set.disjoint_left.1 hd (hKu hzK) hzv
      by_cases hqV : ∃ i ∈ F, q ∈ V i
      · obtain ⟨i, hiF, hqVi⟩ := hqV
        have hqA : q ∈ A (n i) := hVY i hiF q hqVi hqY
        let P : Set X := (A (n i) ∩ u ∩ V i) ∪ (A (n i) ∩ (R \ V i)) ∪ K
        let Q : Set X := A (n i) ∩ v ∩ V i
        have hPcl : IsClosed P :=
          ((((hA (n i)).isClosed.inter hu).inter (hV i).2.isClosed).union
            ((hA (n i)).isClosed.inter (hV i).2.isClosed_diff)).union hKcl
        have hQcl : IsClosed Q := ((hA (n i)).isClosed.inter hv).inter (hV i).2.isClosed
        have hcov : A (n i) ⊆ P ∪ Q := by
          intro z hzA
          by_cases hzK : z ∈ K
          · exact Or.inl (Or.inr hzK)
          by_cases hzV : z ∈ V i
          · have hzY : z ∈ Y := (hmemY z).2 fun j _ => hnotO i z hzV hzA j
            have : z ∈ u ∪ v := huv ▸ hzY
            rcases this with h | h
            · exact Or.inl (Or.inl (Or.inl ⟨⟨hzA, h⟩, hzV⟩))
            · exact Or.inr ⟨⟨hzA, h⟩, hzV⟩
          · exact Or.inl (Or.inl (Or.inr ⟨hzA, hKR hzK, hzV⟩))
        have hPQ : Disjoint P Q := by
          rw [Set.disjoint_left]
          rintro z ((⟨⟨_, hzu⟩, _⟩ | ⟨_, _, hzV⟩) | hzK) ⟨⟨_, hzv⟩, hzV'⟩
          · exact Set.disjoint_left.1 hd hzu hzv
          · exact hzV hzV'
          · exact hvK z hzv hzK
        rcases (hA (n i)).isPreconnected.subset_or_subset_of_closed hPcl hQcl hcov hPQ with h | h
        · exact Set.disjoint_left.1 hPQ (h hqA) ⟨⟨hqA, hqv⟩, hqVi⟩
        · exact hvK k₀ (h (hKA _ hk₀)).1.2 hk₀
      · rw [not_exists] at hqV
        have hqV' : ∀ i ∈ F, q ∉ V i := fun i hi hq => hqV i ⟨hi, hq⟩
        have hvR : v ⊆ R := fun z hz => hKR (hvK z hz)
        let P : Set X := u ∪ ⋃ i ∈ F, V i
        let Q : Set X := v ∩ ⋂ i ∈ F, (R \ V i)
        have hPcl : IsClosed P := hu.union (isClosed_biUnion_finset fun i _ => (hV i).2.isClosed)
        have hQcl : IsClosed Q := hv.inter (isClosed_biInter fun i _ => (hV i).2.isClosed_diff)
        have hcov : (univ : Set X) ⊆ P ∪ Q := by
          intro z _
          by_cases hzV : ∃ i ∈ F, z ∈ V i
          · obtain ⟨i, hi, hz⟩ := hzV
            exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨i, hi, hz⟩))
          · rw [not_exists] at hzV
            have hzV' : ∀ i ∈ F, z ∉ V i := fun i hi hz => hzV i ⟨hi, hz⟩
            have hzY : z ∈ Y := (hmemY z).2 fun i hi hzO => hzV' i hi (hOV i hzO)
            have : z ∈ u ∪ v := huv ▸ hzY
            rcases this with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr ⟨h, mem_iInter₂.2 fun i hi => ⟨hvR h, hzV' i hi⟩⟩
        have hPQ : Disjoint P Q := by
          rw [Set.disjoint_left]
          rintro z (hzu | hzV) ⟨hzv, hzI⟩
          · exact Set.disjoint_left.1 hd hzu hzv
          · obtain ⟨i, hi, hz⟩ := mem_iUnion₂.1 hzV
            exact (mem_iInter₂.1 hzI i hi).2 hz
        have hqQ : q ∈ Q := ⟨hqv, mem_iInter₂.2 fun i hi => ⟨hvR hqv, hqV' i hi⟩⟩
        rcases isPreconnected_univ.subset_or_subset_of_closed hPcl hQcl hcov hPQ with h | h
        · exact Set.disjoint_left.1 hPQ (h (mem_univ q)) hqQ
        · exact hvK k₀ (h (mem_univ k₀)).1 hk₀
    have hYpre : IsPreconnected Y := by
      apply isPreconnected_of_closed_sep hYcl
      intro u v hu hv huv hd
      have hKuv : K ⊆ u ∪ v := huv ▸ hKY
      rcases hKconn.isPreconnected.subset_or_subset_of_closed hu hv hKuv hd with h | h
      · exact Or.inr (aux u v hu hv huv hd h)
      · exact Or.inl (aux v u hv hu (by rw [union_comm]; exact huv) hd.symm h)
    have hYreg : IsRegularClosed Y := by
      apply Subset.antisymm (closure_minimal interior_subset hYcl)
      intro y hyY
      by_cases hyK : y ∈ K
      · have hAN : A (F.sup n) ⊆ Y := fun z hz =>
          (hmemY z).2 fun i hi hzO => hzO.2 (hanti (Finset.le_sup hi) hz)
        exact (hA (F.sup n)).isRegularClosed.subset_closure_interior_of_subset hAN
          (hKA _ hyK)
      by_cases hyV : ∃ i ∈ F, y ∈ V i
      · obtain ⟨i, hiF, hyVi⟩ := hyV
        have hyA : y ∈ A (n i) := hVY i hiF y hyVi hyY
        have hU : IsOpen (W i ∩ Kᶜ) := (hWo i).inter hKcl.isOpen_compl
        have hsub : interior (A (n i)) ∩ (W i ∩ Kᶜ) ⊆ interior Y := by
          apply interior_maximal _ (isOpen_interior.inter hU)
          rintro z ⟨hzA, hzW, hzK⟩
          have hzV : z ∈ V i := hWV i z hzW (hKR hzK)
          exact (hmemY z).2 fun j _ => hnotO i z hzV (interior_subset hzA) j
        have hycl : y ∈ closure (interior (A (n i))) := by
          rw [(hA (n i)).isRegularClosed.eq]; exact hyA
        rw [mem_closure_iff]
        intro o ho hyo
        obtain ⟨z, ⟨hzo, hzU⟩, hzint⟩ :=
          mem_closure_iff.1 hycl (o ∩ (W i ∩ Kᶜ)) (ho.inter hU) ⟨hyo, hVW i hyVi, hyK⟩
        exact ⟨z, hzo, hsub ⟨hzint, hzU⟩⟩
      · rw [not_exists] at hyV
        have hUo : IsOpen (⋃ i ∈ F, V i)ᶜ :=
          (isClosed_biUnion_finset fun i _ => (hV i).2.isClosed).isOpen_compl
        have hUY : (⋃ i ∈ F, V i)ᶜ ⊆ Y := fun z hz =>
          (hmemY z).2 fun i hi hzO => hz (mem_iUnion₂.2 ⟨i, hi, hOV i hzO⟩)
        have hyU : y ∈ (⋃ i ∈ F, V i)ᶜ := fun hy => by
          obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
          exact hyV i ⟨hi, hyi⟩
        exact subset_closure (interior_maximal hUY hUo hyU)
    exact isRegSubcontinuum_of_isClosed hYcl ⟨⟨k₀, hKY hk₀⟩, hYpre⟩ hYreg
  exact not_countable_of_card_eq_continuum
    (card_of_blisters isRegSubcontinuum_univ hOo hOne (fun i => subset_univ _) hOdisj hY) hcount

/-- Lemma 4.6 (decreasing intersections). -/
theorem decreasing_intersection' (hcount : (regular X).Countable) {A : ℕ → Set X}
    (hA : ∀ n, IsRegSubcontinuum (A n)) (hanti : Antitone A) :
    IsFiniteUnion (closure ((⋂ n, A n)ᶜ)) ∧
    IsFiniteUnion (closure (interior (⋂ n, A n))) ∧
    ((interior (⋂ n, A n)).Nonempty →
      ∃ B : Set X, IsRegSubcontinuum B ∧ B ⊆ ⋂ n, A n) := by
  have hKcl : IsClosed (⋂ n, A n) := isClosed_iInter fun n => (hA n).isClosed
  have hRreg : IsRegularClosed (closure ((⋂ n, A n)ᶜ)) :=
    isRegularClosed_closure_of_isOpen hKcl.isOpen_compl
  obtain ⟨𝒞, hfin, h𝒞, hU⟩ := decreasing_core hcount hA hanti
  have hR : IsFiniteUnion (closure ((⋂ n, A n)ᶜ)) :=
    ⟨𝒞, hfin, fun C hC => isRegSubcontinuum_of_isClosed (h𝒞 C hC).2.isClosed (h𝒞 C hC).1
      ((h𝒞 C hC).2.isRegularClosed hRreg), hU.symm⟩
  have heq : closure (interior (⋂ n, A n)) = regDiff univ (closure ((⋂ n, A n)ᶜ)) := by
    have h1 : closure ((⋂ n, A n)ᶜ) = (interior (⋂ n, A n))ᶜ := closure_compl
    rw [regDiff, interior_univ, ← compl_eq_univ_sdiff, h1, compl_compl]
  have hI : IsFiniteUnion (closure (interior (⋂ n, A n))) := by
    rw [heq]
    exact isFiniteUnion_regDiff hcount isRegSubcontinuum_univ.isFiniteUnion hR
  refine ⟨hR, hI, fun hne => ?_⟩
  obtain ⟨S, -, hS, hSU⟩ := hI
  obtain ⟨z, hz⟩ := hne
  have hz' : z ∈ ⋃₀ S := hSU ▸ subset_closure hz
  obtain ⟨B, hBS, -⟩ := hz'
  refine ⟨B, hS B hBS, ?_⟩
  calc B ⊆ ⋃₀ S := subset_sUnion_of_mem hBS
    _ = closure (interior (⋂ n, A n)) := hSU.symm
    _ ⊆ ⋂ n, A n := closure_minimal interior_subset hKcl

end RegularSubcontinua
