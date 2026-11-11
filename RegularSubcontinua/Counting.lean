module

public import RegularSubcontinua.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Order.Interval.Finset.Basic

@[expose] public section

/-!
# Counting principles: cardinality bounds, independent families (Lemma 3.2), thinning (Lemma 2.7),
and the blister theorem (Theorem 3.4)
-/

open Set Function TopologicalSpace Topology
open scoped Cardinal

universe u

namespace RegularSubcontinua

/-! ### Nested intersections -/

theorem isConnected_iInter_of_antitone {X : Type*} [TopologicalSpace X] [T2Space X]
    {B : ℕ → Set X} (hanti : Antitone B) (hc : ∀ n, IsCompact (B n))
    (hconn : ∀ n, IsConnected (B n)) : IsConnected (⋂ n, B n) :=
  ⟨IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed B
      (fun i => hanti (Nat.le_succ i)) (fun i => (hconn i).nonempty) (hc 0)
      (fun i => (hc i).isClosed),
    isPreconnected_iInter_of_antitone hanti hc fun n => (hconn n).isPreconnected⟩

/-! ### Thinning -/

/-- Lemma 2.7 (thinning), in the form used: infinitely many indices can be discarded without
losing any point at which the family accumulates. -/
theorem exists_thinning {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (O : ℕ → Set X) :
    ∃ Ψ : Set ℕ, Ψᶜ.Infinite ∧ ∀ y : X,
      (∀ U : Set X, IsOpen U → y ∈ U → {n | (O n ∩ U).Nonempty}.Infinite) →
      y ∈ closure (⋃ n ∈ Ψ, O n) := by
  obtain ⟨b, hbc, -, hb⟩ := exists_countable_basis X
  have hb'c : (insert univ b).Countable := hbc.insert univ
  obtain ⟨e, he⟩ := hb'c.exists_eq_range (insert_nonempty univ b)
  have heb : ∀ v ∈ b, ∃ k, e k = v := by
    intro v hv
    have : v ∈ range e := he ▸ mem_insert_of_mem univ hv
    exact this
  have heo : ∀ k, IsOpen (e k) := by
    intro k
    have : e k ∈ insert univ b := he ▸ mem_range_self k
    rcases this with h | h
    · rw [h]; exact isOpen_univ
    · exact hb.isOpen h
  have H : ∀ k m : ℕ, ∃ n, m ≤ n ∧
      ({n | (O n ∩ e k).Nonempty}.Infinite → (O n ∩ e k).Nonempty) := by
    intro k m
    by_cases hgood : {n | (O n ∩ e k).Nonempty}.Infinite
    · obtain ⟨n, hn, hmn⟩ := hgood.exists_gt m
      exact ⟨n, hmn.le, fun _ => hn⟩
    · exact ⟨m, le_rfl, fun h => absurd h hgood⟩
  choose g hg using H
  let f : ℕ → ℕ := fun k => Nat.rec (g 0 0) (fun k fk => g (k + 1) (fk + 2)) k
  have hf_succ : ∀ k, f (k + 1) = g (k + 1) (f k + 2) := fun k => rfl
  have hstep : ∀ k, f k + 2 ≤ f (k + 1) := fun k => by
    rw [hf_succ]; exact (hg (k + 1) (f k + 2)).1
  have hmono : StrictMono f := strictMono_nat_of_lt_succ fun k => by
    have := hstep k; omega
  have hgoodk : ∀ k, {n | (O n ∩ e k).Nonempty}.Infinite → (O (f k) ∩ e k).Nonempty := by
    intro k
    cases k with
    | zero => exact (hg 0 0).2
    | succ k => rw [hf_succ]; exact (hg (k + 1) (f k + 2)).2
  refine ⟨range f, ?_, ?_⟩
  · have hinj : Injective fun k => f k + 1 := fun a c h => hmono.injective (by simpa using h)
    apply infinite_of_injective_forall_mem hinj
    rintro k ⟨j, hj⟩
    rcases le_or_gt j k with hjk | hjk
    · have := hmono.monotone hjk; omega
    · have h1 := hmono.monotone (show k + 1 ≤ j from hjk)
      have h2 := hstep k
      omega
  · intro y hy
    rw [mem_closure_iff]
    intro o ho hyo
    obtain ⟨v, hvb, hyv, hvo⟩ := hb.exists_subset_of_mem_open hyo ho
    obtain ⟨k, rfl⟩ := heb v hvb
    obtain ⟨z, hzO, hzv⟩ := hgoodk k (hy (e k) (heo k) hyv)
    exact ⟨z, hvo hzv, mem_iUnion₂.2 ⟨f k, mem_range_self k, hzO⟩⟩

/-! ### The hyperspace and cardinality -/

section Card

variable {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- A regular subcontinuum, as a point of the hyperspace `regular X`. -/
def toRegular (A : Set X) (hA : IsRegSubcontinuum A) : ↥(regular X) :=
  ⟨⟨⟨⟨A, hA.isCompact⟩, hA.nonempty⟩, hA.isConnected⟩, hA.isRegularClosed⟩

@[simp]
theorem coe_toRegular (A : Set X) (hA : IsRegSubcontinuum A) :
    ((toRegular A hA).1.1 : Set X) = A := rfl

theorem isRegSubcontinuum_coe (K : ↥(regular X)) : IsRegSubcontinuum (K.1.1 : Set X) :=
  ⟨K.1.1.isCompact, K.1.2, K.2⟩

theorem toRegular_coe (K : ↥(regular X)) :
    toRegular (K.1.1 : Set X) (isRegSubcontinuum_coe K) = K := by
  apply Subtype.ext
  apply Subtype.ext
  apply SetLike.coe_injective
  rfl

theorem coe_injective_regular :
    Injective fun K : ↥(regular X) => (K.1.1 : Set X) := by
  intro K L h
  apply Subtype.ext
  apply Subtype.ext
  exact SetLike.coe_injective h

theorem isRegSubcontinuum_iff_exists (A : Set X) :
    IsRegSubcontinuum A ↔ ∃ K ∈ regular X, (K.1 : Set X) = A := by
  constructor
  · intro hA
    exact ⟨(toRegular A hA).1, (toRegular A hA).2, rfl⟩
  · rintro ⟨K, hK, rfl⟩
    exact isRegSubcontinuum_coe ⟨K, hK⟩

theorem countable_setOf_isRegSubcontinuum (hcount : (regular X).Countable) :
    {A : Set X | IsRegSubcontinuum A}.Countable := by
  have : {A : Set X | IsRegSubcontinuum A} = (fun K : Subcontinua X => (K.1 : Set X)) '' regular X := by
    ext A
    rw [mem_ofPred_eq, isRegSubcontinuum_iff_exists]
    constructor
    · rintro ⟨K, hK, rfl⟩; exact ⟨K, hK, rfl⟩
    · rintro ⟨K, hK, rfl⟩; exact ⟨K, hK, rfl⟩
  rw [this]
  exact hcount.image _

theorem card_regular_le_continuum : #(↥(regular X)) ≤ 𝔠 := by
  let Y := ↥(regular X)
  let b := countableBasis Y
  have hbc : b.Countable := countable_countableBasis Y
  have hb : IsTopologicalBasis b := isBasis_countableBasis Y
  let φ : Y → Set ↥b := fun y => {v | y ∈ (v : Set Y)}
  have hφ : Injective φ := by
    intro y z hyz
    by_contra hne
    obtain ⟨v, hvb, hyv, hvsub⟩ :=
      hb.exists_subset_of_mem_open (show y ∈ ({z} : Set Y)ᶜ from hne) isOpen_compl_singleton
    have h1 : (⟨v, hvb⟩ : ↥b) ∈ φ y := hyv
    rw [hyz] at h1
    exact hvsub h1 rfl
  calc #Y ≤ #(Set ↥b) := Cardinal.mk_le_of_injective hφ
    _ = 2 ^ #(↥b) := Cardinal.mk_set
    _ ≤ 2 ^ ℵ₀ := Cardinal.power_le_power_left two_ne_zero (Cardinal.le_aleph0_iff_set_countable.2 hbc)
    _ = 𝔠 := Cardinal.two_power_aleph0

theorem continuum_le_card_regular {F : Set ℕ → Set X} (hF : ∀ T, IsRegSubcontinuum (F T))
    (hinj : Injective F) : 𝔠 ≤ #(↥(regular X)) := by
  have hemb : Nonempty (Set ℕ ↪ ↥(regular X)) :=
    ⟨⟨fun T => toRegular (F T) (hF T), fun T T' h => hinj (by
      have := congrArg (fun K : ↥(regular X) => (K.1.1 : Set X)) h
      simpa using this)⟩⟩
  have h := Cardinal.lift_mk_le'.2 hemb
  rw [Cardinal.mk_set_nat, Cardinal.lift_continuum, Cardinal.lift_uzero] at h
  exact h

theorem card_regular_eq_continuum {F : Set ℕ → Set X} (hF : ∀ T, IsRegSubcontinuum (F T))
    (hinj : Injective F) : #(↥(regular X)) = 𝔠 :=
  le_antisymm card_regular_le_continuum (continuum_le_card_regular hF hinj)

theorem not_countable_of_card_eq_continuum (h : #(↥(regular X)) = 𝔠) :
    ¬ (regular X).Countable := by
  intro hc
  have := Cardinal.le_aleph0_iff_set_countable.2 hc
  rw [h] at this
  exact absurd Cardinal.aleph0_lt_continuum (not_lt.2 this)

/-! ### Independent families (Lemma 3.2) -/

theorem card_of_independent {A : Set X} {C : ℕ → Set X}
    (hA : IsRegSubcontinuum A) (hC : ∀ n, IsRegSubcontinuum (C n))
    (h : IsIndependentOver A C) : #(↥(regular X)) = 𝔠 := by
  classical
  let s : Set ℕ → ℕ → Set X := fun Θ n => if n ∈ Θ then A ∪ C n else A
  let B : Set ℕ → Set X := fun Θ => closure (⋃ n, s Θ n)
  have hsreg : ∀ Θ n, IsRegSubcontinuum (s Θ n) := by
    intro Θ n
    by_cases hn : n ∈ Θ
    · simp only [s, ite_eq_left hn]
      exact hA.union (hC n) (by rw [inter_comm]; exact (h n).1)
    · simp only [s, ite_eq_right hn]
      exact hA
  have hAs : ∀ Θ n, A ⊆ s Θ n := by
    intro Θ n
    by_cases hn : n ∈ Θ
    · simp only [s, ite_eq_left hn]; exact subset_union_left
    · simp only [s, ite_eq_right hn]; exact Subset.rfl
  have hB : ∀ Θ, IsRegSubcontinuum (B Θ) := by
    intro Θ
    obtain ⟨a, ha⟩ := hA.nonempty
    have hpre : IsPreconnected (⋃ n, s Θ n) :=
      isPreconnected_iUnion ⟨a, mem_iInter.2 fun n => hAs Θ n ha⟩
        fun n => (hsreg Θ n).isPreconnected
    refine isRegSubcontinuum_of_isClosed isClosed_closure
      ⟨⟨a, subset_closure (mem_iUnion.2 ⟨0, hAs Θ 0 ha⟩)⟩, hpre.closure⟩
      (isRegularClosed_closure_iUnion fun n => (hsreg Θ n).isRegularClosed)
  have hx : ∀ n, ∃ x, x ∈ C n ∧ x ∉ closure (A ∪ ⋃ (m : ℕ) (_ : m ≠ n), C m) := by
    intro n
    have := (h n).2
    rw [not_subset] at this
    obtain ⟨x, hx1, hx2⟩ := this
    exact ⟨x, hx1, hx2⟩
  choose x hx1 hx2 using hx
  have hmem : ∀ Θ n, x n ∈ B Θ ↔ n ∈ Θ := by
    intro Θ n
    constructor
    · intro hxn
      by_contra hn
      apply hx2 n
      refine closure_mono ?_ hxn
      intro z hz
      obtain ⟨m, hm⟩ := mem_iUnion.1 hz
      by_cases hmΘ : m ∈ Θ
      · simp only [s, ite_eq_left hmΘ] at hm
        rcases hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr (mem_iUnion₂.2 ⟨m, fun hmn => hn (hmn ▸ hmΘ), hm⟩)
      · simp only [s, ite_eq_right hmΘ] at hm
        exact Or.inl hm
    · intro hn
      apply subset_closure
      refine mem_iUnion.2 ⟨n, ?_⟩
      simp only [s, ite_eq_left hn]
      exact Or.inr (hx1 n)
  apply card_regular_eq_continuum hB
  intro Θ Θ' hΘ
  ext n
  rw [← hmem Θ n, ← hmem Θ' n]
  show x n ∈ B Θ ↔ x n ∈ B Θ'
  rw [show B Θ = B Θ' from hΘ]

/-! ### The blister theorem (Theorem 3.4) -/

theorem card_of_blisters {A : Set X} {O : ℕ → Set X}
    (hA : IsRegSubcontinuum A) (hopen : ∀ n, IsOpen (O n))
    (hne : ∀ n, (O n).Nonempty) (hsub : ∀ n, O n ⊆ A)
    (hdisj : Pairwise (Disjoint on O))
    (hfin : ∀ F : Finset ℕ, IsRegSubcontinuum (A \ ⋃ n ∈ F, O n)) :
    #(↥(regular X)) = 𝔠 := by
  classical
  let Y : Set ℕ → Set X := fun Ψ => A \ ⋃ (n : ℕ) (_ : n ∉ Ψ), O n
  -- membership
  have hY : ∀ Ψ z, z ∈ Y Ψ ↔ z ∈ A ∧ ∀ n, n ∉ Ψ → z ∉ O n := by
    intro Ψ z
    simp only [Y, mem_sdiff, mem_iUnion, not_exists]
  have hdis : ∀ n m, n ≠ m → ∀ z, z ∈ O n → z ∉ O m := fun n m hnm z hzn hzm =>
    Set.disjoint_left.1 (hdisj hnm) hzn hzm
  -- retained blisters lie in `Y Ψ`
  have hOY : ∀ Ψ n, n ∈ Ψ → O n ⊆ Y Ψ := by
    intro Ψ n hn z hz
    rw [hY]
    exact ⟨hsub n hz, fun m hm => hdis n m (fun h => hm (h ▸ hn)) z hz⟩
  have hclosed : ∀ Ψ, IsClosed (Y Ψ) := by
    intro Ψ
    have : Y Ψ = A ∩ (⋃ (n : ℕ) (_ : n ∉ Ψ), O n)ᶜ := rfl
    rw [this]
    exact hA.isClosed.inter
      (isOpen_iUnion fun n => isOpen_iUnion fun _ => hopen n).isClosed_compl
  -- connectedness
  have hconn : ∀ Ψ, IsConnected (Y Ψ) := by
    intro Ψ
    let B : ℕ → Set X := fun k => A \ ⋃ n ∈ (Finset.range k).filter (· ∉ Ψ), O n
    have hBreg : ∀ k, IsRegSubcontinuum (B k) := fun k => hfin _
    have hBanti : Antitone B := by
      intro k l hkl z hz
      refine ⟨hz.1, fun hzu => hz.2 ?_⟩
      obtain ⟨n, hn, hzn⟩ := mem_iUnion₂.1 hzu
      rw [Finset.mem_filter, Finset.mem_range] at hn
      exact mem_iUnion₂.2 ⟨n, by
        rw [Finset.mem_filter, Finset.mem_range]; exact ⟨lt_of_lt_of_le hn.1 hkl, hn.2⟩, hzn⟩
    have hYB : Y Ψ = ⋂ k, B k := by
      ext z
      rw [hY, mem_iInter]
      constructor
      · rintro ⟨hzA, hz⟩ k
        refine ⟨hzA, fun hzu => ?_⟩
        obtain ⟨n, hn, hzn⟩ := mem_iUnion₂.1 hzu
        rw [Finset.mem_filter] at hn
        exact hz n hn.2 hzn
      · intro hz
        refine ⟨(hz 0).1, fun n hn hzn => (hz (n + 1)).2 ?_⟩
        exact mem_iUnion₂.2 ⟨n, by
          rw [Finset.mem_filter, Finset.mem_range]; exact ⟨Nat.lt_succ_self n, hn⟩, hzn⟩
    rw [hYB]
    exact isConnected_iInter_of_antitone hBanti (fun k => (hBreg k).isCompact)
      fun k => (hBreg k).isConnected
  -- thinning
  obtain ⟨Ψ₀, hΨ₀inf, hΨ₀⟩ := exists_thinning O
  have hreg : ∀ Ψ, Ψ₀ ⊆ Ψ → IsRegularClosed (Y Ψ) := by
    intro Ψ hΨ
    apply Subset.antisymm (closure_minimal interior_subset (hclosed Ψ))
    intro y hy
    have hOint : ∀ n, n ∈ Ψ → O n ⊆ interior (Y Ψ) := fun n hn =>
      interior_maximal (hOY Ψ n hn) (hopen n)
    by_cases hyO : ∃ n, y ∈ O n
    · obtain ⟨n, hn⟩ := hyO
      have hnΨ : n ∈ Ψ := by
        by_contra hnΨ
        exact ((hY Ψ y).1 hy).2 n hnΨ hn
      exact subset_closure (hOint n hnΨ hn)
    rw [not_exists] at hyO
    by_cases hycl : y ∈ closure (⋃ n ∈ Ψ₀, O n)
    · refine closure_mono ?_ hycl
      intro z hz
      obtain ⟨n, hn, hzn⟩ := mem_iUnion₂.1 hz
      exact hOint n (hΨ hn) hzn
    · have hnot : ¬ ∀ U : Set X, IsOpen U → y ∈ U → {n | (O n ∩ U).Nonempty}.Infinite :=
        fun hall => hycl (hΨ₀ y hall)
      push Not at hnot
      obtain ⟨U, hU, hyU, hUfin⟩ := hnot
      let F : Finset ℕ := hUfin.toFinset
      have hAF := hfin F
      have hyAF : y ∈ A \ ⋃ n ∈ F, O n := by
        refine ⟨((hY Ψ y).1 hy).1, fun hyu => ?_⟩
        obtain ⟨n, -, hyn⟩ := mem_iUnion₂.1 hyu
        exact hyO n hyn
      have hsubY : interior (A \ ⋃ n ∈ F, O n) ∩ U ⊆ interior (Y Ψ) := by
        apply interior_maximal _ (isOpen_interior.inter hU)
        rintro z ⟨hz1, hzU⟩
        have hz := interior_subset hz1
        rw [hY]
        refine ⟨hz.1, fun m _ hzm => hz.2 ?_⟩
        have hmF : m ∈ F := by
          rw [Set.Finite.mem_toFinset]
          exact ⟨z, hzm, hzU⟩
        exact mem_iUnion₂.2 ⟨m, hmF, hzm⟩
      have hycl' : y ∈ closure (interior (A \ ⋃ n ∈ F, O n)) := by
        rw [hAF.isRegularClosed.eq]; exact hyAF
      rw [mem_closure_iff]
      intro o ho hyo
      obtain ⟨z, ⟨hzo, hzU⟩, hzint⟩ :=
        mem_closure_iff.1 hycl' (o ∩ U) (ho.inter hU) ⟨hyo, hyU⟩
      exact ⟨z, hzo, hsubY ⟨hzint, hzU⟩⟩
  -- continuum many choices
  let e : ℕ → ℕ := fun n => (hΨ₀inf.natEmbedding _ n : ℕ)
  have he_inj : Injective e := fun a c h =>
    (hΨ₀inf.natEmbedding _).injective (Subtype.ext h)
  have he_mem : ∀ n, e n ∉ Ψ₀ := fun n => (hΨ₀inf.natEmbedding _ n).2
  let F : Set ℕ → Set X := fun T => Y (Ψ₀ ∪ e '' T)
  have hF : ∀ T, IsRegSubcontinuum (F T) := fun T =>
    isRegSubcontinuum_of_isClosed (hclosed _) (hconn _) (hreg _ subset_union_left)
  have hmem : ∀ T n, O (e n) ⊆ F T ↔ n ∈ T := by
    intro T n
    constructor
    · intro hsubF
      by_contra hn
      obtain ⟨z, hz⟩ := hne (e n)
      have hzF := hsubF hz
      refine ((hY _ z).1 hzF).2 (e n) ?_ hz
      rintro (h | ⟨m, hm, hme⟩)
      · exact he_mem n h
      · exact hn (he_inj hme ▸ hm)
    · intro hn
      exact hOY _ (e n) (Or.inr ⟨n, hn, rfl⟩)
  apply card_regular_eq_continuum hF
  intro T T' hTT'
  ext n
  rw [← hmem T n, ← hmem T' n]
  show O (e n) ⊆ F T ↔ O (e n) ⊆ F T'
  rw [show F T = F T' from hTT']

end Card

end RegularSubcontinua
