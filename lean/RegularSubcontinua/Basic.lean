module

public import RegularSubcontinua.Defs
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.NhdsSet

@[expose] public section

/-!
# Regular closed sets, relatively clopen sets, connectedness by closed separations
-/

open Set Function TopologicalSpace Topology

namespace RegularSubcontinua

variable {X : Type*} [TopologicalSpace X]

/-! ### Regular closed sets -/

theorem IsRegularClosed.eq {s : Set X} (h : IsRegularClosed s) : closure (interior s) = s := h

theorem IsRegularClosed.isClosed {s : Set X} (h : IsRegularClosed s) : IsClosed s := by
  have := isClosed_closure (s := interior s)
  rwa [h.eq] at this

theorem isRegularClosed_empty : IsRegularClosed (∅ : Set X) := by
  simp [IsRegularClosed]

theorem isRegularClosed_univ : IsRegularClosed (univ : Set X) := by
  simp [IsRegularClosed]

theorem isRegularClosed_closure_of_isOpen {U : Set X} (hU : IsOpen U) :
    IsRegularClosed (closure U) := by
  apply Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · exact closure_mono (interior_maximal subset_closure hU)

theorem IsRegularClosed.subset_closure_interior_of_subset {s t : Set X} (hs : IsRegularClosed s)
    (hst : s ⊆ t) : s ⊆ closure (interior t) := by
  calc s = closure (interior s) := hs.eq.symm
    _ ⊆ closure (interior t) := closure_mono (interior_mono hst)

theorem isRegularClosed_closure_sUnion {S : Set (Set X)} (h : ∀ s ∈ S, IsRegularClosed s) :
    IsRegularClosed (closure (⋃₀ S)) := by
  apply Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · apply closure_minimal _ isClosed_closure
    rintro x ⟨s, hs, hx⟩
    exact (h s hs).subset_closure_interior_of_subset
      ((subset_sUnion_of_mem hs).trans subset_closure) hx

theorem isRegularClosed_closure_iUnion {ι : Sort*} {s : ι → Set X}
    (h : ∀ i, IsRegularClosed (s i)) : IsRegularClosed (closure (⋃ i, s i)) := by
  apply Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · apply closure_minimal _ isClosed_closure
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    exact (h i).subset_closure_interior_of_subset
      ((subset_iUnion s i).trans subset_closure) hi

theorem IsRegularClosed.union {s t : Set X} (hs : IsRegularClosed s) (ht : IsRegularClosed t) :
    IsRegularClosed (s ∪ t) := by
  have hc : IsClosed (s ∪ t) := hs.isClosed.union ht.isClosed
  apply Subset.antisymm (closure_minimal interior_subset hc)
  rintro x (hx | hx)
  · exact hs.subset_closure_interior_of_subset subset_union_left hx
  · exact ht.subset_closure_interior_of_subset subset_union_right hx

theorem isRegularClosed_sUnion_of_finite {S : Set (Set X)} (hS : S.Finite)
    (h : ∀ s ∈ S, IsRegularClosed s) : IsRegularClosed (⋃₀ S) := by
  have hc : IsClosed (⋃₀ S) := hS.isClosed_sUnion fun s hs => (h s hs).isClosed
  have := isRegularClosed_closure_sUnion h
  rwa [hc.closure_eq] at this

/-- An open set meeting a regular closed set meets its interior. -/
theorem IsRegularClosed.inter_interior_nonempty {s U : Set X} (hs : IsRegularClosed s)
    (hU : IsOpen U) (h : (s ∩ U).Nonempty) : (interior s ∩ U).Nonempty := by
  obtain ⟨x, hxs, hxU⟩ := h
  rw [← hs.eq] at hxs
  have := mem_closure_iff.1 hxs U hU hxU
  rwa [inter_comm] at this

theorem IsRegularClosed.interior_nonempty {s : Set X} (hs : IsRegularClosed s)
    (h : s.Nonempty) : (interior s).Nonempty := by
  have := hs.inter_interior_nonempty isOpen_univ (by simpa using h)
  simpa using this

/-- If the interior of `s` misses the regular closed set `t`... more precisely: an open set that
misses the interior of a regular closed set misses the set. -/
theorem IsRegularClosed.disjoint_of_disjoint_interior {s U : Set X} (hs : IsRegularClosed s)
    (hU : IsOpen U) (h : Disjoint U (interior s)) : Disjoint U s := by
  rw [Set.disjoint_iff_inter_eq_empty] at h ⊢
  by_contra hne
  have hne' : (s ∩ U).Nonempty := by
    rw [inter_comm]; exact nonempty_iff_ne_empty.2 hne
  obtain ⟨y, hy1, hy2⟩ := hs.inter_interior_nonempty hU hne'
  have : y ∈ U ∩ interior s := ⟨hy2, hy1⟩
  rw [h] at this
  exact this

/-! ### Regular subcontinua -/

theorem IsRegSubcontinuum.isCompact {A : Set X} (h : IsRegSubcontinuum A) : IsCompact A := h.1
theorem IsRegSubcontinuum.isConnected {A : Set X} (h : IsRegSubcontinuum A) : IsConnected A := h.2.1
theorem IsRegSubcontinuum.isRegularClosed {A : Set X} (h : IsRegSubcontinuum A) :
    IsRegularClosed A := h.2.2
theorem IsRegSubcontinuum.isClosed {A : Set X} (h : IsRegSubcontinuum A) : IsClosed A :=
  h.isRegularClosed.isClosed
theorem IsRegSubcontinuum.nonempty {A : Set X} (h : IsRegSubcontinuum A) : A.Nonempty :=
  h.isConnected.nonempty
theorem IsRegSubcontinuum.isPreconnected {A : Set X} (h : IsRegSubcontinuum A) :
    IsPreconnected A := h.isConnected.isPreconnected
theorem IsRegSubcontinuum.interior_nonempty {A : Set X} (h : IsRegSubcontinuum A) :
    (interior A).Nonempty := h.isRegularClosed.interior_nonempty h.nonempty

theorem isRegSubcontinuum_of_isClosed [CompactSpace X] {A : Set X} (hc : IsClosed A)
    (hconn : IsConnected A) (hr : IsRegularClosed A) : IsRegSubcontinuum A :=
  ⟨hc.isCompact, hconn, hr⟩

theorem isRegSubcontinuum_univ [CompactSpace X] [ConnectedSpace X] :
    IsRegSubcontinuum (univ : Set X) :=
  ⟨isCompact_univ, isConnected_univ, isRegularClosed_univ⟩

theorem IsRegSubcontinuum.union {A B : Set X} (hA : IsRegSubcontinuum A)
    (hB : IsRegSubcontinuum B) (h : (A ∩ B).Nonempty) : IsRegSubcontinuum (A ∪ B) :=
  ⟨hA.isCompact.union hB.isCompact, hA.isConnected.union h hB.isConnected,
    hA.isRegularClosed.union hB.isRegularClosed⟩

/-! ### Closed separations -/

theorem _root_.IsPreconnected.subset_or_subset_of_closed {s u v : Set X} (hs : IsPreconnected s)
    (hu : IsClosed u) (hv : IsClosed v) (hsuv : s ⊆ u ∪ v) (hd : Disjoint u v) :
    s ⊆ u ∨ s ⊆ v :=
  isPreconnected_iff_subset_of_disjoint_closed.1 hs u v hu hv hsuv
    (by rw [hd.inter_eq, inter_empty])

theorem isPreconnected_of_closed_sep {s : Set X} (hs : IsClosed s)
    (h : ∀ u v : Set X, IsClosed u → IsClosed v → u ∪ v = s → Disjoint u v → u = ∅ ∨ v = ∅) :
    IsPreconnected s := by
  rw [isPreconnected_closed_iff]
  rintro t t' ht ht' hsub ⟨x, hxs, hxt⟩ ⟨y, hys, hyt'⟩
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hd : Disjoint (s ∩ t) (s ∩ t') := by
    rw [Set.disjoint_left]
    rintro z ⟨hz, hzt⟩ ⟨_, hzt'⟩
    have : z ∈ s ∩ (t ∩ t') := ⟨hz, hzt, hzt'⟩
    rw [hne] at this
    exact this
  have hun : (s ∩ t) ∪ (s ∩ t') = s := by
    ext z
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hz
      rcases hsub hz with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  rcases h _ _ (hs.inter ht) (hs.inter ht') hun hd with h1 | h1
  · have : x ∈ s ∩ t := ⟨hxs, hxt⟩
    rw [h1] at this
    exact this
  · have : y ∈ s ∩ t' := ⟨hys, hyt'⟩
    rw [h1] at this
    exact this

/-- A closed set that is not preconnected splits into two disjoint nonempty closed sets. -/
theorem exists_closed_sep_of_not_isPreconnected {s : Set X} (hs : IsClosed s)
    (h : ¬ IsPreconnected s) :
    ∃ u v : Set X, IsClosed u ∧ IsClosed v ∧ u ∪ v = s ∧ Disjoint u v ∧ u.Nonempty ∧
      v.Nonempty := by
  by_contra hcon
  apply h
  apply isPreconnected_of_closed_sep hs
  intro u v hu hv huv hd
  by_contra hne
  rw [not_or] at hne
  exact hcon ⟨u, v, hu, hv, huv, hd, nonempty_iff_ne_empty.2 hne.1,
    nonempty_iff_ne_empty.2 hne.2⟩

/-- The intersection of a decreasing sequence of compact preconnected sets is preconnected. -/
theorem isPreconnected_iInter_of_antitone [T2Space X] {B : ℕ → Set X} (hanti : Antitone B)
    (hc : ∀ n, IsCompact (B n)) (hconn : ∀ n, IsPreconnected (B n)) :
    IsPreconnected (⋂ n, B n) := by
  have hcl : IsClosed (⋂ n, B n) := isClosed_iInter fun n => (hc n).isClosed
  apply isPreconnected_of_closed_sep hcl
  intro u v hu hv huv hd
  by_contra hne
  rw [not_or] at hne
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := And.intro (nonempty_iff_ne_empty.2 hne.1)
    (nonempty_iff_ne_empty.2 hne.2)
  have hsub0 : ⋂ n, B n ⊆ B 0 := iInter_subset _ 0
  have huK : u ⊆ ⋂ n, B n := huv ▸ subset_union_left
  have hvK : v ⊆ ⋂ n, B n := huv ▸ subset_union_right
  have huc : IsCompact u := (hc 0).of_isClosed_subset hu (huK.trans hsub0)
  have hvc : IsCompact v := (hc 0).of_isClosed_subset hv (hvK.trans hsub0)
  obtain ⟨U, V, hU, hV, huU, hvV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact huc hvc hd
  have hdir : Directed (· ⊇ ·) B := fun i j =>
    ⟨max i j, hanti (le_max_left i j), hanti (le_max_right i j)⟩
  have hnhds : U ∪ V ∈ 𝓝ˢ (⋂ n, B n) := by
    rw [(hU.union hV).mem_nhdsSet, ← huv]
    exact union_subset_union huU hvV
  obtain ⟨i, hi⟩ := exists_subset_nhds_of_isCompact' hdir hc (fun n => (hc n).isClosed) hnhds
  have hKi : ⋂ n, B n ⊆ B i := iInter_subset _ i
  rcases (hconn i).subset_or_subset hU hV hUV hi with h | h
  · exact Set.disjoint_left.1 hUV (h (hKi (hvK hb))) (hvV hb)
  · exact Set.disjoint_left.1 hUV (huU ha) (h (hKi (huK ha)))

/-! ### Relatively clopen subsets of a closed set -/

/-- `V` is a relatively clopen subset of `R` (intended for closed `R`). -/
structure IsRelClopen (R V : Set X) : Prop where
  subset : V ⊆ R
  isClosed : IsClosed V
  isClosed_diff : IsClosed (R \ V)

theorem isRelClopen_self {R : Set X} (hR : IsClosed R) : IsRelClopen R R :=
  ⟨Subset.rfl, hR, by simp⟩

theorem isRelClopen_empty {R : Set X} (hR : IsClosed R) : IsRelClopen R ∅ :=
  ⟨empty_subset _, isClosed_empty, by simpa using hR⟩

theorem IsRelClopen.trans {R S V : Set X} (hS : IsRelClopen R S) (hV : IsRelClopen S V) :
    IsRelClopen R V := by
  refine ⟨hV.subset.trans hS.subset, hV.isClosed, ?_⟩
  have : R \ V = (R \ S) ∪ (S \ V) := by
    ext z
    constructor
    · rintro ⟨hz, hzV⟩
      by_cases hzS : z ∈ S
      · exact Or.inr ⟨hzS, hzV⟩
      · exact Or.inl ⟨hz, hzS⟩
    · rintro (⟨hz, hzS⟩ | ⟨hz, hzV⟩)
      · exact ⟨hz, fun h => hzS (hV.subset h)⟩
      · exact ⟨hS.subset hz, hzV⟩
  rw [this]
  exact hS.isClosed_diff.union hV.isClosed_diff

/-- A relatively clopen subset of a regular closed set is regular closed. -/
theorem IsRelClopen.isRegularClosed {R V : Set X} (h : IsRelClopen R V)
    (hR : IsRegularClosed R) : IsRegularClosed V := by
  apply Subset.antisymm (closure_minimal interior_subset h.isClosed)
  intro x hx
  have hW : IsOpen (R \ V)ᶜ := h.isClosed_diff.isOpen_compl
  have hxW : x ∈ (R \ V)ᶜ := fun hx' => hx'.2 hx
  have hxR : x ∈ closure (interior R) := by
    rw [hR.eq]
    exact h.subset hx
  have hsub : interior R ∩ (R \ V)ᶜ ⊆ interior V := by
    apply interior_maximal _ (isOpen_interior.inter hW)
    rintro y ⟨hy1, hy2⟩
    by_contra hyV
    exact hy2 ⟨interior_subset hy1, hyV⟩
  rw [mem_closure_iff]
  intro o ho hxo
  obtain ⟨y, ⟨hyo, hyW⟩, hyR⟩ :=
    mem_closure_iff.1 hxR (o ∩ (R \ V)ᶜ) (ho.inter hW) ⟨hxo, hxW⟩
  exact ⟨y, hyo, hsub ⟨hyR, hyW⟩⟩

/-- A nonempty relatively clopen subset of `closure O`, `O` open, meets `O`. -/
theorem IsRelClopen.inter_nonempty_of_closure {O V : Set X} (h : IsRelClopen (closure O) V)
    (hne : V.Nonempty) : (V ∩ O).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  have hW : IsOpen (closure O \ V)ᶜ := h.isClosed_diff.isOpen_compl
  have hxW : x ∈ (closure O \ V)ᶜ := fun hx' => hx'.2 hx
  obtain ⟨y, hyW, hyO⟩ := mem_closure_iff.1 (h.subset hx) _ hW hxW
  refine ⟨y, ?_, hyO⟩
  by_contra hyV
  exact hyW ⟨subset_closure hyO, hyV⟩

/-- A preconnected subset of `R` that meets a relatively clopen set lies inside it. -/
theorem IsRelClopen.subset_of_isPreconnected {R V s : Set X} (h : IsRelClopen R V)
    (hs : IsPreconnected s) (hsR : s ⊆ R) (hne : (s ∩ V).Nonempty) : s ⊆ V := by
  have hsub : s ⊆ V ∪ (R \ V) := fun y hy => by
    by_cases hyV : y ∈ V
    · exact Or.inl hyV
    · exact Or.inr ⟨hsR hy, hyV⟩
  rcases hs.subset_or_subset_of_closed h.isClosed h.isClosed_diff hsub
    disjoint_sdiff_self_right with h1 | h1
  · exact h1
  · obtain ⟨x, hxs, hxV⟩ := hne
    exact absurd hxV (h1 hxs).2

theorem connectedComponentIn_eq_of_isRelClopen {R C : Set X} {x : X} (hC : IsRelClopen R C)
    (hCc : IsConnected C) (hx : x ∈ C) : connectedComponentIn R x = C := by
  apply Subset.antisymm
  · exact hC.subset_of_isPreconnected isPreconnected_connectedComponentIn
      (connectedComponentIn_subset R x) ⟨x, mem_connectedComponentIn (hC.subset hx), hx⟩
  · exact hCc.isPreconnected.subset_connectedComponentIn hx hC.subset

/-! ### Finitely many components, or infinitely many disjoint clopen pieces -/

/-- `S` is a finite union of connected relatively clopen subsets of `R`. -/
def FinClopenCover (R S : Set X) : Prop :=
  ∃ 𝒞 : Set (Set X), 𝒞.Finite ∧ (∀ C ∈ 𝒞, IsConnected C ∧ IsRelClopen R C) ∧ ⋃₀ 𝒞 = S

theorem exists_split {R S : Set X} (hS : IsRelClopen R S) (hn : ¬ FinClopenCover R S) :
    ∃ S' V : Set X, IsRelClopen R S' ∧ ¬ FinClopenCover R S' ∧ S' ⊆ S ∧ IsRelClopen R V ∧
      V.Nonempty ∧ V ⊆ S ∧ Disjoint S' V := by
  have hne : S.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    exact hn ⟨∅, finite_empty, by simp, by simp [h]⟩
  have hnp : ¬ IsPreconnected S := fun hp =>
    hn ⟨{S}, finite_singleton S, by
      intro C hC
      rw [mem_singleton_iff] at hC
      subst hC
      exact ⟨⟨hne, hp⟩, hS⟩, by simp⟩
  obtain ⟨u, v, hu, hv, huv, hd, hune, hvne⟩ :=
    exists_closed_sep_of_not_isPreconnected hS.isClosed hnp
  have hSu : S \ u = v := by
    ext z
    constructor
    · rintro ⟨hz, hzu⟩
      rw [← huv] at hz
      exact hz.resolve_left hzu
    · intro hz
      exact ⟨huv ▸ Or.inr hz, fun hzu => Set.disjoint_left.1 hd hzu hz⟩
  have hSv : S \ v = u := by
    ext z
    constructor
    · rintro ⟨hz, hzv⟩
      rw [← huv] at hz
      exact hz.resolve_right hzv
    · intro hz
      exact ⟨huv ▸ Or.inl hz, fun hzv => Set.disjoint_left.1 hd hz hzv⟩
  have huS : u ⊆ S := huv ▸ subset_union_left
  have hvS : v ⊆ S := huv ▸ subset_union_right
  have hRu : IsRelClopen R u := hS.trans ⟨huS, hu, by rw [hSu]; exact hv⟩
  have hRv : IsRelClopen R v := hS.trans ⟨hvS, hv, by rw [hSv]; exact hu⟩
  by_cases hcu : FinClopenCover R u
  · have hcv : ¬ FinClopenCover R v := by
      intro hcv
      obtain ⟨𝒞u, hfu, h1u, h2u⟩ := hcu
      obtain ⟨𝒞v, hfv, h1v, h2v⟩ := hcv
      refine hn ⟨𝒞u ∪ 𝒞v, hfu.union hfv, ?_, ?_⟩
      · rintro C (hC | hC)
        · exact h1u C hC
        · exact h1v C hC
      · rw [sUnion_union, h2u, h2v, huv]
    exact ⟨v, u, hRv, hcv, hvS, hRu, hune, huS, hd.symm⟩
  · exact ⟨u, v, hRu, hcu, huS, hRv, hvne, hvS, hd⟩

theorem finClopenCover_or_seq {R : Set X} (hR : IsClosed R) :
    FinClopenCover R R ∨ ∃ V : ℕ → Set X, (∀ n, (V n).Nonempty ∧ IsRelClopen R (V n)) ∧
      Pairwise (Disjoint on V) := by
  by_cases h : FinClopenCover R R
  · exact Or.inl h
  right
  let T := {S : Set X // IsRelClopen R S ∧ ¬ FinClopenCover R S}
  have step : ∀ t : T, ∃ p : T × Set X, p.1.1 ⊆ t.1 ∧ IsRelClopen R p.2 ∧ p.2.Nonempty ∧
      p.2 ⊆ t.1 ∧ Disjoint p.1.1 p.2 := by
    rintro ⟨S, hS, hn⟩
    obtain ⟨S', V, h1, h2, h3, h4, h5, h6, h7⟩ := exists_split hS hn
    exact ⟨(⟨S', h1, h2⟩, V), h3, h4, h5, h6, h7⟩
  choose f hf using step
  let s : ℕ → T := fun n => Nat.rec (⟨R, isRelClopen_self hR, h⟩ : T) (fun _ t => (f t).1) n
  have hs_succ : ∀ n, s (n + 1) = (f (s n)).1 := fun n => rfl
  have hanti : Antitone fun n => (s n).1 := by
    apply antitone_nat_of_succ_le
    intro n
    show (s (n + 1)).1 ⊆ (s n).1
    rw [hs_succ]
    exact (hf (s n)).1
  refine ⟨fun n => (f (s n)).2, fun n => ⟨(hf (s n)).2.2.1, (hf (s n)).2.1⟩, ?_⟩
  have key : ∀ n m, n < m → Disjoint (f (s n)).2 (f (s m)).2 := by
    intro n m hnm
    have h1 : (f (s m)).2 ⊆ (s (n + 1)).1 :=
      ((hf (s m)).2.2.2.1).trans (hanti (Nat.succ_le_of_lt hnm))
    have h2 : Disjoint (s (n + 1)).1 (f (s n)).2 := by
      rw [hs_succ]
      exact (hf (s n)).2.2.2.2
    exact (h2.mono_left h1).symm
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem sUnion_components (R : Set X) : ⋃₀ components R = R := by
  apply Subset.antisymm
  · rintro x ⟨C, ⟨y, _, rfl⟩, hx⟩
    exact connectedComponentIn_subset R y hx
  · intro x hx
    exact ⟨connectedComponentIn R x, ⟨x, hx, rfl⟩, mem_connectedComponentIn hx⟩

theorem FinClopenCover.components_spec {R : Set X} (h : FinClopenCover R R) :
    (components R).Finite ∧ ∀ C ∈ components R, IsConnected C ∧ IsRelClopen R C := by
  obtain ⟨𝒞, hfin, h𝒞, hU⟩ := h
  have key : ∀ x ∈ R, connectedComponentIn R x ∈ 𝒞 := by
    intro x hx
    rw [← hU] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    rw [connectedComponentIn_eq_of_isRelClopen (h𝒞 C hC).2 (h𝒞 C hC).1 hxC]
    exact hC
  have hsub : components R ⊆ 𝒞 := by
    rintro C ⟨x, hx, rfl⟩
    exact key x hx
  exact ⟨hfin.subset hsub, fun C hC => h𝒞 C (hsub hC)⟩

end RegularSubcontinua
