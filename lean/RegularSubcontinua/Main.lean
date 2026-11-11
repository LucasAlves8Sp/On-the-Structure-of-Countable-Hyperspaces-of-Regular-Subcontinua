module

public import RegularSubcontinua.Atomic
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Analysis.Real.Cardinality

@[expose] public section

/-!
# The main theorem

Theorem 1.4 (structure theorem), Theorem 1.2 (main theorem) and Proposition 7.5.
-/

open Set Function TopologicalSpace Topology
open scoped Cardinal

universe u

namespace RegularSubcontinua

/-! ### General topology used in the last step -/

section General

/-- A `G_δ` subset of a Polish space is Polish. -/
theorem polishSpace_of_isGδ {Y : Type*} [TopologicalSpace Y] [PolishSpace Y] {s : Set Y}
    (hs : IsGδ s) : PolishSpace s := by
  obtain ⟨U, hU, rfl⟩ := isGδ_iff_eq_iInter_nat.1 hs
  have : ∀ n, PolishSpace (U n) := fun n => (hU n).polishSpace
  let e : ↥(⋂ n, U n) → (∀ n, ↥(U n)) := fun x n => ⟨x.1, mem_iInter.1 x.2 n⟩
  have hcont : Continuous e :=
    continuous_pi fun n => Continuous.subtype_mk continuous_subtype_val _
  have hg : Continuous fun f : (∀ n, ↥(U n)) => (f 0 : Y) :=
    continuous_subtype_val.comp (continuous_apply 0)
  have hemb : IsEmbedding e :=
    IsEmbedding.of_comp hcont hg (IsEmbedding.subtypeVal : IsEmbedding
      (Subtype.val : ↥(⋂ n, U n) → Y))
  have hrange : range e = ⋂ n, {f : (∀ n, ↥(U n)) | (f n : Y) = (f 0 : Y)} := by
    ext f
    simp only [mem_range, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro ⟨x, rfl⟩ n
      rfl
    · intro hf
      refine ⟨⟨(f 0 : Y), mem_iInter.2 fun n => ?_⟩, ?_⟩
      · rw [← hf n]
        exact (f n).2
      · funext n
        exact Subtype.ext (hf n).symm
  have hclosed : IsClosed (range e) := by
    rw [hrange]
    exact isClosed_iInter fun n => isClosed_eq
      (continuous_subtype_val.comp (continuous_apply n))
      (continuous_subtype_val.comp (continuous_apply 0))
  exact (IsClosedEmbedding.mk hemb hclosed).polishSpace

/-- A countable completely metrizable space is scattered. -/
theorem isScattered_of_countable {Y : Type*} [TopologicalSpace Y]
    [IsCompletelyMetrizableSpace Y] [Countable Y] : IsScattered Y := by
  intro S hS
  have : IsCompletelyMetrizableSpace ↥(closure S) :=
    isClosed_closure.isCompletelyMetrizableSpace
  have : Nonempty ↥(closure S) := ⟨⟨hS.some, subset_closure hS.some_mem⟩⟩
  have hcov : (⋃ t : ↥(closure S), ({t} : Set ↥(closure S))) = univ := by
    ext t
    simp
  obtain ⟨t, z, hz⟩ := nonempty_interior_of_iUnion_of_closed
    (fun t : ↥(closure S) => isClosed_singleton (x := t)) hcov
  have hzt : z = t := mem_singleton_iff.1 (interior_subset hz)
  subst hzt
  have hopen : IsOpen ({z} : Set ↥(closure S)) := by
    have h1 : interior ({z} : Set ↥(closure S)) = {z} :=
      Subset.antisymm interior_subset (singleton_subset_iff.2 hz)
    rw [← h1]
    exact isOpen_interior
  obtain ⟨U, hU, hUt⟩ := isOpen_induced_iff.1 hopen
  have htU : z.1 ∈ U := by
    have h2 : z ∈ Subtype.val ⁻¹' U := by rw [hUt]; rfl
    exact h2
  have hUS : ∀ y ∈ U ∩ S, y = z.1 := by
    rintro y ⟨hyU, hyS⟩
    have h2 : (⟨y, subset_closure hyS⟩ : ↥(closure S)) ∈ Subtype.val ⁻¹' U := hyU
    rw [hUt] at h2
    exact congrArg Subtype.val h2
  obtain ⟨y, hyU, hyS⟩ := mem_closure_iff.1 z.2 U hU htU
  have hy := hUS y ⟨hyU, hyS⟩
  have hzS : z.1 ∈ S := hy ▸ hyS
  refine ⟨z.1, hzS, U, hU, ?_⟩
  ext w
  constructor
  · intro hw
    exact hUS w hw
  · intro hw
    rw [mem_singleton_iff] at hw
    rw [hw]
    exact ⟨htU, hzS⟩

/-- In a scattered space the isolated points are dense. -/
theorem IsScattered.dense_isolated {Y : Type*} [TopologicalSpace Y] (h : IsScattered Y) :
    Dense {y : Y | IsOpen ({y} : Set Y)} := by
  rw [dense_iff_inter_open]
  intro V hV hVne
  obtain ⟨x, hxV, U, hU, hUV⟩ := h V hVne
  refine ⟨x, hxV, ?_⟩
  show IsOpen ({x} : Set Y)
  rw [← hUV]
  exact hU.inter hV

/-- No point of `ℚ` is isolated. -/
theorem not_isOpen_singleton_rat (q : ℚ) : ¬ IsOpen ({q} : Set ℚ) := by
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 h q rfl
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have hposQ : (0 : ℚ) < 1 / ((n : ℚ) + 1) := by positivity
  have hmem : q + 1 / ((n : ℚ) + 1) ∈ Metric.ball q ε := by
    rw [Metric.mem_ball, Rat.dist_eq]
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hcast : ((q + 1 / ((n : ℚ) + 1) : ℚ) : ℝ) - (q : ℝ) = 1 / ((n : ℝ) + 1) := by
      push_cast
      ring
    rw [hcast, abs_of_pos hpos]
    exact hn
  have h2 := hball hmem
  rw [mem_singleton_iff] at h2
  linarith

end General

variable {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-! ### `C(X)` is closed in the hyperspace of compact sets -/

theorem isClosed_setOf_isConnected :
    IsClosed {K : NonemptyCompacts X | IsConnected (K : Set X)} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro K hK
  have hKnp : ¬ IsPreconnected (K : Set X) := fun h => hK ⟨K.nonempty, h⟩
  obtain ⟨u, v, hu, hv, huv, hdisj, hune, hvne⟩ :=
    exists_closed_sep_of_not_isPreconnected K.isCompact.isClosed hKnp
  have huK : u ⊆ (K : Set X) := by rw [← huv]; exact subset_union_left
  have hvK : v ⊆ (K : Set X) := by rw [← huv]; exact subset_union_right
  have huc : IsCompact u := K.isCompact.of_isClosed_subset hu huK
  have hvc : IsCompact v := K.isCompact.of_isClosed_subset hv hvK
  obtain ⟨U, V, hU, hV, huU, hvV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact huc hvc hdisj
  refine ⟨({L : NonemptyCompacts X | (L : Set X) ⊆ U ∪ V} ∩
      {L : NonemptyCompacts X | ((L : Set X) ∩ U).Nonempty}) ∩
      {L : NonemptyCompacts X | ((L : Set X) ∩ V).Nonempty}, ?_, ?_, ?_⟩
  · rintro L ⟨⟨hLsub, hLU⟩, hLV⟩ hLconn
    have hLconn' : IsConnected (L : Set X) := hLconn
    obtain ⟨z, -, hzU, hzV⟩ := hLconn'.isPreconnected U V hU hV hLsub hLU hLV
    exact Set.disjoint_left.1 hUV hzU hzV
  · exact ((NonemptyCompacts.isOpen_subsets_of_isOpen (hU.union hV)).inter
      (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU)).inter
      (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hV)
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · show (K : Set X) ⊆ U ∪ V
      rw [← huv]
      exact union_subset_union huU hvV
    · obtain ⟨z, hz⟩ := hune
      exact ⟨z, huK hz, huU hz⟩
    · obtain ⟨z, hz⟩ := hvne
      exact ⟨z, hvK hz, hvV hz⟩

theorem polishSpace_subcontinua : PolishSpace (Subcontinua X) :=
  (isClosed_setOf_isConnected (X := X)).polishSpace

/-! ### Theorem 1.4 and Theorem 1.2 -/

/-- Under countability the minimal elements form an atomic family. -/
theorem isAtomicFamily_minimal (hcount : (regular X).Countable) :
    IsAtomicFamily {N : Set X | IsMinimalReg N} := by
  refine ⟨fun p hp => hp.1, fun A hA p hp h => ?_, dense_interior_minimal' hcount⟩
  rcases absorption' hcount hp hA with h1 | h1
  · exact h1
  · obtain ⟨z, hzA, hzp⟩ := h
    exact absurd hzA (Set.disjoint_left.1 h1 (interior_subset hzp))

theorem isDAtomic_of_countable (hcount : (regular X).Countable) : IsDAtomic X :=
  ⟨_, isAtomicFamily_minimal hcount⟩

/-- Theorem 1.4 (structure theorem). -/
theorem structure_theorem' (hcount : (regular X).Countable) :
    (∀ A N : Set X, IsRegSubcontinuum A → IsMinimalReg N →
      N ⊆ A ∨ Disjoint N (interior A)) ∧
    (∀ N N' : Set X, IsMinimalReg N → IsMinimalReg N' → N ≠ N' →
      Disjoint (interior N) (interior N')) ∧
    Dense (⋃ (N : Set X) (_ : IsMinimalReg N), interior N) ∧
    (∀ A : Set X, IsRegSubcontinuum A →
      A = closure (⋃₀ {N | IsMinimalReg N ∧ N ⊆ A}) ∧
      ∃ N : Set X, IsMinimalReg N ∧ N ⊆ A) := by
  have hP := isAtomicFamily_minimal hcount
  obtain ⟨h1, -, h3, -⟩ := atomicFamily_basic' hP
  refine ⟨fun A N hA hN => absorption' hcount hN hA,
    fun N N' hN hN' hne => h1 N hN N' hN' hne, dense_interior_minimal' hcount, fun A hA => ?_⟩
  obtain ⟨⟨p, hp, hpA⟩, heq⟩ := h3 A hA
  exact ⟨heq, p, hp, hpA⟩

/-- Theorem 1.2 (main theorem). -/
theorem main_theorem' (hcount : (regular X).Countable) :
    IsGδ (regular X) ∧ IsCompletelyMetrizableSpace ↥(regular X) ∧
    IsScattered ↥(regular X) ∧
    Dense {K : ↥(regular X) | IsOpen ({K} : Set ↥(regular X))} := by
  have hG : IsGδ (regular X) := isGδ_regular_of_isDAtomic' (isDAtomic_of_countable hcount)
  have : PolishSpace (Subcontinua X) := polishSpace_subcontinua
  have : PolishSpace ↥(regular X) := polishSpace_of_isGδ hG
  have : Countable ↥(regular X) := hcount.to_subtype
  have hsc : IsScattered ↥(regular X) := isScattered_of_countable
  exact ⟨hG, inferInstance, hsc, hsc.dense_isolated⟩

/-- Theorem 1.2, last assertion. -/
theorem not_homeomorphic_rat' : IsEmpty (↥(regular X) ≃ₜ ℚ) := by
  refine ⟨fun e => ?_⟩
  have hc : Countable ↥(regular X) := Countable.of_equiv ℚ e.symm.toEquiv
  have hcount : (regular X).Countable := Set.countable_coe_iff.1 hc
  obtain ⟨-, -, -, hd⟩ := main_theorem' hcount
  obtain ⟨K, -, hK⟩ := dense_iff_inter_open.1 hd univ isOpen_univ ⟨e.symm 0, trivial⟩
  have hK' : IsOpen ({K} : Set ↥(regular X)) := hK
  have h2 : IsOpen (e '' {K}) := e.isOpen_image.2 hK'
  rw [image_singleton] at h2
  exact not_isOpen_singleton_rat _ h2

/-! ### Proposition 7.5 -/

/-- Proposition 7.5: no chain of `D(X)` has the order type of `ℚ`. -/
theorem no_rational_chain' (hcount : (regular X).Countable) :
    ¬ ∃ f : ℚ → Set X, (∀ q, IsRegSubcontinuum (f q)) ∧ StrictMono f := by
  rintro ⟨f, hf, hmono⟩
  have hS : ∀ r : ℝ, IsRegSubcontinuum (closure (⋃₀ (f '' {q : ℚ | (q : ℝ) < r}))) := by
    intro r
    refine isRegSubcontinuum_of_isClosed isClosed_closure ?_ (isRegularClosed_closure_sUnion ?_)
    · have hpre : IsPreconnected (⋃₀ (f '' {q : ℚ | (q : ℝ) < r})) := by
        apply IsPreconnected.sUnion_directed
        · rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩
          refine ⟨f (max q q'), ⟨max q q', ?_, rfl⟩, hmono.monotone (le_max_left _ _),
            hmono.monotone (le_max_right _ _)⟩
          show ((max q q' : ℚ) : ℝ) < r
          rcases max_cases q q' with ⟨h, -⟩ | ⟨h, -⟩
          · rw [h]; exact hq
          · rw [h]; exact hq'
        · rintro _ ⟨q, -, rfl⟩
          exact (hf q).isPreconnected
      obtain ⟨q, hq⟩ := exists_rat_lt r
      obtain ⟨z, hz⟩ := (hf q).nonempty
      exact IsConnected.closure ⟨⟨z, f q, ⟨q, hq, rfl⟩, hz⟩, hpre⟩
    · rintro _ ⟨q, -, rfl⟩
      exact (hf q).isRegularClosed
  have hlt : ∀ r r' : ℝ, r < r' →
      closure (⋃₀ (f '' {q : ℚ | (q : ℝ) < r})) ≠ closure (⋃₀ (f '' {q : ℚ | (q : ℝ) < r'})) := by
    intro r r' hrr' h
    obtain ⟨q, hrq, hqr'⟩ := exists_rat_btwn hrr'
    obtain ⟨q', hqq', hq'r'⟩ := exists_rat_btwn hqr'
    have h1 : closure (⋃₀ (f '' {q : ℚ | (q : ℝ) < r})) ⊆ f q := by
      refine closure_minimal (sUnion_subset ?_) (hf q).isClosed
      rintro _ ⟨p, hp, rfl⟩
      have hp' : (p : ℝ) < r := hp
      exact hmono.monotone (by exact_mod_cast (hp'.trans hrq).le)
    have h2 : f q' ⊆ closure (⋃₀ (f '' {q : ℚ | (q : ℝ) < r'})) :=
      (subset_sUnion_of_mem (mem_image_of_mem f hq'r')).trans subset_closure
    have h3 : f q < f q' := hmono (by exact_mod_cast hqq')
    rw [← h] at h2
    exact absurd (show f q' ≤ f q from h2.trans h1) (not_le_of_gt h3)
  have hinj : Injective fun r : ℝ =>
      (⟨closure (⋃₀ (f '' {q : ℚ | (q : ℝ) < r})), hS r⟩ : ↥{A : Set X | IsRegSubcontinuum A}) := by
    intro r r' h
    have h' : closure (⋃₀ (f '' {q : ℚ | (q : ℝ) < r})) =
        closure (⋃₀ (f '' {q : ℚ | (q : ℝ) < r'})) := congrArg Subtype.val h
    rcases lt_trichotomy r r' with hlt' | heq | hgt
    · exact absurd h' (hlt r r' hlt')
    · exact heq
    · exact absurd h'.symm (hlt r' r hgt)
  have : Countable ↥{A : Set X | IsRegSubcontinuum A} :=
    (countable_setOf_isRegSubcontinuum hcount).to_subtype
  exact not_countable (α := ℝ) hinj.countable

/-! ### The countability hypothesis is satisfiable -/

/-- For the one-point space, `D(X)` is countable (it has one element). -/
theorem countable_regular_punit : (regular PUnit.{u + 1}).Countable := by
  apply Set.Subsingleton.countable
  intro K _ L _
  have key : ∀ M : Subcontinua PUnit.{u + 1}, (M.1 : Set PUnit.{u + 1}) = univ := by
    intro M
    obtain ⟨y, hy⟩ := M.1.nonempty
    exact eq_univ_of_forall fun x => Subsingleton.elim y x ▸ hy
  exact Subtype.ext (SetLike.coe_injective ((key K).trans (key L).symm))

/-- The one-point space is connected. -/
theorem connectedSpace_punit : ConnectedSpace PUnit.{u + 1} :=
  { toPreconnectedSpace := ⟨(Set.subsingleton_of_subsingleton).isPreconnected⟩
    toNonempty := ⟨PUnit.unit⟩ }

end RegularSubcontinua
