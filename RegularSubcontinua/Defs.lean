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
# Definitions

These are the definitions of `Challenge.lean`, verbatim. Comparator checks that the two copies agree.
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

end RegularSubcontinua
