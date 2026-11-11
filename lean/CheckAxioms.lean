module

public import Solution

@[expose] public section

/-! Run `lake env lean CheckAxioms.lean` to list the axioms used by every compared theorem.
Each line should report only `propext`, `Classical.choice` and `Quot.sound`. -/

#print axioms RegularSubcontinua.isRegSubcontinuum_iff_exists_mem_regular
#print axioms RegularSubcontinua.card_eq_continuum_of_independent
#print axioms RegularSubcontinua.card_eq_continuum_of_blisters
#print axioms RegularSubcontinua.complement_lemma
#print axioms RegularSubcontinua.isFiniteUnion_operations
#print axioms RegularSubcontinua.components_of_isFiniteUnion
#print axioms RegularSubcontinua.absorption
#print axioms RegularSubcontinua.minimal_disjoint_interior
#print axioms RegularSubcontinua.decreasing_intersection
#print axioms RegularSubcontinua.dense_interior_minimal
#print axioms RegularSubcontinua.atomicFamily_basic
#print axioms RegularSubcontinua.atomicFamily_coding
#print axioms RegularSubcontinua.atomicFamily_open_of_mem
#print axioms RegularSubcontinua.atomicFamily_discrete
#print axioms RegularSubcontinua.isGdelta_regular_of_isDAtomic
#print axioms RegularSubcontinua.structure_theorem
#print axioms RegularSubcontinua.main_theorem
#print axioms RegularSubcontinua.not_homeomorphic_rat
#print axioms RegularSubcontinua.no_continuum_with_regular_hyperspace_rat
#print axioms RegularSubcontinua.dichotomy
#print axioms RegularSubcontinua.no_rational_chain
#print axioms RegularSubcontinua.dichotomy_exclusive
#print axioms RegularSubcontinua.countable_hypothesis_satisfiable
