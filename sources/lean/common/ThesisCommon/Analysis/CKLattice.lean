import ThesisCommon.Analysis.BanachLattice

noncomputable section
universe u
namespace ThesisCommon
open scoped BoundedContinuousFunction

/-- Real bounded functions form a vector lattice with their usual pointwise order. -/
instance boundedFunctions_orderedModule (K : Type*) [TopologicalSpace K] :
    IsOrderedModule ℝ (K →ᵇ ℝ) where
  smul_le_smul_of_nonneg_left := by
    intro r hr f g h x
    exact mul_le_mul_of_nonneg_left (h x) hr
  smul_le_smul_of_nonneg_right := by
    intro f hf r s h x
    exact mul_le_mul_of_nonneg_right h (hf x)

/-- Every real C(K) is a Banach lattice. The bounded-continuous representation
is isometrically identified with C(K) by mathlib. -/
theorem ck_isomorphicToBanachLattice (K : Compactum.{u}) :
    IsomorphicToBanachLattice C(K, ℝ) := by
  refine ⟨{ Carrier := K →ᵇ ℝ
            lattice := inferInstance
            orderedAdd := inferInstance
            orderedModule := inferInstance
            solidNorm := inferInstance }, ?_⟩
  exact ⟨(ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ).toContinuousLinearEquiv⟩

/-- Isomorphism to a C(K) implies isomorphism to a Banach lattice, with no norm-equality assumption. -/
theorem isomorphicToCK_implies_lattice {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (h : IsomorphicToCK E) : IsomorphicToBanachLattice E := by
  rcases h with ⟨K, ⟨e⟩⟩
  rcases ck_isomorphicToBanachLattice K with ⟨F, ⟨f⟩⟩
  exact ⟨F, ⟨e.trans f⟩⟩

end ThesisCommon
