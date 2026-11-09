import PL1.DaugavetAveraging
import PL1.IntrinsicWalshBlocks

/-! # The actual dense increasing finite-coordinate intrinsic ranges -/

noncomputable section
open Filter MeasureTheory
open scoped NNReal Topology

namespace PL1.Noise

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

theorem intrinsicExpectation_range_monotone :
    Monotone (fun n => (intrinsicExpectation K rates n).range) := by
  intro m n hmn x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨intrinsicExpectation K rates m y, ?_⟩
  change ((intrinsicExpectation K rates n).comp (intrinsicExpectation K rates m)) y = _
  rw [intrinsicExpectation_comp_min, min_eq_right hmn]
  rfl

theorem dense_iUnion_intrinsicExpectation_range :
    Dense (⋃ n, ((intrinsicExpectation K rates n).range : Set (dyadicSystem K rates).IntrinsicSpace)) := by
  intro x
  apply isClosed_closure.mem_of_tendsto (tendsto_intrinsicExpectation K rates x)
  exact Eventually.of_forall (fun n => subset_closure (Set.mem_iUnion.mpr ⟨n, ⟨x, rfl⟩⟩))

theorem intrinsicSpace_nontrivial : Nontrivial (dyadicSystem K rates).IntrinsicSpace :=
  ⟨⟨intrinsicCharacter K rates ∅, 0, (linearIndependent_intrinsicCharacter K rates).ne_zero ∅⟩⟩

theorem intrinsic_sliceCriterion_of_finiteSpikeFamilies
    (hspikes : Daugavet.FiniteSpikeFamilies K (dyadicSystem K rates).IntrinsicSpace
      (fun n => (intrinsicExpectation K rates n).range)) :
    Daugavet.SliceCriterion K (dyadicSystem K rates).IntrinsicSpace :=
  Daugavet.sliceCriterion_of_finiteSpikeFamilies _
    (intrinsicExpectation_range_monotone K rates)
    (dense_iUnion_intrinsicExpectation_range K rates) hspikes

theorem intrinsic_hasDaugavetProperty_of_finiteSpikeFamilies
    (hspikes : Daugavet.FiniteSpikeFamilies K (dyadicSystem K rates).IntrinsicSpace
      (fun n => (intrinsicExpectation K rates n).range)) :
    Daugavet.HasDaugavetProperty K (dyadicSystem K rates).IntrinsicSpace := by
  let := intrinsicSpace_nontrivial K rates
  exact (intrinsic_sliceCriterion_of_finiteSpikeFamilies K rates hspikes).hasDaugavetProperty

end PL1.Noise
