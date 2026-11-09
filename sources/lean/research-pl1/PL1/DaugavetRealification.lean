import PL1.MainDaugavet

/-! # Daugavet for all real rank-one operators on the same intrinsic norm

Finite spike families use real coefficients in their averages. They survive
restriction of scalars, so the real slice criterion tests the entire real
continuous dual, including functionals that are not complex linear.
-/

noncomputable section
open scoped NNReal BigOperators
namespace PL1.Daugavet

variable {K E : Type*} [RCLike K] [NormedAddCommGroup E]
  [NormedSpace K E] [NormedSpace ℝ E] [IsScalarTower ℝ K E]

/-- Restricting a finite spike family to real scalars preserves its exact averages and norms. -/
theorem FiniteSpikeFamilies.restrictScalars {V : ℕ → Submodule K E}
    (hspikes : FiniteSpikeFamilies K E V) :
    FiniteSpikeFamilies ℝ E (fun n => (V n).restrictScalars ℝ) := by
  intro n h hh f hf δ hδ η hη
  obtain ⟨N, hN, w, hav, hnorm, hsep⟩ := hspikes n h hh f hf δ hδ η hη
  refine ⟨N, hN, w, ?_, hnorm, hsep⟩
  rw [RCLike.real_smul_eq_coe_smul (K := K)]
  simpa only [RCLike.ofReal_inv, RCLike.ofReal_natCast] using hav

/-- Monotonicity and density of the original subspaces give the full real slice criterion. -/
theorem real_sliceCriterion_of_finiteSpikeFamilies (V : ℕ → Submodule K E)
    (hmono : Monotone V) (hdense : Dense (⋃ n, (V n : Set E)))
    (hspikes : FiniteSpikeFamilies K E V) : SliceCriterion ℝ E :=
  sliceCriterion_of_finiteSpikeFamilies (fun n => (V n).restrictScalars ℝ)
    (fun _ _ hnm => hmono hnm) hdense hspikes.restrictScalars

/-- This statement explicitly retains the original additive norm and restricted real action. -/
theorem underlyingReal_sliceCriterion_of_finiteSpikeFamilies
    {K E : Type*} [RCLike K] [NormedAddCommGroup E] [NormedSpace K E]
    (V : ℕ → Submodule K E) (hmono : Monotone V)
    (hdense : Dense (⋃ n, (V n : Set E))) (hspikes : FiniteSpikeFamilies K E V) :
    @SliceCriterion ℝ (UnderlyingReal K E) _
      (inferInstance : NormedAddCommGroup E) (NormedSpace.restrictScalars ℝ K E) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ K E
  exact real_sliceCriterion_of_finiteSpikeFamilies (K := K) (E := E) V hmono hdense hspikes

end PL1.Daugavet

namespace PL1.Noise
variable (K : Type*) [RCLike K]

/-- The Schur construction satisfies every real slice test with the original graph norm. -/
theorem schur_intrinsic_underlyingReal_sliceCriterion :
    @Daugavet.SliceCriterion ℝ (UnderlyingReal K (dyadicSystem K schurRates).IntrinsicSpace) _
      (inferInstance : NormedAddCommGroup (dyadicSystem K schurRates).IntrinsicSpace)
      (NormedSpace.restrictScalars ℝ K (dyadicSystem K schurRates).IntrinsicSpace) :=
  Daugavet.underlyingReal_sliceCriterion_of_finiteSpikeFamilies
    (fun n => (intrinsicExpectation K schurRates n).range)
    (intrinsicExpectation_range_monotone K schurRates)
    (dense_iUnion_intrinsicExpectation_range K schurRates)
    (IntrinsicSpikeFamilies.finiteSpikeFamilies schurRates
      (fun d T _ hδ => TailSpikes.exists_family d T hδ))

/-- The constant-rate construction satisfies the same full real slice criterion. -/
theorem constant_intrinsic_underlyingReal_sliceCriterion :
    @Daugavet.SliceCriterion ℝ (UnderlyingReal K (dyadicSystem K constantRates).IntrinsicSpace) _
      (inferInstance : NormedAddCommGroup (dyadicSystem K constantRates).IntrinsicSpace)
      (NormedSpace.restrictScalars ℝ K (dyadicSystem K constantRates).IntrinsicSpace) :=
  Daugavet.underlyingReal_sliceCriterion_of_finiteSpikeFamilies
    (fun n => (intrinsicExpectation K constantRates n).range)
    (intrinsicExpectation_range_monotone K constantRates)
    (dense_iUnion_intrinsicExpectation_range K constantRates)
    (IntrinsicSpikeFamilies.finiteSpikeFamilies constantRates
      (fun d T _ hδ => TailSpikes.exists_constant_family d T hδ))

/-- All real rank-one operators satisfy the Daugavet equation on the Schur intrinsic space. -/
theorem schur_intrinsic_underlyingReal_hasDaugavetProperty :
    @Daugavet.HasDaugavetProperty ℝ (UnderlyingReal K (dyadicSystem K schurRates).IntrinsicSpace) _
      (inferInstance : NormedAddCommGroup (dyadicSystem K schurRates).IntrinsicSpace)
      (NormedSpace.restrictScalars ℝ K (dyadicSystem K schurRates).IntrinsicSpace) := by
  let := intrinsicSpace_nontrivial K schurRates
  let : NormedSpace ℝ (dyadicSystem K schurRates).IntrinsicSpace :=
    NormedSpace.restrictScalars ℝ K (dyadicSystem K schurRates).IntrinsicSpace
  exact Daugavet.SliceCriterion.hasDaugavetProperty (𝕜 := ℝ) (E := (dyadicSystem K schurRates).IntrinsicSpace) (schur_intrinsic_underlyingReal_sliceCriterion K)

/-- All real rank-one operators satisfy the Daugavet equation on the constant-rate intrinsic space. -/
theorem constant_intrinsic_underlyingReal_hasDaugavetProperty :
    @Daugavet.HasDaugavetProperty ℝ (UnderlyingReal K (dyadicSystem K constantRates).IntrinsicSpace) _
      (inferInstance : NormedAddCommGroup (dyadicSystem K constantRates).IntrinsicSpace)
      (NormedSpace.restrictScalars ℝ K (dyadicSystem K constantRates).IntrinsicSpace) := by
  let := intrinsicSpace_nontrivial K constantRates
  let : NormedSpace ℝ (dyadicSystem K constantRates).IntrinsicSpace :=
    NormedSpace.restrictScalars ℝ K (dyadicSystem K constantRates).IntrinsicSpace
  exact Daugavet.SliceCriterion.hasDaugavetProperty (𝕜 := ℝ) (E := (dyadicSystem K constantRates).IntrinsicSpace) (constant_intrinsic_underlyingReal_sliceCriterion K)

#print axioms schur_intrinsic_underlyingReal_hasDaugavetProperty
#print axioms constant_intrinsic_underlyingReal_hasDaugavetProperty
end PL1.Noise
