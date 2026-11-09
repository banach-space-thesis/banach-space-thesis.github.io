import PL1.IntervalDyadicApproximation
import PL1.DyadicCellMeasure
import PL1.FiniteSummingFromMatrix

/-! Actual contractive finite ell1 coordinates for interval dyadic averages. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace PL1.DyadicL1Coordinates
open PL1.DyadicTrace PL1.FiniteSumming
attribute [local instance] intervalMeasure_probability

def normalizedVector (m : ℕ) (i : Fin (2 ^ m)) : IntervalL1 ℝ :=
  (2 : ℝ) ^ m • dyadicVector m i

theorem norm_normalizedVector (m : ℕ) (i : Fin (2 ^ m)) :
    ‖normalizedVector m i‖ = 1 := by
  rw [normalizedVector, norm_smul, PartitionAverages.norm_vector]
  rw [measureReal_def, intervalMeasure_cell_toReal m i i.isLt]
  simp

def synthesis (m : ℕ) : EllOne (2 ^ m) →L[ℝ] IntervalL1 ℝ :=
  ∑ i : Fin (2 ^ m), (PiLp.proj 1 (fun _ : Fin (2 ^ m) => ℝ) i).smulRight
    (normalizedVector m i)

theorem synthesis_apply (m : ℕ) (x : EllOne (2 ^ m)) :
    synthesis m x = ∑ i, x i • normalizedVector m i := by
  simp [synthesis]

theorem norm_synthesis_le_one (m : ℕ) : ‖synthesis m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, synthesis_apply, norm_ellOne]
  calc
    _ ≤ ∑ i, ‖x i • normalizedVector m i‖ := norm_sum_le _ _
    _ = _ := by simp [norm_smul, norm_normalizedVector, Real.norm_eq_abs]

def analysisLinear (m : ℕ) : IntervalL1 ℝ →ₗ[ℝ] EllOne (2 ^ m) :=
  (WithLp.linearEquiv 1 ℝ (Fin (2 ^ m) → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi (fun i : Fin (2 ^ m) =>
      (TraceBounds.cellFunctional (𝕜 := ℝ) intervalMeasure (cell m)
        (measurableSet_cell m) i).toLinearMap))

theorem analysisLinear_apply (m : ℕ) (f : IntervalL1 ℝ) (i : Fin (2 ^ m)) :
    analysisLinear m f i = TraceBounds.cellFunctional intervalMeasure (cell m)
      (measurableSet_cell m) i f := rfl

theorem norm_analysisLinear_le (m : ℕ) (f : IntervalL1 ℝ) :
    ‖analysisLinear m f‖ ≤ ‖f‖ := by
  rw [norm_ellOne]
  simp_rw [analysisLinear_apply, ← Real.norm_eq_abs]
  rw [← Finset.sum_range (fun i => ‖TraceBounds.cellFunctional (𝕜 := ℝ)
    intervalMeasure (cell m) (measurableSet_cell m) i f‖)]
  calc
    _ ≤ ∑ i ∈ Finset.range (2 ^ m),
        ‖L1Masks.mask intervalMeasure (cell m i) (measurableSet_cell m i) f‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact TraceBounds.norm_cellFunctional_apply_le_mask intervalMeasure (cell m)
        (measurableSet_cell m) i f
    _ ≤ ‖f‖ := L1Masks.sum_norm_mask_le intervalMeasure (Finset.range (2 ^ m))
      (cell m) (measurableSet_cell m) (pairwiseDisjoint_cell m) f

def analysis (m : ℕ) : IntervalL1 ℝ →L[ℝ] EllOne (2 ^ m) :=
  (analysisLinear m).mkContinuous 1 (by
    intro f
    simpa using norm_analysisLinear_le m f)

theorem analysis_apply (m : ℕ) (f : IntervalL1 ℝ) (i : Fin (2 ^ m)) :
    analysis m f i = TraceBounds.cellFunctional intervalMeasure (cell m)
      (measurableSet_cell m) i f := rfl

theorem norm_analysis_le_one (m : ℕ) : ‖analysis m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa [analysis] using norm_analysisLinear_le m f

theorem synthesis_analysis (m : ℕ) (f : IntervalL1 ℝ) :
    synthesis m (analysis m f) = dyadicAverage m f := by
  rw [synthesis_apply]
  simp_rw [analysis_apply, normalizedVector, smul_smul]
  rw [← Finset.sum_range (fun i => (TraceBounds.cellFunctional (𝕜 := ℝ)
    intervalMeasure (cell m) (measurableSet_cell m) i f * (2 : ℝ) ^ m) • dyadicVector m i)]
  rw [dyadicAverage, PartitionAverages.average_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < 2 ^ m := Finset.mem_range.mp hi
  rw [PartitionAverages.coefficient, smul_apply]
  rw [measureReal_def, intervalMeasure_cell_toReal m i hi']
  simp [mul_comm, smul_eq_mul]

theorem cellFunctional_normalizedVector (m : ℕ) (i j : Fin (2 ^ m)) :
    TraceBounds.cellFunctional (𝕜 := ℝ) intervalMeasure (cell m) (measurableSet_cell m)
      i (normalizedVector m j) = if i = j then 1 else 0 := by
  rw [normalizedVector, map_smul,
    PartitionAverages.cellFunctional_vector intervalMeasure (cell m)
      (measurableSet_cell m) (pairwiseDisjoint_cell m)]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, smul_eq_mul, measureReal_def]
    rw [intervalMeasure_cell_toReal m i i.isLt]
    exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))
  · have hval : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp [hij, hval]

theorem analysis_synthesis (m : ℕ) (x : EllOne (2 ^ m)) :
    analysis m (synthesis m x) = x := by
  ext i
  rw [analysis_apply, synthesis_apply, map_sum]
  simp only [map_smul, cellFunctional_normalizedVector, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  simp

theorem norm_synthesis (m : ℕ) (x : EllOne (2 ^ m)) :
    ‖synthesis m x‖ = ‖x‖ := by
  apply le_antisymm
  · exact ((synthesis m).le_opNorm x).trans (by
      simpa using mul_le_mul_of_nonneg_right (norm_synthesis_le_one m) (norm_nonneg x))
  · calc
      ‖x‖ = ‖analysis m (synthesis m x)‖ := congrArg norm (analysis_synthesis m x).symm
      _ ≤ ‖synthesis m x‖ := by
        exact ((analysis m).le_opNorm _).trans (by
          simpa using mul_le_mul_of_nonneg_right (norm_analysis_le_one m) (norm_nonneg _))

end PL1.DyadicL1Coordinates
