import SurveyStatements.P5CaponLeafTests

/-! Actual small tensors used in the Capon counterexample. The inner leaf
vectors are bounded while the outer Rademacher averages converge in norm. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def tensorLeft (f : Lp ℝ p unitIntervalMeasure) :
    Lp ℝ 1 unitIntervalMeasure →L[ℝ] MixedNorm ℝ p :=
  LinearMap.mkContinuous
    { toFun := fun g => tensorWith g f
      map_add' := by
        intro g h
        apply Lp.ext
        filter_upwards [tensorWith_ae (g + h) f, tensorWith_ae g f,
          tensorWith_ae h f, Lp.coeFn_add (tensorWith g f) (tensorWith h f)]
          with x hsum hg hh hadd
        simp only [Pi.add_apply] at hadd
        rw [hsum, hadd, hg, hh]
        exact smul_add _ _ _
      map_smul' := by
        intro c g
        apply Lp.ext
        filter_upwards [tensorWith_ae (c • g) f, tensorWith_ae g f,
          Lp.coeFn_smul c (tensorWith g f)] with x hc hg hmul
        simp only [Pi.smul_apply] at hmul
        simp only [RingHom.id_apply]
        rw [hc, hmul, hg]
        exact smul_comm _ _ _ }
    ‖f‖ (fun g => by simpa only [mul_comm] using (norm_tensorWith ℝ p g f).le)

theorem tensorLeft_apply (f : Lp ℝ p unitIntervalMeasure)
    (g : Lp ℝ 1 unitIntervalMeasure) : tensorLeft f g = tensorWith g f := rfl

theorem tensorWith_sum_left {ι : Type*} (F : Finset ι)
    (g : ι → Lp ℝ 1 unitIntervalMeasure) (f : Lp ℝ p unitIntervalMeasure) :
    tensorWith (∑ i ∈ F, g i) f = ∑ i ∈ F, tensorWith (g i) f :=
  map_sum (tensorLeft f) _ _

theorem tensorWith_smul_left (c : ℝ) (g : Lp ℝ 1 unitIntervalMeasure)
    (f : Lp ℝ p unitIntervalMeasure) : tensorWith (c • g) f = c • tensorWith g f :=
  map_smul (tensorLeft f) c g

def caponInput (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) : MixedNorm ℝ p :=
  tensorWith (leftLeafTest (N + 1)) (rademacherAverageLp p N)

theorem norm_caponInput_le (N : ℕ) :
    ‖caponInput p N‖ ≤ 2 * ‖rademacherAverageLp p N‖ := by
  rw [caponInput, norm_tensorWith]
  exact mul_le_mul_of_nonneg_right (leftLeafTest_norm_le _) (norm_nonneg _)

theorem caponInput_mem_doublyZeroMean (N : ℕ) :
    caponInput p N ∈ DoublyZeroMean ℝ p :=
  tensor_mem_doublyZeroMean _ _ (leftLeafTest_mean_zero _) (rademacherAverageLp_mean_zero _)

theorem tendsto_caponInput (hp_finite : p ≠ ∞) :
    Tendsto (caponInput p) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun N => norm_nonneg _) norm_caponInput_le
    (by simpa using (tendsto_norm_rademacherAverageLp hp_finite).const_mul 2)

theorem caponInput_eq_sum (N : ℕ) :
    caponInput p N = ((N + 1 : ℕ) : ℝ)⁻¹ •
      ∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ k •
        ∑ n ∈ Finset.range (N + 1),
          ∑ l : Fin (2 ^ n), productHaar ℝ p ⟨n, l⟩ (leftDyadicIndex k) := by
  rw [caponInput, rademacherAverageLp, map_smul, leftLeafTest_eq_sum,
    tensorWith_sum_left]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [tensorWith_smul_left, rademacherSumLp, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [dyadicRademacherLp, map_sum]
  rfl

theorem caponInput_eq_level_sum (N : ℕ) :
    caponInput p N = ((N + 1 : ℕ) : ℝ)⁻¹ •
      ∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ k •
        ∑ n ∈ Finset.range (N + 1),
          tensorWith (dyadicHaar ℝ 1 (leftDyadicIndex k)) (dyadicRademacherLp ℝ p n) := by
  rw [caponInput, rademacherAverageLp, map_smul, leftLeafTest_eq_sum,
    tensorWith_sum_left]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [tensorWith_smul_left, rademacherSumLp, map_sum]

end SurveyStatements.P5
