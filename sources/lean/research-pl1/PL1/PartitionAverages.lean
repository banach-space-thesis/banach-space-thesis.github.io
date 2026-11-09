import PL1.TraceBounds

/-! # Contractive averages over finite measurable partitions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ENNReal BigOperators Topology

namespace PL1.PartitionAverages

variable {𝕜 Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (A : ℕ → Set Ω) (hA : ∀ i, MeasurableSet (A i))

def vector (i : ℕ) : Lp 𝕜 1 μ :=
  indicatorConstLp 1 (hA i) (measure_ne_top μ (A i)) (1 : 𝕜)

theorem norm_vector (i : ℕ) : ‖vector (𝕜 := 𝕜) μ A hA i‖ = μ.real (A i) := by
  rw [vector, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [measureReal_def]

def coefficient (i : ℕ) : Lp 𝕜 1 μ →L[𝕜] 𝕜 :=
  (((μ.real (A i))⁻¹ : ℝ) : 𝕜) • TraceBounds.cellFunctional (𝕜 := 𝕜) μ A hA i

omit [IsProbabilityMeasure μ] in
theorem coefficient_apply (i : ℕ) (f : Lp 𝕜 1 μ) :
    coefficient (𝕜 := 𝕜) μ A hA i f = (((μ.real (A i))⁻¹ : ℝ) : 𝕜) * ∫ x in A i, f x ∂μ := by
  simp only [coefficient, smul_apply, TraceBounds.cellFunctional_apply, smul_eq_mul]

def average (s : Finset ℕ) : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ :=
  ∑ i ∈ s, (coefficient (𝕜 := 𝕜) μ A hA i).smulRight (vector (𝕜 := 𝕜) μ A hA i)

theorem average_apply (s : Finset ℕ) (f : Lp 𝕜 1 μ) :
    average μ A hA s f = ∑ i ∈ s, coefficient (𝕜 := 𝕜) μ A hA i f • vector (𝕜 := 𝕜) μ A hA i := by
  simp only [average, sum_apply, ContinuousLinearMap.smulRight_apply]

theorem norm_coefficient_smul_vector_le (i : ℕ) (f : Lp 𝕜 1 μ) :
    ‖coefficient (𝕜 := 𝕜) μ A hA i f • vector (𝕜 := 𝕜) μ A hA i‖ ≤
      ‖TraceBounds.cellFunctional (𝕜 := 𝕜) μ A hA i f‖ := by
  simp only [norm_smul, norm_vector, coefficient, smul_apply, norm_smul,
    RCLike.norm_ofReal, abs_inv, abs_of_nonneg (measureReal_nonneg)]
  by_cases hi : μ.real (A i) = 0
  · simp [hi]
  · rw [mul_right_comm, inv_mul_cancel₀ hi, one_mul]

theorem norm_average_apply_le (s : Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (f : Lp 𝕜 1 μ) :
    ‖average μ A hA s f‖ ≤ ‖f‖ := by
  rw [average_apply]
  calc
    _ ≤ ∑ i ∈ s, ‖coefficient (𝕜 := 𝕜) μ A hA i f • vector (𝕜 := 𝕜) μ A hA i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖TraceBounds.cellFunctional (𝕜 := 𝕜) μ A hA i f‖ :=
      Finset.sum_le_sum (fun i _ => norm_coefficient_smul_vector_le μ A hA i f)
    _ ≤ ∑ i ∈ s, ‖L1Masks.mask μ (A i) (hA i) f‖ :=
      Finset.sum_le_sum (fun i _ => TraceBounds.norm_cellFunctional_apply_le_mask μ A hA i f)
    _ ≤ ‖f‖ := L1Masks.sum_norm_mask_le μ s A hA hdisj f

theorem norm_average_le_one (s : Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ‖average (𝕜 := 𝕜) μ A hA s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_average_apply_le μ A hA s hdisj f

theorem cellFunctional_vector
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (i j : ℕ) :
    TraceBounds.cellFunctional (𝕜 := 𝕜) μ A hA i (vector (𝕜 := 𝕜) μ A hA j) =
      if i = j then (μ.real (A i) : 𝕜) else 0 := by
  rw [TraceBounds.cellFunctional_apply]
  unfold vector
  rw [integral_congr_ae (ae_restrict_of_ae
    (indicatorConstLp_coeFn (p := 1) (hs := hA j) (hμs := measure_ne_top μ (A j))
      (c := (1 : 𝕜)))), setIntegral_indicator (hA j)]
  by_cases hij : i = j
  · subst j
    simp [Algebra.smul_def]
  · rw [Set.disjoint_iff_inter_eq_empty.mp (hdisj hij)]
    simp [hij]

theorem average_vector (s : Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (j : ℕ) (hj : j ∈ s) :
    average μ A hA s (vector (𝕜 := 𝕜) μ A hA j) = vector (𝕜 := 𝕜) μ A hA j := by
  by_cases hμ : μ.real (A j) = 0
  · have hz : vector (𝕜 := 𝕜) μ A hA j = 0 := norm_eq_zero.mp (by rw [norm_vector, hμ])
    rw [hz, map_zero]
  · rw [average_apply]
    simp only [coefficient, smul_apply, cellFunctional_vector (𝕜 := 𝕜) μ A hA hdisj]
    rw [Finset.sum_eq_single j]
    · simp only [ite_true]
      rw [smul_eq_mul, ← RCLike.ofReal_mul, inv_mul_cancel₀ hμ, RCLike.ofReal_one, one_smul]
    · intro i hi hij
      simp [hij]
    · exact fun h => (h hj).elim

theorem average_step (s : Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (c : ℕ → 𝕜) :
    average μ A hA s (∑ i ∈ s, c i • vector (𝕜 := 𝕜) μ A hA i) =
      ∑ i ∈ s, c i • vector (𝕜 := 𝕜) μ A hA i := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, average_vector (𝕜 := 𝕜) μ A hA s hdisj i hi]

theorem norm_coefficient_le_of_ae_bound (i : ℕ) (f : Lp 𝕜 1 μ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖coefficient (𝕜 := 𝕜) μ A hA i f‖ ≤ C := by
  have hi := norm_integral_le_of_norm_le_const (μ := μ.restrict (A i))
    (ae_restrict_of_ae hf)
  rw [coefficient_apply, norm_mul, RCLike.norm_ofReal,
    abs_inv, abs_of_nonneg (measureReal_nonneg)]
  by_cases hμ : μ.real (A i) = 0
  · simpa [hμ] using hC
  · calc
      _ ≤ (μ.real (A i))⁻¹ * (C * μ.real (A i)) :=
        mul_le_mul_of_nonneg_left (by simpa using hi) (inv_nonneg.mpr (measureReal_nonneg))
      _ = C := by field_simp

theorem norm_coefficient_inclusion_le_one (i : ℕ) (f : Lp 𝕜 ∞ μ) (hf : ‖f‖ ≤ 1) :
    ‖coefficient (𝕜 := 𝕜) μ A hA i (ProbabilityLp.inclusion μ 1 ∞ le_top f)‖ ≤ 1 := by
  apply norm_coefficient_le_of_ae_bound μ A hA i _ 1 zero_le_one
  filter_upwards [ProbabilityLp.coeFn_inclusion μ 1 ∞ le_top f,
    ae_le_eLpNormEssSup (f := (f : Ω → 𝕜))] with x hx hnorm
  rw [hx]
  have h := ENNReal.toReal_mono (show eLpNormEssSup (f : Ω → 𝕜) μ ≠ ∞ from (Lp.memLp f).2.ne) hnorm
  have h' : ‖f x‖ ≤ ‖f‖ := by simpa only [toReal_enorm, Lp.norm_def, eLpNorm_exponent_top] using h
  exact h'.trans hf

end PL1.PartitionAverages

