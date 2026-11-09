import PL1.KFunctionalIntegral
import PL1.GeneratorGraphBanach

/-!
# The full interpolation identification with the actual generator domain

The norm below is the standard real interpolation integral at (1/2, 1),
defined directly from the actual complete graph-norm domain of the positive
generator. Its finite functions are exactly the original intrinsic space.
All statements hold for every nonnegative coordinate rate sequence, hence
for both manuscript constructions over either scalar field.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1.Interpolation
open Noise Walsh IntrinsicGraph ResolventEstimates

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

/-- The extended standard (Y,D(A))_{1/2,1} norm, with D(A)'s actual sum norm. -/
def normIntegral (f : Lp K 1 haar) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-3 / 2 : ℝ) *
    sInf (Set.range (fun z : GeneratorGraphBanach.Domain K rates =>
      ‖f - GeneratorGraphBanach.inclusion K rates z‖ + t * ‖z‖)))

theorem normIntegral_eq (f : Lp K 1 haar) :
    normIntegral K rates f = KFunctional.continuousNorm K rates f := by
  unfold normIntegral KFunctional.continuousNorm
  congr 1
  funext t
  rw [GeneratorGraphBanach.kFunctional_eq]

/-- Equality as spaces of actual Haar-L1 functions. -/
theorem mem_intrinsic_iff (f : Lp K 1 haar) :
    f ∈ (evalZero (dyadicSystem K rates).analysis).range ↔ normIntegral K rates f < ⊤ := by
  rw [normIntegral_eq, lt_top_iff_ne_top, KFunctional.continuousNorm_ne_top_iff,
    DiscreteInterpolation.extendedNorm_ne_top_iff]

theorem normIntegral_eval_ne_top (x : (dyadicSystem K rates).IntrinsicSpace) :
    normIntegral K rates (evalZero (dyadicSystem K rates).analysis x) ≠ ⊤ :=
  ((mem_intrinsic_iff K rates _).mp ⟨x, rfl⟩).ne

/-- The real value is used only on the finite domain in the norm comparisons. -/
def normValue (f : Lp K 1 haar) : ℝ := (normIntegral K rates f).toReal

theorem normValue_lower (x : (dyadicSystem K rates).IntrinsicSpace) :
    (1 / 10 : ℝ) * ‖x‖ ≤ normValue K rates (evalZero (dyadicSystem K rates).analysis x) := by
  let f := evalZero (dyadicSystem K rates).analysis x
  have hI : KFunctional.continuousNorm K rates f ≠ ⊤ := by
    rw [← normIntegral_eq]
    exact normIntegral_eval_ne_top K rates x
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num : (5 : ℝ≥0∞) ≠ ⊤) hI)
    (KFunctional.extendedNorm_le_five_continuousNorm K rates f)
  rw [DiscreteInterpolation.extendedNorm_eval_eq] at h
  have hd : 0 ≤ DiscreteInterpolation.normValue K rates f :=
    add_nonneg (norm_nonneg _) (tsum_nonneg (DiscreteInterpolation.term_nonneg K rates f))
  rw [ENNReal.toReal_ofReal hd, ENNReal.toReal_mul] at h
  norm_num only [ENNReal.toReal_ofNat] at h
  have hl := DiscreteInterpolation.half_norm_le K rates x
  change (1 / 2 : ℝ) * ‖x‖ ≤ DiscreteInterpolation.normValue K rates f at hl
  rw [normValue, normIntegral_eq]
  change (1 / 10 : ℝ) * ‖x‖ ≤ (KFunctional.continuousNorm K rates f).toReal
  linarith

theorem normValue_upper (x : (dyadicSystem K rates).IntrinsicSpace) :
    normValue K rates (evalZero (dyadicSystem K rates).analysis x) ≤
      (4 * (2 + dyadicRatio / (1 - dyadicRatio))) * ‖x‖ := by
  let f := evalZero (dyadicSystem K rates).analysis x
  have hD : DiscreteInterpolation.extendedNorm K rates f ≠ ⊤ :=
    (DiscreteInterpolation.extendedNorm_ne_top_iff K rates f).mpr ⟨x, rfl⟩
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) hD)
    (KFunctional.continuousNorm_le_four_extendedNorm K rates f)
  rw [DiscreteInterpolation.extendedNorm_eval_eq] at h
  have hd : 0 ≤ DiscreteInterpolation.normValue K rates f :=
    add_nonneg (norm_nonneg _) (tsum_nonneg (DiscreteInterpolation.term_nonneg K rates f))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd] at h
  norm_num only [ENNReal.toReal_ofNat] at h
  have hu := DiscreteInterpolation.normValue_le K rates x
  change DiscreteInterpolation.normValue K rates f ≤
    (2 + dyadicRatio / (1 - dyadicRatio)) * ‖x‖ at hu
  rw [normValue, normIntegral_eq]
  change (KFunctional.continuousNorm K rates f).toReal ≤ _
  nlinarith

/-- Full function-space identification and universal equivalent-norm bounds. -/
theorem intrinsic_eq_realInterpolation :
    (∀ f : Lp K 1 haar,
      f ∈ (evalZero (dyadicSystem K rates).analysis).range ↔ normIntegral K rates f < ⊤) ∧
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ x : (dyadicSystem K rates).IntrinsicSpace,
        c * ‖x‖ ≤ normValue K rates (evalZero (dyadicSystem K rates).analysis x) ∧
        normValue K rates (evalZero (dyadicSystem K rates).analysis x) ≤ C * ‖x‖ := by
  refine ⟨mem_intrinsic_iff K rates, 1 / 10,
    4 * (2 + dyadicRatio / (1 - dyadicRatio)), by norm_num, ?_, ?_⟩
  · have hc : 0 ≤ dyadicRatio / (1 - dyadicRatio) :=
      div_nonneg dyadicRatio_nonneg one_sub_dyadicRatio_pos.le
    positivity
  · exact fun x => ⟨normValue_lower K rates x, normValue_upper K rates x⟩

theorem schur_mem_intrinsic_iff (f : Lp K 1 haar) :
    f ∈ (evalZero (dyadicSystem K schurRates).analysis).range ↔ normIntegral K schurRates f < ⊤ :=
  mem_intrinsic_iff K schurRates f

theorem constant_mem_intrinsic_iff (f : Lp K 1 haar) :
    f ∈ (evalZero (dyadicSystem K constantRates).analysis).range ↔ normIntegral K constantRates f < ⊤ :=
  mem_intrinsic_iff K constantRates f

end PL1.Interpolation
