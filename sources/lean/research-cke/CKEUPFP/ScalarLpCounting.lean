import CKEUPFP.MainStatements
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Scalar ℓp embeds isometrically in counting-measure Lp

The defining count lintegral is the same sum used for the `lp` norm. This
supplies the bridge needed to obtain the no-c₀ assertion for scalar ℓp from
the corresponding assertion for scalar Lp over an arbitrary measure.
-/

noncomputable section

namespace CKEUPFP

open MeasureTheory
open scoped ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]

theorem finiteBanachExponent_ne_zero (p : FiniteBanachExponent) : p.val ≠ 0 :=
  (zero_lt_one.trans_le p.property.1).ne'

theorem finiteBanachExponent_toReal_pos (p : FiniteBanachExponent) : 0 < p.val.toReal :=
  ENNReal.toReal_pos (finiteBanachExponent_ne_zero p) p.property.2.ne

theorem scalarEllp_count_lintegral (p : FiniteBanachExponent) (f : ScalarEllp 𝕜 p) :
    ∫⁻ n : ℕ, ‖f n‖ₑ ^ p.val.toReal ∂Measure.count =
      ENNReal.ofReal (∑' n : ℕ, ‖f n‖ ^ p.val.toReal) := by
  rw [lintegral_count]
  simp_rw [← ofReal_norm_eq_enorm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun n => Real.rpow_nonneg (norm_nonneg (f n)) p.val.toReal)
    ((lp.memℓp f).summable (finiteBanachExponent_toReal_pos p))).symm

theorem scalarEllp_eLpNorm_count (p : FiniteBanachExponent) (f : ScalarEllp 𝕜 p) :
    eLpNorm f p.val Measure.count = ENNReal.ofReal ‖f‖ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (finiteBanachExponent_ne_zero p) p.property.2.ne,
    scalarEllp_count_lintegral,
    lp.norm_eq_tsum_rpow (finiteBanachExponent_toReal_pos p)]
  exact (ENNReal.ofReal_rpow_of_nonneg
    (tsum_nonneg fun n : ℕ => Real.rpow_nonneg (norm_nonneg (f n)) p.val.toReal)
    (div_nonneg zero_le_one (ENNReal.toReal_nonneg : 0 ≤ p.val.toReal)))

theorem scalarEllp_memLp_count (p : FiniteBanachExponent) (f : ScalarEllp 𝕜 p) :
    MemLp f p.val Measure.count := by
  refine ⟨AEStronglyMeasurable.of_discrete, ?_⟩
  rw [scalarEllp_eLpNorm_count]
  exact ENNReal.ofReal_lt_top

/-- The same scalar sequence, regarded as a class modulo counting-null sets. -/
def scalarLpCountingValue (p : FiniteBanachExponent) (f : ScalarEllp 𝕜 p) :
    Lp 𝕜 p.val (Measure.count (α := ℕ)) :=
  (scalarEllp_memLp_count p f).toLp f

theorem scalarLpCountingValue_norm (p : FiniteBanachExponent) (f : ScalarEllp 𝕜 p) :
    ‖scalarLpCountingValue p f‖ = ‖f‖ := by
  rw [scalarLpCountingValue, Lp.norm_toLp, scalarEllp_eLpNorm_count,
    ENNReal.toReal_ofReal (norm_nonneg f)]

/-- An actual linear isometric embedding for every finite Banach exponent. -/
def scalarLpCountingIsometry (p : FiniteBanachExponent) :
    ScalarEllp 𝕜 p →ₗᵢ[𝕜] Lp 𝕜 p.val (Measure.count (α := ℕ)) where
  toFun := scalarLpCountingValue p
  map_add' f g := by
    exact MemLp.toLp_add (scalarEllp_memLp_count p f) (scalarEllp_memLp_count p g)
  map_smul' c f := by
    exact MemLp.toLp_const_smul c (scalarEllp_memLp_count p f)
  norm_map' := scalarLpCountingValue_norm p

/-- Pull the no-c₀ assertion back through the actual counting-measure embedding. -/
theorem containsNoCZero_scalarEllp_of_countingLp (p : FiniteBanachExponent)
    (h : ContainsNoCZero 𝕜 (Lp 𝕜 p.val (Measure.count (α := ℕ)))) :
    ContainsNoCZero 𝕜 (ScalarEllp 𝕜 p) := by
  rintro ⟨J, c, hc, hJ⟩
  apply h
  refine ⟨(scalarLpCountingIsometry p).toContinuousLinearMap.comp J, c, hc, ?_⟩
  intro y
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map] using hJ y

end CKEUPFP
