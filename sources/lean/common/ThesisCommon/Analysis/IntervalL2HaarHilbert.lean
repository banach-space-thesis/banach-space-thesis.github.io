import ThesisCommon.Analysis.LpHaarSchauderBasis
import ThesisCommon.Analysis.LpHaarCoefficientFormula
import ThesisCommon.Analysis.SchauderHilbertBasis
import ThesisCommon.Analysis.ScalarLpPrimary
import Mathlib.MeasureTheory.Function.L2Space

/-! The genuine interval L2 space has a countable Hilbert representation
given by its actual normalized Haar basis. This proves its base UPFP; it
does not assert the corresponding statement at other exponents. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal Classical ComplexConjugate
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

def lpHaarHilbertWeight : Option (Σ n : ℕ, Fin (2 ^ n)) → ℝ
  | none => 1
  | some ⟨n, _⟩ => intervalLpDyadicRadius n

theorem lpHaarRaw_inner_eq_weight_coordinate
    (i : Option (Σ n : ℕ, Fin (2 ^ n))) (f : IntervalLp 𝕜 ⟨2, by norm_num⟩) :
    inner 𝕜 (lpHaarRawVector 𝕜 ⟨2, by norm_num⟩ i) f =
      (lpHaarHilbertWeight i : 𝕜) * lpHaarRawCoordinate 𝕜 ⟨2, by norm_num⟩ i f := by
  cases i with
  | none =>
      have heq : Lp.const (2 : ℝ≥0∞) (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜) =
          indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) (1 : 𝕜) := by
        apply Lp.ext
        filter_upwards [Lp.coeFn_const (2 : ℝ≥0∞)
          (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜),
          indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
            (hs := MeasurableSet.univ) (hμs := measure_ne_top
              (volume.restrict (Icc (0 : ℝ) 1)) Set.univ) (c := (1 : 𝕜))] with x hx hy
        simp only [Set.indicator_univ, Pi.one_apply] at hy
        exact hx.trans hy.symm
      simp only [lpHaarRawVector, lpHaarRawCoordinate, lpHaarHilbertWeight,
        RCLike.ofReal_one, one_mul, heq, lpHaarIntegral_apply]
      rw [L2.inner_indicatorConstLp_one]
      simp
  | some i =>
      rcases i with ⟨n, k⟩
      change inner 𝕜 (lpHaarDyadic 𝕜 ⟨2, by norm_num⟩ n k) f =
        (intervalLpDyadicRadius n : 𝕜) * lpHaarDyadicCoefficient 𝕜 ⟨2, by norm_num⟩ n k f
      rw [lpHaarDyadicCoefficient_apply_integrals 𝕜 _ n k k.isLt, lpHaarDyadic,
        lpHaarVector, inner_sub_left, L2.inner_indicatorConstLp_one,
        L2.inner_indicatorConstLp_one]
      have hn : (intervalLpDyadicRadius n : 𝕜) ≠ 0 :=
        RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos n).ne'
      rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

theorem lpHaarHilbertWeight_eq_norm_sq
    (i : Option (Σ n : ℕ, Fin (2 ^ n))) :
    (lpHaarHilbertWeight i : 𝕜) =
      ((‖lpHaarRawVector 𝕜 ⟨2, by norm_num⟩ i‖ : ℝ) : 𝕜) ^ 2 := by
  have h := lpHaarRaw_inner_eq_weight_coordinate 𝕜 i
    (lpHaarRawVector 𝕜 ⟨2, by norm_num⟩ i)
  rw [lpHaarRaw_biorthogonal 𝕜 _ (by simp) i i, if_pos rfl, mul_one,
    inner_self_eq_norm_sq_to_K] at h
  simpa only [map_pow] using h.symm

theorem lpHaarNormalizedCoordinate_eq_inner
    (i : Option (Σ n : ℕ, Fin (2 ^ n))) (f : IntervalLp 𝕜 ⟨2, by norm_num⟩) :
    lpHaarNormalizedCoordinate 𝕜 ⟨2, by norm_num⟩ i f =
      inner 𝕜 (lpHaarNormalizedVector 𝕜 ⟨2, by norm_num⟩ i) f := by
  rw [lpHaarNormalizedVector, inner_smul_left]
  simp only [map_inv₀, RCLike.conj_ofReal]
  rw [lpHaarRaw_inner_eq_weight_coordinate, lpHaarHilbertWeight_eq_norm_sq,
    lpHaarNormalizedCoordinate, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hn : ((‖lpHaarRawVector 𝕜 ⟨2, by norm_num⟩ i‖ : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (lpHaarRawVector_norm_pos 𝕜 _ (by simp) i).ne'
  field_simp

def intervalL2HaarHilbertBasis : HilbertBasis ℕ 𝕜 (IntervalLp 𝕜 ⟨2, by norm_num⟩) :=
  (intervalLpHaarBasis 𝕜 ⟨2, by norm_num⟩ (by simp)).toHilbertBasis
    (fun n x => lpHaarNormalizedCoordinate_eq_inner 𝕜 (lpHaarIndexEquiv n) x)

def intervalL2HaarIsometry : IntervalLp 𝕜 ⟨2, by norm_num⟩ ≃ₗᵢ[𝕜]
    lp (fun _ : ℕ => 𝕜) 2 := (intervalL2HaarHilbertBasis 𝕜).repr

theorem intervalL2_hasUPFP : HasUPFP 𝕜 (IntervalLp 𝕜 ⟨2, by norm_num⟩) :=
  (scalar_lp_hasUPFP (𝕜 := 𝕜) 2).of_equiv
    (intervalL2HaarIsometry 𝕜).symm.toContinuousLinearEquiv

end ThesisCommon
