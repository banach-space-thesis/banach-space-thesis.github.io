import BanachIsometric.Covariance
import Mathlib.Analysis.NormedSpace.Normalize
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Positive radial moments and their exact scaling

The constants in the signed integral identity are actual unnormalised body
moments. Their positivity uses only a neighbourhood of zero, and the scaling
exponent is exactly the ambient real dimension plus the weight degree.
-/

namespace BanachIsometric

open MeasureTheory Set NormedSpace
open scoped Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_norm_pow_smul_set (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Set E) (m : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ x in r • S, ‖x‖ ^ m ∂μ) =
      r ^ (Module.finrank ℝ E + m) * ∫ x in S, ‖x‖ ^ m ∂μ := by
  have he : (∫ x in S, ‖r • x‖ ^ m ∂μ) = r ^ m * ∫ x in S, ‖x‖ ^ m ∂μ := by
    simp_rw [norm_smul, Real.norm_of_nonneg hr.le, mul_pow]
    exact integral_const_mul _ _
  have hc := Measure.setIntegral_comp_smul_of_pos μ (fun x : E => ‖x‖ ^ m) S hr
  rw [he, smul_eq_mul] at hc
  have hn : r ^ Module.finrank ℝ E ≠ 0 := pow_ne_zero _ hr.ne'
  calc
    (∫ x in r • S, ‖x‖ ^ m ∂μ) =
        r ^ Module.finrank ℝ E * ((r ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in r • S, ‖x‖ ^ m ∂μ) := by rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
    _ = r ^ Module.finrank ℝ E * (r ^ m * ∫ x in S, ‖x‖ ^ m ∂μ) := by rw [← hc]
    _ = r ^ (Module.finrank ℝ E + m) * ∫ x in S, ‖x‖ ^ m ∂μ := by
      rw [pow_add, mul_assoc]

variable [Nontrivial E]

omit [FiniteDimensional ℝ E] in
theorem integral_norm_pow_pos_of_zero_mem_interior
    (μ : Measure E) [μ.IsAddHaarMeasure] {S : Set E}
    (hS : IsCompact S) (h0 : (0 : E) ∈ interior S) (m : ℕ) :
    0 < ∫ x in S, ‖x‖ ^ m ∂μ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds h0)
  let x : E := (r / 2) • normalize v
  have hn : ‖x‖ = r / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (half_pos hr).le, norm_normalize hv, mul_one]
  have hx : x ∈ interior S := by
    apply hball
    simpa only [Metric.mem_ball, dist_zero_right, hn] using half_lt_self hr
  have hpos : 0 < ‖x‖ ^ m := pow_pos (by rw [hn]; exact half_pos hr) m
  have hcont : Continuous (fun z : E => ‖z‖ ^ m) := continuous_norm.pow m
  have hopen : IsOpen (interior S ∩ Function.support (fun z : E => ‖z‖ ^ m)) :=
    isOpen_interior.inter hcont.isOpen_support
  have hsupp : 0 < μ (Function.support (fun z : E => ‖z‖ ^ m) ∩ S) := by
    apply (hopen.measure_pos μ ⟨x, hx, hpos.ne'⟩).trans_le
    apply measure_mono
    exact fun z hz => ⟨hz.2, interior_subset hz.1⟩
  exact (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun z => pow_nonneg (norm_nonneg z) m))
    (hcont.continuousOn.integrableOn_compact hS)).mpr hsupp

end BanachIsometric
