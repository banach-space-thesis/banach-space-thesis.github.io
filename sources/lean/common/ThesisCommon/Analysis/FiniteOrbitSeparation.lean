import ThesisCommon.Analysis.FiniteAbsoluteConvexOrbit
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Convex

/-! Quantitative geometric Hahn--Banach separation for the actual finite
absolute-convex orbit. The resulting functional has norm one and controls
every orbit generator; the premise is literal distance from that orbit. -/
noncomputable section
open scoped BigOperators Pointwise
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

theorem norm_functional_le_inv_of_re_ball_lt_one (f : X →L[𝕜] 𝕜)
    {ε r : ℝ} (hr : 0 < r) (hrε : r < ε)
    (hf : ∀ z : X, ‖z‖ < ε → RCLike.re (f z) < 1) : ‖f‖ ≤ r⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (inv_nonneg.mpr hr.le)
  intro x hx
  obtain ⟨a, ha, hphase⟩ := RCLike.exists_norm_eq_mul_self (f (r • x))
  have hnorm : ‖a • (r • x)‖ < ε := by
    simpa only [norm_smul, ha, Real.norm_eq_abs, abs_of_pos hr, hx, mul_one,
      one_mul] using hrε
  have hsmall : ‖f (r • x)‖ < 1 := by
    simpa only [map_smul, smul_eq_mul, ← hphase, RCLike.ofReal_re] using
      hf (a • (r • x)) hnorm
  have hmap : f (r • x) = r • f x := (f.restrictScalars ℝ).map_smul r x
  rw [hmap, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hsmall
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hr).mpr
  simpa only [mul_comm] using hsmall.le

variable {ι : Type*} [Fintype ι]

theorem exists_unit_functional_separating_finite_orbit (v : ι → X) (y : X)
    {m ε : ℝ} (hm : 0 < m) (hε : 0 < ε)
    (hsep : ∀ w ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜) v m, ε ≤ ‖y - w‖) :
    ∃ f : X →L[𝕜] 𝕜, ‖f‖ = 1 ∧ ε / 2 < RCLike.re (f y) ∧
      ∀ i, ‖f (v i)‖ ≤ ‖y‖ / m := by
  let O := finiteAbsoluteConvexOrbit (𝕜 := 𝕜) v m
  let A := O + Metric.ball (0 : X) ε
  have h0O : (0 : X) ∈ O := zero_mem_finiteAbsoluteConvexOrbit v hm.le
  have h0B : (0 : X) ∈ Metric.ball (0 : X) ε := by simpa using hε
  have h0A : (0 : X) ∈ A := ⟨0, h0O, 0, h0B, by simp⟩
  have hconv : Convex ℝ A := (convex_finiteAbsoluteConvexOrbit v m).add (convex_ball _ _)
  have hopen : IsOpen A := Metric.isOpen_ball.add_left
  have hyA : y ∉ A := by
    rintro ⟨w, hw, z, hz, hy⟩
    have hdist : ‖z‖ < ε := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have heq : y - w = z := by rw [← hy]; change w + z - w = z; abel
    exact (not_lt_of_ge (hsep w hw)) (heq.symm ▸ hdist)
  obtain ⟨f, hfy, hfA⟩ := RCLike.separate_convex_open_set (𝕜 := 𝕜) h0A hconv hopen hyA
  have hf0 : f ≠ 0 := by
    intro hz
    simp only [hz, ContinuousLinearMap.zero_apply, map_zero] at hfy
    norm_num at hfy
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  have hfball : ∀ z : X, ‖z‖ < ε → RCLike.re (f z) < 1 := by
    intro z hz
    apply hfA z
    exact ⟨0, h0O, z, by simpa only [Metric.mem_ball, dist_zero_right] using hz,
      zero_add z⟩
  have hr : 0 < 3 * ε / 4 := by linarith
  have hrε : 3 * ε / 4 < ε := by linarith
  have hfnorm := norm_functional_le_inv_of_re_ball_lt_one f hr hrε hfball
  let g : X →L[𝕜] 𝕜 := (‖f‖⁻¹ : ℝ) • f
  have hgnorm : ‖g‖ = 1 := by
    simp only [g, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hfpos),
      inv_mul_cancel₀ hfpos.ne']
  have hgy : RCLike.re (g y) = ‖f‖⁻¹ := by
    simp only [g, ContinuousLinearMap.smul_apply, RCLike.smul_re, hfy, mul_one]
  have hrlower : 3 * ε / 4 ≤ ‖f‖⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hfpos).mpr
    have h := (le_div_iff₀ hr).mp
      (show ‖f‖ ≤ 1 / (3 * ε / 4) by simpa only [inv_eq_one_div] using hfnorm)
    simpa only [mul_comm] using h
  refine ⟨g, hgnorm, ?_, ?_⟩
  · rw [hgy]
    linarith
  · intro i
    obtain ⟨a, ha, hphase⟩ := RCLike.exists_norm_eq_mul_self (g (v i))
    have hcoef : ‖(m : 𝕜) * a‖ ≤ m := by
      simp only [norm_mul, RCLike.norm_ofReal, abs_of_pos hm, ha, mul_one, le_refl]
    have hwO : ((m : 𝕜) * a) • v i ∈ O := smul_mem_finiteAbsoluteConvexOrbit v i _ hcoef
    have hwA : ((m : 𝕜) * a) • v i ∈ A :=
      ⟨_, hwO, 0, h0B, add_zero _⟩
    have hw := hfA _ hwA
    have hwg : RCLike.re (g (((m : 𝕜) * a) • v i)) < RCLike.re (g y) := by
      simp only [g, ContinuousLinearMap.smul_apply, RCLike.smul_re, hfy]
      exact mul_lt_mul_of_pos_left hw (inv_pos.mpr hfpos)
    have hvalue : RCLike.re (g (((m : 𝕜) * a) • v i)) = m * ‖g (v i)‖ := by
      rw [map_smul, smul_eq_mul, mul_assoc, ← hphase, RCLike.re_ofReal_mul,
        RCLike.ofReal_re]
    have hybound : RCLike.re (g y) ≤ ‖y‖ := by
      calc
        _ ≤ ‖g y‖ := RCLike.re_le_norm _
        _ ≤ ‖g‖ * ‖y‖ := g.le_opNorm y
        _ = ‖y‖ := by rw [hgnorm, one_mul]
    apply (le_div_iff₀ hm).mpr
    simpa only [mul_comm] using (hvalue ▸ hwg.le).trans hybound

end ThesisCommon
