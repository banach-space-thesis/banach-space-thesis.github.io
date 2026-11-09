import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Actual positive Jacobian of a positive radial change of coordinates

For `F(x) = a(x) x`, differentiating degree-zero radial scaling gives
`Da(x)[x] = 0`. The actual rank-one determinant lemma then gives
`det DF(x) = a(x)^dim`, so the sign is positive whenever `a(x)>0`.
No orientation or degree-composition assertion is assumed.
-/

namespace BanachIsometric

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem derivative_zeroHomogeneous_apply_self
    {a : E → ℝ} {a' : E →L[ℝ] ℝ} {x : E} (ha : HasFDerivAt a a' x)
    (hscale : ∀ t : ℝ, 0 < t → a (t • x) = a x) : a' x = 0 := by
  have hline : HasDerivAt (fun t : ℝ => a (t • x)) (a' x) 1 := by
    have ha' : HasFDerivAt a a' ((1 : ℝ) • x) := by simpa only [one_smul] using ha
    simpa only [one_smul] using ha'.comp_hasDerivAt (1 : ℝ)
      ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have heq : (fun t : ℝ => a (t • x)) =ᶠ[𝓝 1] (fun _ => a x) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hscale t ht
  exact hline.unique ((hasDerivAt_const (1 : ℝ) (a x)).congr_of_eventuallyEq heq)

variable [FiniteDimensional ℝ E]

theorem det_id_add_smulRight (ℓ : E →L[ℝ] ℝ) (x : E) :
    (ContinuousLinearMap.id ℝ E + ℓ.smulRight x).det = 1 + ℓ x := by
  classical
  let b := Module.finBasis ℝ E
  change LinearMap.det (LinearMap.id + ℓ.toLinearMap.smulRight x) = _
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_id,
    LinearMap.toMatrix_smulRight, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  change (∑ i, ℓ (b i) * b.repr x i) = ℓ x
  calc
    (∑ i, ℓ (b i) * b.repr x i) = ℓ (∑ i, b.repr x i • b i) := by
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
    _ = ℓ x := by rw [b.sum_repr]

theorem det_posScalar_id_add_smulRight (c : ℝ) (hc : c ≠ 0)
    (ℓ : E →L[ℝ] ℝ) (x : E) (hℓx : ℓ x = 0) :
    (c • ContinuousLinearMap.id ℝ E + ℓ.smulRight x).det = c ^ Module.finrank ℝ E := by
  have hfactor : c • ContinuousLinearMap.id ℝ E + ℓ.smulRight x =
      c • (ContinuousLinearMap.id ℝ E + (c⁻¹ • ℓ).smulRight x) := by
    ext v
    change c • v + ℓ v • x = c • (v + (c⁻¹ * ℓ v) • x)
    rw [smul_add, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [hfactor]
  change LinearMap.det (c • (ContinuousLinearMap.id ℝ E +
    (c⁻¹ • ℓ).smulRight x).toLinearMap) = _
  rw [LinearMap.det_smul]
  change c ^ Module.finrank ℝ E * (ContinuousLinearMap.id ℝ E +
    (c⁻¹ • ℓ).smulRight x).det = _
  rw [det_id_add_smulRight]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hℓx, mul_zero, add_zero, mul_one]

theorem det_fderiv_radial_of_zeroHomogeneous
    {a : E → ℝ} {a' : E →L[ℝ] ℝ} {x : E} (ha : HasFDerivAt a a' x)
    (hscale : ∀ t : ℝ, 0 < t → a (t • x) = a x) (hpos : 0 < a x) :
    (fderiv ℝ (fun z => a z • z) x).det = (a x) ^ Module.finrank ℝ E := by
  have hF : HasFDerivAt (fun z => a z • z)
      (a x • ContinuousLinearMap.id ℝ E + a'.smulRight x) x :=
    ha.fun_smul (hasFDerivAt_id x)
  rw [hF.fderiv]
  exact det_posScalar_id_add_smulRight (a x) hpos.ne' a' x
    (derivative_zeroHomogeneous_apply_self ha hscale)

theorem det_fderiv_radial_pos
    {a : E → ℝ} {a' : E →L[ℝ] ℝ} {x : E} (ha : HasFDerivAt a a' x)
    (hscale : ∀ t : ℝ, 0 < t → a (t • x) = a x) (hpos : 0 < a x) :
    0 < (fderiv ℝ (fun z => a z • z) x).det := by
  rw [det_fderiv_radial_of_zeroHomogeneous ha hscale hpos]
  exact pow_pos hpos _

end BanachIsometric
