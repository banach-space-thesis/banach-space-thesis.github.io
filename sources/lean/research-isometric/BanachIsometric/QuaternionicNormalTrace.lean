import BanachIsometric.QuaternionicHermitianRealGeometry
import BanachIsometric.HermitianCompressionTrace

/-!
# Four real trace contributions of an actual quaternionic normal line

The normal projection is explicitly the sum of the four real rank-one maps
associated with `u,ui,uj,uk`. Every right Hermitian square takes the same value
on these four vectors. The actual compressed trace therefore removes exactly
four copies of the normal vector's diagonal value.
-/

namespace BanachIsometric.Quaternionic

open scoped Quaternion BigOperators

noncomputable section

def quaternionUnits : Fin 4 → H := ![1, i, j, k]

theorem quaternionUnits_normSq (r : Fin 4) : Quaternion.normSq (quaternionUnits r) = 1 := by
  fin_cases r <;> norm_num [quaternionUnits, normSq_i, normSq_j, normSq_k]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module Hᵐᵒᵖ E] [IsScalarTower ℝ Hᵐᵒᵖ E]

def quaternionLineFrame (u : E) (r : Fin 4) : E := rightMul u (quaternionUnits r)

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem quaternionLineFrame_diagonal (Q : HermitianForm E) (u : E) (r : Fin 4) :
    (Q.form (quaternionLineFrame u r) (quaternionLineFrame u r)).re = (Q.form u u).re := by
  rw [quaternionLineFrame, Q.real_self_rightMul, quaternionUnits_normSq, one_mul]

omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem inner_quaternionLineFrame (P : HermitianForm E)
    (hP : ∀ x y, (P.form x y).re = inner ℝ x y) (u v : E) (r : Fin 4) :
    inner ℝ (quaternionLineFrame u r) v =
      ![(P.form u v).re, (P.form u v).imI, (P.form u v).imJ, (P.form u v).imK] r := by
  change inner ℝ (rightMul u (quaternionUnits r)) v = _
  rw [← hP, P.mul_left]
  fin_cases r <;> simp [quaternionUnits, i, j, k, Quaternion.re_mul]

variable [FiniteDimensional Hᵐᵒᵖ E]

local instance : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ Hᵐᵒᵖ E

theorem hermitianNormalPart_eq_sum_rank_one (P : HermitianForm E)
    (hP : ∀ x y, (P.form x y).re = inner ℝ x y) (u : E) :
    (hermitianNormalPart P u).toLinearMap =
      ∑ r : Fin 4, (innerₗ E (quaternionLineFrame u r)).smulRight (quaternionLineFrame u r) := by
  ext v
  change rightMul u (P.form u v) = ∑ r : Fin 4,
    inner ℝ (quaternionLineFrame u r) v • quaternionLineFrame u r
  simp_rw [inner_quaternionLineFrame P hP]
  rw [rightMul_decompose]
  simp [Fin.sum_univ_succ, quaternionLineFrame, quaternionUnits]
  abel

theorem hermitianNormalProjection_eq_id_sub_rank_one (P : HermitianForm E)
    (hP : ∀ x y, (P.form x y).re = inner ℝ x y) (u : E) (hu : ‖u‖ = 1) :
    (realHermitianNormalHyperplane P u).starProjection.toLinearMap = LinearMap.id -
      ∑ r : Fin 4, (innerₗ E (quaternionLineFrame u r)).smulRight (quaternionLineFrame u r) := by
  calc
    _ = LinearMap.id - (hermitianNormalPart P u).toLinearMap :=
      congrArg ContinuousLinearMap.toLinearMap (hermitianNormalProjection_eq_starProjection P hP u hu).symm
    _ = _ := congrArg (fun T => LinearMap.id - T) (hermitianNormalPart_eq_sum_rank_one P hP u)

theorem trace_realHermitianNormalHyperplane (P Q : HermitianForm E)
    (hP : ∀ x y, (P.form x y).re = inner ℝ x y) (u : E) (hu : ‖u‖ = 1) :
    LinearMap.trace ℝ (realHermitianNormalHyperplane P u)
      (hermitianRelativeOperator (restrictSesqForm Q.realBilinear (realHermitianNormalHyperplane P u))) =
      LinearMap.trace ℝ E (hermitianRelativeOperator Q.realBilinear) - 4 * (Q.form u u).re := by
  rw [trace_relativeOperator_restrict_eq_sub_rank_one Q.realBilinear Q.realBilinear_symmetric
    (realHermitianNormalHyperplane P u) (quaternionLineFrame u)
    (hermitianNormalProjection_eq_id_sub_rank_one P hP u hu)]
  simp only [HermitianForm.realBilinear_apply, quaternionLineFrame_diagonal,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

end

end BanachIsometric.Quaternionic
