import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Uniformly bounded operators on arbitrary dependent families of Banach
spaces assemble to an actual operator on their ell-one sum. -/
noncomputable section
open scoped ENNReal Classical
namespace ThesisCommon
variable {𝕜 I : Type*} [RCLike 𝕜] {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

theorem lpOneFamily_hasSum_norm (x : lp E 1) : HasSum (fun i => ‖x i‖) ‖x‖ := by
  simpa only [ENNReal.toReal_one, Real.rpow_one] using
    lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) x

theorem summable_norm_lpOneFamily_operators (A : ∀ i, E i →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (x : lp E 1) :
    Summable (fun i => ‖A i (x i)‖) := by
  apply ((lpOneFamily_hasSum_norm x).summable.mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro i
  exact ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))

theorem norm_tsum_lpOneFamily_operators_le (A : ∀ i, E i →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (x : lp E 1) :
    ‖∑' i, A i (x i)‖ ≤ C * ‖x‖ := by
  have hnorm := summable_norm_lpOneFamily_operators A C hC hA x
  calc
    ‖∑' i, A i (x i)‖ ≤ ∑' i, ‖A i (x i)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, C * ‖x i‖ := hnorm.tsum_le_tsum
      (fun i => ((A i).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _)))
      ((lpOneFamily_hasSum_norm x).summable.mul_left C)
    _ = C * ‖x‖ := ((lpOneFamily_hasSum_norm x).mul_left C).tsum_eq

def lpOneFamilyOperator (A : ∀ i, E i →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) : lp E 1 →L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, A i (x i)
      map_add' := by
        intro x y
        simp only [lp.coeFn_add, Pi.add_apply, map_add]
        exact (summable_norm_lpOneFamily_operators A C hC hA x).of_norm.tsum_add
          (summable_norm_lpOneFamily_operators A C hC hA y).of_norm
      map_smul' := by
        intro c x
        simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
        exact Summable.tsum_const_smul c
          (summable_norm_lpOneFamily_operators A C hC hA x).of_norm }
    C (norm_tsum_lpOneFamily_operators_le A C hC hA)

theorem lpOneFamilyOperator_apply (A : ∀ i, E i →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (x : lp E 1) :
    lpOneFamilyOperator A C hC hA x = ∑' i, A i (x i) := rfl

theorem norm_lpOneFamilyOperator_le (A : ∀ i, E i →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) :
    ‖lpOneFamilyOperator A C hC hA‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

theorem lpOneFamilyOperator_single (A : ∀ i, E i →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (i : I) (x : E i) :
    lpOneFamilyOperator A C hC hA (lp.single 1 i x) = A i x := by
  classical
  rw [lpOneFamilyOperator_apply, tsum_eq_single i]
  · rw [lp.single_apply_self]
  · intro j hji
    rw [lp.single_apply_ne 1 i x hji, map_zero]

theorem lpOneFamilyOperator_comp_single (A : ∀ i, E i →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (i : I) :
    (lpOneFamilyOperator A C hC hA).comp (lp.singleContinuousLinearMap 𝕜 E 1 i) = A i := by
  ext x
  exact lpOneFamilyOperator_single A C hC hA i x

theorem lpOneFamilyOperator_unique (A : ∀ i, E i →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (T : lp E 1 →L[𝕜] F)
    (hT : ∀ i, T.comp (lp.singleContinuousLinearMap 𝕜 E 1 i) = A i) :
    T = lpOneFamilyOperator A C hC hA := by
  apply lp.ext_continuousLinearMap (by norm_num : (1 : ENNReal) ≠ ⊤)
  intro i
  rw [hT, lpOneFamilyOperator_comp_single]

end ThesisCommon
