import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.Topology.Algebra.Order.Field

/-! Form bounded sequence-valued operators from their actual coordinate maps.
For c₀, vanishing of the row norms proves the output is a null sequence.
-/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Bounded rows define an operator into the actual bounded-sequence space. -/
def infinityRows (F : ℕ → Y →L[𝕜] X) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n, ‖F n‖ ≤ C) : Y →L[𝕜] EllInfinitySum X :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => F n x, memℓp_infty ⟨C * ‖x‖, by
        rintro _ ⟨n, rfl⟩
        exact ((F n).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hF n) (norm_nonneg x))⟩⟩
      map_add' := by intros; ext n; exact map_add _ _ _
      map_smul' := by intros; ext n; exact map_smul _ _ _ }
    C (fun x => lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg x)) fun n =>
      ((F n).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hF n) (norm_nonneg x)))

@[simp] theorem infinityRows_apply (F : ℕ → Y →L[𝕜] X) (C : ℝ) (hC hF) (x : Y) (n : ℕ) :
    infinityRows F C hC hF x n = F n x := rfl

theorem norm_infinityRows_le (F : ℕ → Y →L[𝕜] X) (C : ℝ) (hC hF) :
    ‖infinityRows F C hC hF‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

/-- Rows with norms tending to zero send every vector to a null sequence. -/
def cZeroRowValue (F : ℕ → Y →L[𝕜] X)
    (hF : Tendsto (fun n => ‖F n‖) atTop (𝓝 0)) (x : Y) : CZeroSum X where
  toFun n := F n x
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    exact squeeze_zero_norm (fun n => (F n).le_opNorm x)
      (by simpa using hF.mul_const ‖x‖)

/-- Uniform bounds and vanishing row norms define an operator into c₀. -/
def cZeroRows (F : ℕ → Y →L[𝕜] X) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, ‖F n‖ ≤ C) (hzero : Tendsto (fun n => ‖F n‖) atTop (𝓝 0)) :
    Y →L[𝕜] CZeroSum X :=
  LinearMap.mkContinuous
    { toFun := cZeroRowValue F hzero
      map_add' := by
        intro x y
        ext n
        change F n (x + y) = F n x + F n y
        exact map_add _ _ _
      map_smul' := by
        intro a x
        ext n
        change F n (a • x) = a • F n x
        exact map_smul _ _ _ }
    C (fun x => (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg x))).mpr
      (fun n => ((F n).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg x))))

@[simp] theorem cZeroRows_apply (F : ℕ → Y →L[𝕜] X) (C : ℝ) (hC hbound hzero)
    (x : Y) (n : ℕ) : cZeroRows F C hC hbound hzero x n = F n x := rfl

theorem norm_cZeroRows_le (F : ℕ → Y →L[𝕜] X) (C : ℝ) (hC hbound hzero) :
    ‖cZeroRows F C hC hbound hzero‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

end ThesisCommon
