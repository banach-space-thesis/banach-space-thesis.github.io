import ThesisCommon.Analysis.SupRowOperators

/-! Uniformly bounded rows that converge strongly to zero define a bounded
c0-valued operator. Their operator norms need not tend to zero. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def cZeroStrongRowValue (F : ℕ → Y →L[𝕜] X)
    (hzero : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 0)) (x : Y) : CZeroSum X where
  toFun n := F n x
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    exact hzero x

def cZeroStrongRows (F : ℕ → Y →L[𝕜] X) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, ‖F n‖ ≤ C) (hzero : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Y →L[𝕜] CZeroSum X :=
  LinearMap.mkContinuous
    { toFun := cZeroStrongRowValue F hzero
      map_add' := by
        intro x y
        ext n
        change F n (x+y) = F n x + F n y
        exact map_add _ _ _
      map_smul' := by
        intro a x
        ext n
        change F n (a • x) = a • F n x
        exact map_smul _ _ _ }
    C (fun x => (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg x))).mpr
      (fun n => ((F n).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg x))))

@[simp] theorem cZeroStrongRows_apply (F : ℕ → Y →L[𝕜] X) (C : ℝ) (hC hbound hzero)
    (x : Y) (n : ℕ) : cZeroStrongRows F C hC hbound hzero x n = F n x := rfl

theorem norm_cZeroStrongRows_le (F : ℕ → Y →L[𝕜] X) (C : ℝ) (hC hbound hzero) :
    ‖cZeroStrongRows F C hC hbound hzero‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

end ThesisCommon
