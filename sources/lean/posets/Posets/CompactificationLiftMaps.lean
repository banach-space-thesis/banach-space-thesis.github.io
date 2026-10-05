import Posets.AutomaticContinuity
import PosetsCommon.CountableCZero
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section
open Filter Topology
open scoped ZeroAtInfty OnePoint
namespace Posets

variable {𝕜 : Type} [RCLike 𝕜]
variable (K : Type) [TopologicalSpace K] [T2Space K]

/-- Extension by zero to the point at infinity. -/
def compactificationInclusion : C₀(K, 𝕜) →L[𝕜] C(OnePoint K, 𝕜) :=
  (ThesisCommon.cZeroAtInfinityIsometry K).toContinuousLinearMap

@[simp] theorem compactificationInclusion_coe (f : C₀(K, 𝕜)) (x : K) :
    compactificationInclusion K f (x : OnePoint K) = f x := rfl

@[simp] theorem compactificationInclusion_infty (f : C₀(K, 𝕜)) :
    compactificationInclusion K f ∞ = 0 := rfl

/-- Subtract the value at infinity before restricting to the original space. -/
def compactificationProjectionValue (f : C(OnePoint K, 𝕜)) : C₀(K, 𝕜) where
  toFun x := f (x : OnePoint K) - f ∞
  continuous_toFun := (f.continuous.comp OnePoint.continuous_coe).sub continuous_const
  zero_at_infty' := by
    have h := (f.continuous.tendsto ∞).comp (OnePoint.tendsto_coe_infty (X := K))
    simpa only [coclosedCompact_eq_cocompact, sub_self] using h.sub_const (f ∞)

def compactificationProjection : C(OnePoint K, 𝕜) →L[𝕜] C₀(K, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := compactificationProjectionValue K
      map_add' := by intro f g; ext x; change (f _ + g _) - (f _ + g _) = _; simp [compactificationProjectionValue]; ring
      map_smul' := by intro a f; ext x; exact (smul_sub a (f (x : OnePoint K)) (f ∞)).symm }
    2 (by
      intro f
      apply (BoundedContinuousFunction.norm_le (by positivity : 0 ≤ 2 * ‖f‖)).mpr
      intro x
      change ‖f (x : OnePoint K) - f ∞‖ ≤ 2 * ‖f‖
      calc
        _ ≤ ‖f (x : OnePoint K)‖ + ‖f ∞‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
        _ = 2 * ‖f‖ := by ring)

@[simp] theorem compactificationProjection_apply (f : C(OnePoint K, 𝕜)) (x : K) :
    compactificationProjection K f x = f (x : OnePoint K) - f ∞ := rfl

@[simp] theorem compactificationProjection_inclusion :
    (compactificationProjection (𝕜 := 𝕜) K).comp (compactificationInclusion K) =
      ContinuousLinearMap.id 𝕜 C₀(K, 𝕜) := by
  ext f x
  simp

theorem compactification_decomposition (f : C(OnePoint K, 𝕜)) :
    compactificationInclusion K (compactificationProjection K f) +
      f ∞ • (1 : C(OnePoint K, 𝕜)) = f := by
  ext x
  cases x with
  | infty => simp
  | coe x => simp

end Posets
