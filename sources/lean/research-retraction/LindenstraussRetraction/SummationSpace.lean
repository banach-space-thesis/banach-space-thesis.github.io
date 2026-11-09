import LindenstraussRetraction.Definitions
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The concrete summation space in Section 4

`FiniteCoordinateSpace 𝕜 m` is the paper's `E_(m+1)`. This indexing keeps
all blocks nonzero and aligns the zero-based Lean index with positive indices
in the manuscript. The norm on `SummationSpace` is the dependent ℓ₁ norm.
-/

noncomputable section

open scoped ZeroAtInfty ENNReal
open Filter Topology

namespace LindenstraussRetraction

universe v
variable (𝕜 : Type v) [RCLike 𝕜]

/-- Scalar sequences tending to zero, with the supremum norm. -/
abbrev C0 := C₀(ℕ, 𝕜)

/-- The first `m+1` coordinate subspace of `c₀`. -/
def finiteCoordinateSubmodule (m : ℕ) : Submodule 𝕜 (C0 𝕜) where
  carrier := {x | ∀ k, m + 1 ≤ k → x k = 0}
  zero_mem' := by intro k hk; rfl
  add_mem' := by
    intro x y hx hy k hk
    simp only [ZeroAtInftyContinuousMap.add_apply, hx k hk, hy k hk, add_zero]
  smul_mem' := by
    intro c x hx k hk
    simp only [ZeroAtInftyContinuousMap.smul_apply, hx k hk, smul_zero]

abbrev FiniteCoordinateSpace (m : ℕ) : Type v := finiteCoordinateSubmodule 𝕜 m

/-- Restrict a finite-coordinate vector to its potentially nonzero entries. -/
def finiteCoordinateRestriction (m : ℕ) :
    FiniteCoordinateSpace 𝕜 m →ₗ[𝕜] (Fin (m+1) → 𝕜) where
  toFun x i := x.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finiteCoordinateRestriction_injective (m : ℕ) :
    Function.Injective (finiteCoordinateRestriction 𝕜 m) := by
  intro x y h
  apply Subtype.ext
  apply ZeroAtInftyContinuousMap.ext
  intro k
  by_cases hk : k < m+1
  · exact congrFun h ⟨k, hk⟩
  · rw [x.property k (Nat.le_of_not_gt hk), y.property k (Nat.le_of_not_gt hk)]

instance finiteCoordinateSpace_finiteDimensional (m : ℕ) :
    FiniteDimensional 𝕜 (FiniteCoordinateSpace 𝕜 m) :=
  FiniteDimensional.of_injective (finiteCoordinateRestriction 𝕜 m)
    (finiteCoordinateRestriction_injective 𝕜 m)

instance finiteCoordinateSpace_complete (m : ℕ) :
    CompleteSpace (FiniteCoordinateSpace 𝕜 m) :=
  FiniteDimensional.complete 𝕜 _

/-- `Y = (⊕ E_m)_ℓ₁` from Section 4. -/
abbrev SummationSpace : Type v := lp (FiniteCoordinateSpace 𝕜) 1

theorem summationSpace_hasSum_norm (u : SummationSpace 𝕜) :
    HasSum (fun m => ‖u m‖) ‖u‖ := by
  simpa using lp.hasSum_norm (E := FiniteCoordinateSpace 𝕜) (p := (1 : ℝ≥0∞))
    (by norm_num) u

theorem summationSpace_summable (u : SummationSpace 𝕜) :
    Summable (fun m => (u m).val) := by
  apply Summable.of_norm
  exact (summationSpace_hasSum_norm 𝕜 u).summable

/-- The summation operator, before bundling its continuity. -/
def summationLinear : SummationSpace 𝕜 →ₗ[𝕜] C0 𝕜 where
  toFun u := ∑' m, (u m).val
  map_add' u v := by
    change (∑' m, ((u m).val + (v m).val)) = _
    exact (summationSpace_summable 𝕜 u).tsum_add (summationSpace_summable 𝕜 v)
  map_smul' c u := by
    change (∑' m, c • (u m).val) = c • ∑' m, (u m).val
    exact (summationSpace_summable 𝕜 u).tsum_const_smul c

theorem summationLinear_norm_le (u : SummationSpace 𝕜) :
    ‖summationLinear 𝕜 u‖ ≤ ‖u‖ := by
  calc
    ‖summationLinear 𝕜 u‖ ≤ ∑' m, ‖(u m).val‖ :=
      norm_tsum_le_tsum_norm (summationSpace_hasSum_norm 𝕜 u).summable
    _ = ‖u‖ := (summationSpace_hasSum_norm 𝕜 u).tsum_eq

/-- The paper's `Q : Y → c₀`, with its norm bound established. -/
def summationOperator : SummationSpace 𝕜 →L[𝕜] C0 𝕜 :=
  (summationLinear 𝕜).mkContinuous 1 (fun u => by
    simpa only [one_mul] using summationLinear_norm_le 𝕜 u)

@[simp] theorem summationOperator_apply (u : SummationSpace 𝕜) :
    summationOperator 𝕜 u = ∑' m, (u m).val := rfl

theorem norm_summationOperator_le : ‖summationOperator 𝕜‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using summationLinear_norm_le 𝕜 u

end LindenstraussRetraction
