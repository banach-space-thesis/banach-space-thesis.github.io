import BanachIsometric.QuaternionicGluing
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Quaternionic functional and normed targets

These are the quaternionic assertions of Theorem A and Corollary B. They are
target proposition definitions, not proofs of those assertions. Right vector
spaces are encoded by modules over the opposite quaternion algebra. The
Hermitian conclusions use that same original right action.

The scalar action's norm compatibility is expressed by `NormSMulClass`, since
Mathlib's `NormedSpace` requires a commutative normed field and cannot be used
with the quaternions. No RCLike or complex-linearity assumption is imposed.
-/

namespace BanachIsometric
namespace Quaternionic

open scoped Quaternion NNReal

variable {E : Type*} [AddCommGroup E] [Module Hᵐᵒᵖ E]

/-- Nonnegative definite functions absolutely homogeneous for the original
right quaternionic scalar action, without any triangle inequality. -/
structure IsDefiniteHomogeneous (p : E → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  eq_zero_iff : ∀ x, p x = 0 ↔ x = 0
  right_mul : ∀ x a, p (rightMul x a) = p x * ‖a‖

/-- Section equivalences are real-linear bijections; their right quaternionic
linearity is not required. The restricted real actions are canonical. -/
def RealEquivalentSections (n : ℕ) (p : E → ℝ) : Prop :=
  ∀ Y Z : Submodule Hᵐᵒᵖ E,
    Module.rank Hᵐᵒᵖ Y = (n : Cardinal) → Module.rank Hᵐᵒᵖ Z = (n : Cardinal) →
    ∃ T : RestrictScalars ℝ Hᵐᵒᵖ Y ≃ₗ[ℝ] RestrictScalars ℝ Hᵐᵒᵖ Z,
      ∀ x : Y, p ((RestrictScalars.addEquiv ℝ Hᵐᵒᵖ Z) (T x) : E) = p x.val

/-- The local regularity hypothesis uses arbitrary real Euclidean coordinates
of real dimension `4 * (n+1)` on each right `(n+1)`-dimensional subspace. -/
def SphereLipschitz (n : ℕ) (p : E → ℝ) : Prop :=
  ∀ Y : Submodule Hᵐᵒᵖ E, Module.rank Hᵐᵒᵖ Y = ((n + 1 : ℕ) : Cardinal) →
    ∃ e : EuclideanSpace ℝ (Fin (4 * (n + 1))) ≃ₗ[ℝ] RestrictScalars ℝ Hᵐᵒᵖ Y,
      ∃ C : ℝ≥0, LipschitzOnWith C
        (fun v => p ((RestrictScalars.addEquiv ℝ Hᵐᵒᵖ Y) (e v) : E)) (Metric.sphere 0 1)

/-- The full quaternionic assertion of Theorem A, as an unproved target. -/
def FunctionalStatement : Prop :=
  ∀ (n : ℕ) (p : E → ℝ), 2 ≤ n → (n : Cardinal) < Module.rank Hᵐᵒᵖ E →
    IsDefiniteHomogeneous p → SphereLipschitz n p → RealEquivalentSections n p →
      HasHermitianSquare p

section Normed

variable {V : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V]

/-- The quaternionic metric hypothesis includes surjectivity, and imposes no
linearity or requirement to fix the origin. -/
def MetricSubspaceHomogeneity (n : ℕ) : Prop :=
  ∀ Y Z : Submodule Hᵐᵒᵖ V,
    Module.rank Hᵐᵒᵖ Y = (n : Cardinal) → Module.rank Hᵐᵒᵖ Z = (n : Cardinal) →
      Nonempty (Y ≃ᵢ Z)

/-- The quaternionic norm-inducing assertion of Corollary B for the specified
dimension. Completeness is not required. This is an unproved target. -/
def NormedCorollaryBAt [NormSMulClass Hᵐᵒᵖ V] (n : ℕ) : Prop :=
  2 ≤ n → (n : Cardinal) < Module.rank Hᵐᵒᵖ V →
    MetricSubspaceHomogeneity (V := V) n → HasHermitianSquare (norm : V → ℝ)

/-- Quaternionic norms satisfy the exact algebraic hypotheses of Theorem A.
The scalar compatibility of the given norm is explicit in `NormSMulClass`. -/
theorem norm_isDefiniteHomogeneous [NormSMulClass Hᵐᵒᵖ V] :
    IsDefiniteHomogeneous (norm : V → ℝ) where
  nonneg := norm_nonneg
  eq_zero_iff := fun _ => norm_eq_zero
  right_mul := fun x a => by simpa [rightMul, mul_comm] using norm_smul (MulOpposite.op a) x

end Normed

end Quaternionic
end BanachIsometric
