import ThesisCommon.Analysis.GowersMaureySpace
import ThesisCommon.Analysis.PrimaryIdeal
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.SetTheory.Cardinal.Continuum

/-! Genuine operator predicates and quotient specifications for the prime
shift-generated Gowers--Maurey space. These are theorem targets, not
assumptions in the construction of the space. The quotient target uses its
actual quotient norm and spells out convolution coordinate by coordinate.
This avoids treating Laurent Toeplitz representatives as a subalgebra
under ordinary operator composition (they are not such a subalgebra).
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- No restriction to an infinite-dimensional subspace is bounded below. -/
def IsStrictlySingularOperator (T : X →L[𝕜] X) : Prop :=
  ∀ E : Submodule 𝕜 X,
    (∃ c : ℝ, 0 < c ∧ ∀ x : E, c * ‖x‖ ≤ ‖T x.val‖) → FiniteDimensional 𝕜 E

/-- Every infinite-dimensional complemented subspace is isomorphic to X. -/
def IsPrimeBanachSpace (𝕜 : Type*) [RCLike 𝕜] (X : Type*)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∀ P : X →L[𝕜] X, P.comp P = P →
    ¬ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap) →
      Nonempty (X ≃L[𝕜] LinearMap.range P.toLinearMap)

/-- A two-sided operator ideal is also an actual scalar submodule. -/
def operatorIdealSubmodule (J : TwoSidedIdeal (X →L[𝕜] X)) :
    Submodule 𝕜 (X →L[𝕜] X) where
  carrier := J
  zero_mem' := J.zero_mem
  add_mem' := J.add_mem
  smul_mem' c T hT := by
    have h := J.mul_mem_left (c • ContinuousLinearMap.id 𝕜 X) T hT
    have heq : (c • ContinuousLinearMap.id 𝕜 X) * T = c • T := by
      ext x
      simp
    rwa [heq] at h

@[simp] theorem mem_operatorIdealSubmodule
    (J : TwoSidedIdeal (X →L[𝕜] X)) (T : X →L[𝕜] X) :
    T ∈ operatorIdealSubmodule J ↔ T ∈ J := Iff.rfl

/-- The actual absolutely summable scalar sequence space on the additive integers. -/
abbrev WienerSequences (𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ℤ => 𝕜) 1

/-- Literal convolution coefficients. The quotient target below asserts
that these coefficients are those of the image of the product. -/
def wienerConvolutionCoordinate (a b : WienerSequences 𝕜) (n : ℤ) : 𝕜 :=
  ∑' k : ℤ, a k * b (n - k)

/-- A Banach-algebra quotient identification: the ideal carrier is exactly
the genuinely strictly singular operators, it is closed, the map is a
bounded linear equivalence for the quotient norm, and it preserves the
unit and the actual convolution multiplication. All clauses are goals. -/
def HasStrictlySingularWienerQuotient (𝕜 : Type*) [RCLike 𝕜] (X : Type*)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∃ J : TwoSidedIdeal (X →L[𝕜] X),
    (∀ T, T ∈ J ↔ IsStrictlySingularOperator T) ∧
    ∃ hclosed : IsClosed (operatorIdealSubmodule J : Set (X →L[𝕜] X)),
      letI : IsClosed (operatorIdealSubmodule J : Set (X →L[𝕜] X)) := hclosed
      ∃ e : ((X →L[𝕜] X) ⧸ operatorIdealSubmodule J) ≃L[𝕜] WienerSequences 𝕜,
        e ((operatorIdealSubmodule J).mkQ (ContinuousLinearMap.id 𝕜 X)) = lp.single 1 0 1 ∧
        ∀ S T n, e ((operatorIdealSubmodule J).mkQ (S.comp T)) n =
          wienerConvolutionCoordinate
            (e ((operatorIdealSubmodule J).mkQ S)) (e ((operatorIdealSubmodule J).mkQ T)) n

def AllMaximalIdealsContainStrictlySingular (𝕜 : Type*) [RCLike 𝕜] (X : Type*)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∀ J : TwoSidedIdeal (X →L[𝕜] X), IsCoatom J →
    ∀ T, IsStrictlySingularOperator T → T ∈ J

def HasContinuumManyMaximalOperatorIdeals (𝕜 : Type*) [RCLike 𝕜] (X : Type*)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  Cardinal.mk {J : TwoSidedIdeal (X →L[𝕜] X) // IsCoatom J} = Cardinal.continuum

end ThesisCommon
