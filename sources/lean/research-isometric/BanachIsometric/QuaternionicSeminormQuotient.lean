import BanachIsometric.QuaternionicCompletion
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.LinearAlgebra.Isomorphisms

/-! Genuine normed quotients of right-quaternionic seminorms. The norm is
constructed from the specified real seminorm; its original Hopp action
descends through the stable kernel and extends to the Banach completion. -/

namespace BanachIsometric.Quaternionic

open UniformSpace

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]

/-- A real seminorm with the original absolute right-quaternionic scaling. -/
structure RightSeminorm (X : Type*) [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X] where
  toRealSeminorm : Seminorm ℝ X
  right_mul : ∀ x a, toRealSeminorm (rightMul x a) = toRealSeminorm x * ‖a‖

instance : CoeFun (RightSeminorm X) (fun _ => X → ℝ) := ⟨fun p => p.toRealSeminorm⟩

def SeminormModel (_p : RightSeminorm X) : Type _ := X

instance (p : RightSeminorm X) : AddCommGroup (SeminormModel p) := inferInstanceAs (AddCommGroup X)
instance (p : RightSeminorm X) : Module Hᵐᵒᵖ (SeminormModel p) := inferInstanceAs (Module Hᵐᵒᵖ X)
instance (p : RightSeminorm X) : Module ℝ (SeminormModel p) := inferInstanceAs (Module ℝ X)
instance (p : RightSeminorm X) [IsScalarTower ℝ Hᵐᵒᵖ X] : IsScalarTower ℝ Hᵐᵒᵖ (SeminormModel p) :=
  inferInstanceAs (IsScalarTower ℝ Hᵐᵒᵖ X)

instance (p : RightSeminorm X) : SeminormedAddCommGroup (SeminormModel p) :=
  p.toRealSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup

instance (p : RightSeminorm X) : NormedSpace ℝ (SeminormModel p) where
  norm_smul_le a x := (map_smul_eq_mul p.toRealSeminorm a x).le

instance (p : RightSeminorm X) : NormSMulClass Hᵐᵒᵖ (SeminormModel p) where
  norm_smul a x := by
    change p (rightMul (x : X) a.unop) = ‖a.unop‖ * p x
    rw [p.right_mul, mul_comm]

instance (p : RightSeminorm X) : UniformContinuousConstSMul Hᵐᵒᵖ (SeminormModel p) where
  uniformContinuous_const_smul a := (lipschitzWith_smul a).uniformContinuous

@[simp] theorem norm_seminormModel (p : RightSeminorm X) (x : SeminormModel p) : ‖x‖ = p x := rfl

def toSeminormModel (p : RightSeminorm X) : X ≃ₗ[Hᵐᵒᵖ] SeminormModel p := LinearEquiv.refl _ _

abbrev SeminormQuotient (p : RightSeminorm X) := SeparationQuotient (SeminormModel p)

instance (p : RightSeminorm X) : NormSMulClass Hᵐᵒᵖ (SeminormQuotient p) where
  norm_smul a x := by
    refine Quotient.inductionOn x ?_
    intro v
    simpa only [← SeparationQuotient.mk_smul, SeparationQuotient.norm_mk] using
      (norm_smul a v)

def seminormQuotientMap (p : RightSeminorm X) : X →ₗ[Hᵐᵒᵖ] SeminormQuotient p :=
  (SeparationQuotient.mkCLM Hᵐᵒᵖ (SeminormModel p)).toLinearMap.comp (toSeminormModel p).toLinearMap

@[simp] theorem seminormQuotientMap_norm (p : RightSeminorm X) (x : X) :
    ‖seminormQuotientMap p x‖ = p x := rfl

theorem seminormQuotientMap_surjective (p : RightSeminorm X) :
    Function.Surjective (seminormQuotientMap p) := by
  change Function.Surjective (SeparationQuotient.mk : SeminormModel p → SeminormQuotient p)
  exact SeparationQuotient.surjective_mk

def seminormKernel (p : RightSeminorm X) : Submodule Hᵐᵒᵖ X := LinearMap.ker (seminormQuotientMap p)

@[simp] theorem mem_seminormKernel (p : RightSeminorm X) (x : X) : x ∈ seminormKernel p ↔ p x = 0 := by
  change seminormQuotientMap p x = 0 ↔ p x = 0
  rw [← norm_eq_zero, seminormQuotientMap_norm]

def seminormQuotientEquiv (p : RightSeminorm X) :
    (X ⧸ seminormKernel p) ≃ₗ[Hᵐᵒᵖ] SeminormQuotient p :=
  (seminormQuotientMap p).quotKerEquivOfSurjective (seminormQuotientMap_surjective p)

@[simp] theorem seminormQuotientEquiv_mk_norm (p : RightSeminorm X) (x : X) :
    ‖seminormQuotientEquiv p (Submodule.Quotient.mk x)‖ = p x := rfl

abbrev SeminormCompletion (p : RightSeminorm X) := Completion (SeminormQuotient p)

def seminormCompletionMap (p : RightSeminorm X) : X →ₗ[Hᵐᵒᵖ] SeminormCompletion p :=
  (completionEmbedding (V := SeminormQuotient p)).toLinearMap.comp (seminormQuotientMap p)

@[simp] theorem seminormCompletionMap_norm (p : RightSeminorm X) (x : X) :
    ‖seminormCompletionMap p x‖ = p x := by
  change ‖((seminormQuotientMap p x : SeminormQuotient p) : SeminormCompletion p)‖ = p x
  rw [Completion.norm_coe, seminormQuotientMap_norm]

theorem seminormCompletionMap_denseRange (p : RightSeminorm X) : DenseRange (seminormCompletionMap p) := by
  apply (Completion.denseRange_coe : DenseRange ((↑) : SeminormQuotient p → SeminormCompletion p)).mono
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := seminormQuotientMap_surjective p y
  exact ⟨x, rfl⟩

end
end BanachIsometric.Quaternionic
