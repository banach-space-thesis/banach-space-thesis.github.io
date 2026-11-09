import NonCalkinAlgebra.CompletedAFSystem
import NonCalkinAlgebra.TraceCoefficientSelection
import Mathlib.Analysis.Normed.Operator.Completeness

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.NormedStarDirectLimit
open UniformSpace
open scoped NonCalkinAlgebra.NormedStarCompletion

universe u v
variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {A : ι → Type v} [∀ i, NormedRing (A i)] [∀ i, NormedAlgebra ℂ (A i)]
variable [∀ i, StarRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
variable [DirectedSystem A (f · · ·)] [PreservesNorm f]

variable (τ : ∀ i, A i →ₗ[ℂ] ℂ)
variable (hcompat : ∀ i j hij x, τ j (f i j hij x) = τ i x)
variable (hbound : ∀ i x, ‖τ i x‖ ≤ ‖x‖)

def traceOnLimit : Carrier f →L[ℂ] ℂ :=
  (DirectLimit.Module.lift ℂ ι A f τ hcompat).mkContinuous 1
    (DirectLimit.induction f fun i x => by simpa only [one_mul] using hbound i x)

/-- A compatible contractive family of traces extends to the completed direct limit. -/
def traceOnCompletion : Completed f →L[ℂ] ℂ :=
  (traceOnLimit f τ hcompat hbound).extend Completion.toComplL
    Completion.denseRange_coe (Completion.isUniformInducing_coe _)

@[simp] theorem traceOnCompletion_of (i : ι) (x : A i) :
    traceOnCompletion f τ hcompat hbound (of f i x : Completed f) = τ i x :=
  ContinuousLinearMap.extend_eq _ _ _ _ _

theorem traceOnCompletion_normalized (h1 : ∀ i, τ i 1 = 1)
    (hmul : ∀ i x y, τ i (x * y) = τ i (y * x)) :
    IsNormalizedTrace (traceOnCompletion f τ hcompat hbound) := by
  let L := traceOnCompletion f τ hcompat hbound
  constructor
  · let i : ι := Classical.arbitrary ι
    change L (↑(1 : Carrier f)) = 1
    rw [one_def f i]
    exact (traceOnCompletion_of f τ hcompat hbound i 1).trans (h1 i)
  · intro a b
    refine Completion.induction_on₂ a b
      (isClosed_eq (L.continuous.comp continuous_mul)
        (L.continuous.comp (continuous_snd.mul continuous_fst))) ?_
    intro a' b'
    let coe (z : DirectLimit A f) : Completed f := ((show Carrier f from z) : Completed f)
    refine DirectLimit.induction₂ f
      (C := fun x y => L (coe x * coe y) = L (coe y * coe x)) ?_ a' b'
    intro i x y
    change L ((of f i x : Completed f) * (of f i y : Completed f)) =
      L ((of f i y : Completed f) * (of f i x : Completed f))
    rw [← Completion.coe_mul, ← Completion.coe_mul, mul_of, mul_of]
    exact (traceOnCompletion_of f τ hcompat hbound i (x * y)).trans
      ((hmul i x y).trans (traceOnCompletion_of f τ hcompat hbound i (y * x)).symm)

end NonCalkinAlgebra.NormedStarDirectLimit
