import Posets.Definitions

/-! A zero algebra factor can be realized on a separable Banach space. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon TopologicalSpace
namespace Posets

variable {𝕜 X C : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedRing C] [NormedAlgebra 𝕜 C]

def productZeroQuotient : BoundedHom 𝕜 (X →L[𝕜] X) C where
  toContinuousLinearMap := 0
  map_mul' := fun _ _ => by simp

def productZeroSection : BoundedHom 𝕜 C (X →L[𝕜] X) where
  toContinuousLinearMap := 0
  map_mul' := fun _ _ => by simp

theorem productZero_strongSplit [SeparableSpace X] [Subsingleton C] :
    StrongSplit 𝕜 X C productZeroQuotient productZeroSection := by
  refine ⟨fun a => ⟨0, Subsingleton.elim _ _⟩, ?_, fun a => Subsingleton.elim _ _⟩
  intro T
  exact ⟨fun _ => IsSeparable.of_separableSpace _, fun _ => rfl⟩

theorem productZeroSection_isometry [Subsingleton C] :
    Isometry (productZeroSection (𝕜 := 𝕜) (X := X) (C := C)) := by
  apply AddMonoidHomClass.isometry_of_norm
    (productZeroSection (𝕜 := 𝕜) (X := X) (C := C)).toContinuousLinearMap
  intro a
  rw [Subsingleton.elim a 0]
  simp [productZeroSection]

theorem productZeroQuotient_norm :
    ‖(productZeroQuotient (𝕜 := 𝕜) (X := X) (C := C)).toContinuousLinearMap‖ = 0 :=
  norm_zero

end Posets
