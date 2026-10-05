import JFA.FiniteCZeroTensor
import JFA.TensorCancellation
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Positive finite powers of the few-operator space have distinct isomorphism
types. Tensor cancellation reduces any isomorphism to the finite-dimensional
scalar powers, and their dimensions recover the exponent. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace
namespace JFA
universe u
variable {𝕜 : Type u} [RCLike 𝕜] {X : Type u}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem finitePower_isomorphic_iff (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (m n : ℕ) : Isomorphic 𝕜 (Fin m → X) (Fin n → X) ↔ m = n := by
  constructor
  · rintro ⟨e⟩
    have hTensor : Isomorphic 𝕜 (InjectiveTensor 𝕜 (Fin m → 𝕜) X)
        (InjectiveTensor 𝕜 (Fin n → 𝕜) X) :=
      ⟨(finitePowerTensorEquiv (𝕜 := 𝕜) (D := Fin m) (X := X)).trans
        (e.trans (finitePowerTensorEquiv (𝕜 := 𝕜) (D := Fin n) (X := X)).symm)⟩
    have hScalar := (corollary_1_2 (𝕜 := 𝕜) (E := Fin m → 𝕜)
      (F := Fin n → 𝕜) (X := X) (inferInstance : SeparableSpace (Fin m → 𝕜))
      (inferInstance : SeparableSpace (Fin n → 𝕜)) hX hfew).mp hTensor
    obtain ⟨f⟩ := hScalar
    simpa only [Module.finrank_fin_fun] using f.toLinearEquiv.finrank_eq
  · intro h
    subst n
    exact ⟨ContinuousLinearEquiv.refl 𝕜 _⟩

end JFA
