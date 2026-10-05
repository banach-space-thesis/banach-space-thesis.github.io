import ThesisCommon.Analysis.FiniteCoefficientAbsorption

/-! Finite coefficient powers are absorbed by an infinite outer index set.
The coefficient space is arbitrary: no finite-dimensionality or factorization
property is assumed. The maps use the actual product norms and sum norms. -/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def finitePowerLpEquiv (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (Fin n → X) ≃L[𝕜] lp (fun _ : Fin n => X) p :=
  (PiLp.continuousLinearEquiv p 𝕜 (fun _ : Fin n => X)).symm.trans
    (lpPiLpₗᵢ (fun _ : Fin n => X) 𝕜 (p := p)).symm.toContinuousLinearEquiv

def lpFinitePowerAbsorptionEquiv [Infinite Γ] (n : ℕ) (hn : 0 < n)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) :
    lp (fun _ : Γ => Fin n → X) p ≃L[𝕜] lp (fun _ : Γ => X) p :=
  (lpMapEquiv p (finitePowerLpEquiv (𝕜 := 𝕜) (X := X) n p)).trans
    (lpProductFlattenIsometry (𝕜 := 𝕜) p hp
      (infiniteFiniteProductEquiv Γ n hn)).toContinuousLinearEquiv

def cZeroFinitePowerAbsorptionEquiv [Infinite Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ] (n : ℕ) (hn : 0 < n) :
    C₀(Γ, Fin n → X) ≃L[𝕜] C₀(Γ, X) :=
  (cZeroMapEquiv (ι := Γ)
    (finiteFunctionCZeroIsometry (𝕜 := 𝕜) (X := X) (Fin n)).toContinuousLinearEquiv).trans
    (cZeroProductFlattenIsometry (𝕜 := 𝕜) (X := X)
      (infiniteFiniteProductEquiv Γ n hn)).toContinuousLinearEquiv

end ThesisCommon
