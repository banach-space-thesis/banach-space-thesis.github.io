import Posets.ProductQuotientCZero
import Posets.ProductQuotientTransport
import PosetsCommon.CZeroSumFiniteEquiv

/-! Full matrix and full c₀-operator factors in the product theorem. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon TopologicalSpace
open scoped ZeroAtInfty
namespace Posets

variable {𝕜 C X : Type} [RCLike 𝕜]
  [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (hX : ¬ SeparableSpace X) (hfew : JFA.HasFewOperators 𝕜 X)

include hX hfew

theorem exists_productRepresentedCZero_strongSplit
    {D : Type} [TopologicalSpace D] [DiscreteTopology D] [Countable D]
    (hc : RepresentedBy 𝕜 C C₀(D, 𝕜) Set.univ) :
    ∃ θ : BoundedHom 𝕜
      (DependentCZeroSum 𝕜 (fun _ : D => X) →L[𝕜] DependentCZeroSum 𝕜 (fun _ : D => X)) C,
    ∃ ρ : BoundedHom 𝕜 C
      (DependentCZeroSum 𝕜 (fun _ : D => X) →L[𝕜] DependentCZeroSum 𝕜 (fun _ : D => X)),
      StrongSplit 𝕜 (DependentCZeroSum 𝕜 (fun _ : D => X)) C θ ρ ∧
        Isometry ρ ∧ ‖θ.toContinuousLinearMap‖ ≤ 1 := by
  obtain ⟨θ, ρ, hsplit, hρ, hθ⟩ := exists_productCZero_strongSplit (D := D) hX hfew
  obtain ⟨c, hc'⟩ := representedBy_univ_coordinates hc
  exact product_strongSplit_coordinates c hc' θ ρ hsplit hρ hθ

theorem exists_productRepresentedFinite_strongSplit
    {D : Type} [Fintype D]
    (hc : RepresentedBy 𝕜 C (D → 𝕜) Set.univ) :
    ∃ θ : BoundedHom 𝕜
      (DependentCZeroSum 𝕜 (fun _ : D => X) →L[𝕜] DependentCZeroSum 𝕜 (fun _ : D => X)) C,
    ∃ ρ : BoundedHom 𝕜 C
      (DependentCZeroSum 𝕜 (fun _ : D => X) →L[𝕜] DependentCZeroSum 𝕜 (fun _ : D => X)),
      StrongSplit 𝕜 (DependentCZeroSum 𝕜 (fun _ : D => X)) C θ ρ ∧
        Isometry ρ ∧ ‖θ.toContinuousLinearMap‖ ≤ 1 := by
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
  obtain ⟨θ, ρ, hsplit, hρ, hθ⟩ := exists_productCZero_strongSplit (D := D) hX hfew
  let e : C₀(D, 𝕜) ≃ₗᵢ[𝕜] (D → 𝕜) :=
    productCZeroSumEquiv.trans (finiteCZeroSumEquiv (fun _ : D => 𝕜))
  obtain ⟨c, hc'⟩ := representedBy_univ_coordinates hc
  let d := c.trans (operatorConjugationIsometry e).symm
  have hd : ∀ a b, d (a * b) = d a * d b := by
    intro a b
    change operatorConjugation e.symm (c (a * b)) =
      operatorConjugation e.symm (c a) * operatorConjugation e.symm (c b)
    rw [hc', operatorConjugation_mul]
  exact product_strongSplit_coordinates d hd θ ρ hsplit hρ hθ

end Posets
