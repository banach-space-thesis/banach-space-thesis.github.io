import ThesisCommon.Analysis.LpArbitraryProducts
import ThesisCommon.Analysis.CZeroArbitraryProducts
import ThesisCommon.Analysis.SequenceSumEquivs
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual scalar models for infinite-index sums with a nonzero finite-
dimensional coefficient space. No factorization property of the finite-
dimensional coefficient is assumed. -/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def infiniteFiniteProductEquiv (Γ : Type*) [Infinite Γ] (n : ℕ) (hn : 0 < n) :
    Γ × Fin n ≃ Γ := by
  apply Classical.choice
  apply Cardinal.eq.mp
  have hnle : (n : Cardinal) ≤ Cardinal.mk Γ :=
    (Cardinal.nat_lt_aleph0 n).le.trans (Cardinal.aleph0_le_mk Γ)
  have hnzero : (n : Cardinal) ≠ 0 := by exact_mod_cast hn.ne'
  simpa only [Cardinal.mk_prod, Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero] using
    Cardinal.mul_eq_left (Cardinal.aleph0_le_mk Γ) hnle hnzero

def finiteDimensionalLpEquiv [FiniteDimensional 𝕜 X]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    X ≃L[𝕜] lp (fun _ : Fin (Module.finrank 𝕜 X) => 𝕜) p :=
  (Module.finBasis 𝕜 X).equivFunL.trans
    ((PiLp.continuousLinearEquiv p 𝕜 (fun _ : Fin (Module.finrank 𝕜 X) => 𝕜)).symm.trans
      (lpPiLpₗᵢ (fun _ : Fin (Module.finrank 𝕜 X) => 𝕜) 𝕜 (p := p)).symm.toContinuousLinearEquiv)

def lpFiniteCoefficientEquiv [Infinite Γ] [FiniteDimensional 𝕜 X] [Nontrivial X]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) :
    lp (fun _ : Γ => X) p ≃L[𝕜] lp (fun _ : Γ => 𝕜) p :=
  (lpMapEquiv p (finiteDimensionalLpEquiv (𝕜 := 𝕜) (X := X) p)).trans
    (lpProductFlattenIsometry (𝕜 := 𝕜) p hp
      (infiniteFiniteProductEquiv Γ (Module.finrank 𝕜 X) (Module.finrank_pos))).toContinuousLinearEquiv

def finiteFunctionCZeroIsometry (I : Type*) [Fintype I]
    [TopologicalSpace I] [DiscreteTopology I] : (I → X) ≃ₗᵢ[𝕜] C₀(I, X) where
  toFun f := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
    ⟨f, continuous_of_discreteTopology⟩
  invFun f := f
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := by intro f; rfl
  right_inv := by intro f; rfl
  norm_map' := by
    intro f
    let g : C₀(I, X) := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
      ⟨f, continuous_of_discreteTopology⟩
    change ‖g‖ = ‖f‖
    apply le_antisymm
    · apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
      intro i
      exact norm_le_pi_norm f i
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg g)).mpr
      intro i
      exact BoundedContinuousFunction.norm_coe_le_norm g.toBCF i

def finiteDimensionalCZeroEquiv [FiniteDimensional 𝕜 X] :
    X ≃L[𝕜] C₀(Fin (Module.finrank 𝕜 X), 𝕜) :=
  (Module.finBasis 𝕜 X).equivFunL.trans
    (finiteFunctionCZeroIsometry (𝕜 := 𝕜) (X := 𝕜) (Fin (Module.finrank 𝕜 X))).toContinuousLinearEquiv

def cZeroFiniteCoefficientEquiv [Infinite Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [FiniteDimensional 𝕜 X] [Nontrivial X] : C₀(Γ, X) ≃L[𝕜] C₀(Γ, 𝕜) :=
  (cZeroMapEquiv (ι := Γ) (finiteDimensionalCZeroEquiv (𝕜 := 𝕜) (X := X))).trans
    (cZeroProductFlattenIsometry (𝕜 := 𝕜) (X := 𝕜)
      (infiniteFiniteProductEquiv Γ (Module.finrank 𝕜 X) (Module.finrank_pos))).toContinuousLinearEquiv

end ThesisCommon
