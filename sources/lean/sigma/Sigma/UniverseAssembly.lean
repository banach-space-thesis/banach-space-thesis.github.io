import Sigma.Assembly
import ThesisCommon.Analysis.UniverseTransportBanachLattice

/-! The concrete construction uses small spaces. This file lifts its conclusion
to any universe, retaining the quantifier over all Banach lattice models in
that universe. The smallness of a possible large lattice model follows from
its isomorphism with the constructed space, rather than being assumed. -/
noncomputable section
universe u v
namespace SigmaNonprimarity
open ThesisCommon

def liftCompactum (K : Compactum.{v}) : Compactum.{max u v} where
  Carrier := ULift.{u} K

def liftRealBanachSpace (E : RealBanachSpace.{v}) : RealBanachSpace.{max u v} where
  Carrier := ULift.{u} E

/-- Pullback along the homeomorphism from a lifted compactum. -/
def continuousLiftEquiv (K : Type v) [TopologicalSpace K] [CompactSpace K] :
    C(ULift.{u} K, ℝ) ≃L[ℝ] C(K, ℝ) := by
  let e : C(ULift.{u} K, ℝ) ≃ₗ[ℝ] C(K, ℝ) :=
    { toFun := fun f => ⟨fun x => f (ULift.up x), f.continuous.comp continuous_uliftUp⟩
      invFun := fun f => ⟨fun x => f x.down, f.continuous.comp continuous_uliftDown⟩
      left_inv := by intro f; ext x; rfl
      right_inv := by intro f; ext x; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact LinearEquiv.toContinuousLinearEquivOfBounds e 1 1
    (by
      intro f
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun x => f.norm_coe_le_norm (ULift.up x))
    (by
      intro f
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun x => f.norm_coe_le_norm x.down)

/-- A fully proved small-universe counterexample implies the complete statement
in any prescribed universe, including obstruction to every lattice in it. -/
theorem theorem_1_1_lift (h : Theorem_1_1.{0}) : Theorem_1_1.{u} := by
  rcases h with ⟨K, X, Y, ⟨e⟩, hX, hY⟩
  let ex : X ≃L[ℝ] liftRealBanachSpace.{u} X := ContinuousLinearEquiv.ulift.symm
  let ey : Y ≃L[ℝ] liftRealBanachSpace.{u} Y := ContinuousLinearEquiv.ulift.symm
  refine ⟨liftCompactum.{u} K, liftRealBanachSpace.{u} X, liftRealBanachSpace.{u} Y,
    ⟨((continuousLiftEquiv.{u} K).trans e).trans (ex.prodCongr ey)⟩, ?_, ?_⟩
  · exact not_isomorphicToBanachLattice_of_equiv ex hX
  · exact not_isomorphicToBanachLattice_of_equiv ey hY

end SigmaNonprimarity
