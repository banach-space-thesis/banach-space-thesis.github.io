import Posets.ProductIdealCounts
import Posets.IdealCountRealizationPadding

/-! The admissible finite list that realizes the numerical formulas in 8.4. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
variable (r : ℕ) {k : ℕ} (P : Fin k → Type)
  [∀ i, Fintype (P i)] [∀ i, PartialOrder (P i)] [∀ i, LocallyFiniteOrder (P i)]

instance cZeroIncidenceFactor_complete (i : Fin r ⊕ Fin k) :
    CompleteSpace (cZeroIncidenceFactor (𝕜 := 𝕜) r P i) := by
  cases i with
  | inl i => exact inferInstanceAs (CompleteSpace (cZero 𝕜 →L[𝕜] cZero 𝕜))
  | inr i =>
    have hc : IsClosed (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P i) :
        Set ((P i → 𝕜) →L[𝕜] (P i → 𝕜))) := by
      rw [finiteIncidenceSubalgebra_carrier]
      exact finiteIncidenceOperators_isClosed
    exact hc.completeSpace_coe

theorem cZeroIncidenceFactor_admissible (i : Fin r ⊕ Fin k) :
    AdmissibleAlgebra 𝕜 (cZeroIncidenceFactor (𝕜 := 𝕜) r P i) := by
  cases i with
  | inl i =>
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    let f : BoundedHom 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜) (cZero 𝕜 →L[𝕜] cZero 𝕜) :=
      ⟨ContinuousLinearMap.id 𝕜 _, fun _ _ => rfl⟩
    exact ⟨f, isometry_id, Set.range_id⟩
  | inr i =>
    refine Or.inr (Or.inr (Or.inl ⟨P i, inferInstance, inferInstance, ?_⟩))
    let S := finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P i)
    let f : BoundedHom 𝕜 S ((P i → 𝕜) →L[𝕜] (P i → 𝕜)) :=
      ⟨S.toSubmodule.subtypeL, fun _ _ => rfl⟩
    refine ⟨f, isometry_subtype_coe, ?_⟩
    exact Subtype.range_coe_subtype.trans finiteIncidenceSubalgebra_carrier

abbrev idealCountFiniteFactor (i : Fin (r + k)) : Type :=
  cZeroIncidenceFactor (𝕜 := 𝕜) r P (finSumFinEquiv.symm i)

def idealCountFiniteFactor_closedIdealEquiv :
    ClosedIdeal 𝕜 (∀ i, idealCountFiniteFactor (𝕜 := 𝕜) r P i) ≃
      ClosedIdeal 𝕜 (∀ i, cZeroIncidenceFactor (𝕜 := 𝕜) r P i) :=
  (productClosedIdealOrderIso (𝕜 := 𝕜) (idealCountFiniteFactor (𝕜 := 𝕜) r P)).toEquiv.trans
    ((Equiv.piCongrLeft' (fun i => ClosedIdeal 𝕜 (cZeroIncidenceFactor (𝕜 := 𝕜) r P i))
      finSumFinEquiv).symm.trans
        (productClosedIdealOrderIso (𝕜 := 𝕜) (cZeroIncidenceFactor (𝕜 := 𝕜) r P)).toEquiv.symm)

def idealCountFiniteFactor_maximalClosedIdealEquiv :
    MaximalClosedIdeals 𝕜 (∀ i, idealCountFiniteFactor (𝕜 := 𝕜) r P i) ≃
      MaximalClosedIdeals 𝕜 (∀ i, cZeroIncidenceFactor (𝕜 := 𝕜) r P i) :=
  (productMaximalClosedIdealEquiv (𝕜 := 𝕜) (idealCountFiniteFactor (𝕜 := 𝕜) r P)).trans
    ((Equiv.sigmaCongrLeft finSumFinEquiv.symm).trans
      (productMaximalClosedIdealEquiv (𝕜 := 𝕜) (cZeroIncidenceFactor (𝕜 := 𝕜) r P)).symm)

instance cZeroIncidenceFactor_finite_closedIdeals (i : Fin r ⊕ Fin k) :
    Finite (ClosedIdeal 𝕜 (cZeroIncidenceFactor (𝕜 := 𝕜) r P i)) := by
  cases i with
  | inl i => exact Finite.of_equiv (Fin 3) (cZeroClosedIdealEquivFinThree (𝕜 := 𝕜)).symm
  | inr i =>
    letI : Finite (IntervalUpsets (P i)) := by unfold IntervalUpsets; infer_instance
    exact Finite.of_equiv (IntervalUpsets (P i))
      (finiteIncidenceClosedIdealEquiv (𝕜 := 𝕜) (P := P i)).symm

end Posets
