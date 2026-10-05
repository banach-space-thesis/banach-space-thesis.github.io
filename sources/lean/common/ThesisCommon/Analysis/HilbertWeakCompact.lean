import ThesisCommon.WeakCompact
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Weak compactness of the closed unit ball of a real Hilbert space, obtained
from the actual weak-star compact dual ball through the Riesz isometry. -/
noncomputable section
open Set Topology
namespace ThesisCommon
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def hilbertWeakDualToWeak (f : WeakDual ℝ H) : WeakSpace ℝ H :=
  toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual f))

theorem continuous_hilbertWeakDualToWeak : Continuous (hilbertWeakDualToWeak (H := H)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro f
  let u := (InnerProductSpace.toDual ℝ H).symm f
  have heq : (fun g : WeakDual ℝ H =>
      (topDualPairing ℝ H).flip (hilbertWeakDualToWeak g) f) = fun g => g u := by
    funext g
    change f ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual g)) = g u
    rw [← InnerProductSpace.toDual_symm_apply (y := f)]
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rfl
  rw [heq]
  exact WeakDual.eval_continuous u

theorem weaklyCompact_hilbert_id :
    IsWeaklyCompactOperator (ContinuousLinearMap.id ℝ H) := by
  let B : Set (WeakDual ℝ H) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1
  refine ⟨hilbertWeakDualToWeak '' B,
    (WeakDual.isCompact_closedBall ℝ (0 : StrongDual ℝ H) 1).image
      continuous_hilbertWeakDualToWeak, ?_⟩
  intro x hx
  refine ⟨StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ H) x), ?_, ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ H) x - 0‖ ≤ 1
    simpa using hx
  · change toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm
      ((InnerProductSpace.toDual ℝ H) x)) = toWeakSpace ℝ H x
    rw [LinearIsometryEquiv.symm_apply_apply]

theorem weaklyCompact_of_hilbert_range {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] H) : IsWeaklyCompactOperator T := by
  simpa using (weaklyCompact_hilbert_id (H := H)).comp_right T

theorem weaklyCompact_of_hilbert_factorization
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] H) (B : H →L[ℝ] F) : IsWeaklyCompactOperator (B.comp A) :=
  (weaklyCompact_of_hilbert_range A).comp_left B

end ThesisCommon
