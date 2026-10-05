import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Analysis.Real.Cardinality

/-! A real continuous dual of a separable normed space has cardinality at
most continuum: a functional is determined by its values on a dense sequence. -/
noncomputable section
namespace ThesisCommon

theorem realDual_cardinal_le_continuum (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [TopologicalSpace.SeparableSpace X] :
    Cardinal.mk (X →L[ℝ] ℝ) ≤ Cardinal.continuum := by
  let F : (X →L[ℝ] ℝ) → (ℕ → ℝ) := fun φ n => φ (TopologicalSpace.denseSeq X n)
  have hF : Function.Injective F := by
    intro φ ψ h
    apply ContinuousLinearMap.ext
    have heq : (φ : X → ℝ) = ψ :=
      (TopologicalSpace.denseRange_denseSeq X).equalizer φ.continuous ψ.continuous
        (funext (fun n => congrFun h n))
    exact congrFun heq
  calc
    _ ≤ Cardinal.mk (ℕ → ℝ) := Cardinal.mk_le_of_injective hF
    _ = Cardinal.continuum := by
      rw [Cardinal.mk_arrow, Cardinal.mk_real, Cardinal.mk_nat, Cardinal.lift_uzero,
        Cardinal.lift_uzero, Cardinal.continuum_power_aleph0]

theorem intervalContinuousRealDual_cardinal_le_continuum :
    Cardinal.mk (IntervalContinuous ℝ →L[ℝ] ℝ) ≤ Cardinal.continuum :=
  realDual_cardinal_le_continuum (IntervalContinuous ℝ)

end ThesisCommon
