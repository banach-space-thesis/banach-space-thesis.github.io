import ThesisCommon.Analysis.CompactPositiveCantor
import ThesisCommon.Analysis.IntervalLocalCutoff
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! Actual localization data for every real or complex operator on C[0,1].
The coefficient is bounded below by 1/2 and the local residual is below 1/4. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem intervalKernel_localization_data
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) :
    ∃ (Q : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (n : ℕ)
      (f : (ℕ → Bool) → UnitInterval) (φ : C(UnitInterval, ℝ)),
      (Q = T ∨ Q = ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) - T) ∧
      Continuous f ∧ Function.Injective f ∧
      (∀ x, 1 / 2 ≤ ‖intervalOperatorAtom Q (f x)‖) ∧
      Continuous (fun x => intervalOperatorAtom Q (f x)) ∧
      (∀ x, intervalKernelResidualMass Q n (f x) < 1 / 4) ∧
      (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ (∀ x, φ (f x) = 1) ∧
      (∀ x t, t ∉ Metric.ball (f x) (1 / (n + 1 : ℝ)) → φ t = 0) := by
  letI : MeasurableSpace 𝕜 := borel 𝕜
  letI : BorelSpace 𝕜 := ⟨rfl⟩
  obtain ⟨Q, n, f, hQ, hf, hinj, hlarge, hcont, hres, hdiam⟩ :=
    intervalKernel_small_cantor_selection T (volume : Measure UnitInterval) (by simp)
  obtain ⟨φ, hφ, hφone, hφzero⟩ := exists_interval_cantor_local_cutoff f
    (show 0 < 1 / (n + 1 : ℝ) by positivity) hdiam
  exact ⟨Q, n, f, φ, hQ, hf, hinj, hlarge, hcont, hres, hφ, hφone, hφzero⟩

end ThesisCommon
