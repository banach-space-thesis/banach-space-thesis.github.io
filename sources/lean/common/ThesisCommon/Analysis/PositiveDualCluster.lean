import ThesisCommon.Analysis.ContinuousMapDualAL
import Mathlib.Analysis.Normed.Module.WeakDual

/-! Bounded sequences of positive functionals have positive weak-star
cluster points. The useful conclusion is a direct scalar recurrence
property; no sequential compactness assumption is used. -/
noncomputable section
open Set Topology Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem exists_positive_continuousMapDual_cluster
    (φ : ℕ → C(K, ℝ) →L[ℝ] ℝ) (hφ : ∀ n, 0 ≤ φ n)
    {C : ℝ} (hC : ∀ n, ‖φ n‖ ≤ C) :
    ∃ ψ : C(K, ℝ) →L[ℝ] ℝ, 0 ≤ ψ ∧ ‖ψ‖ ≤ C ∧
      ∀ (f : C(K, ℝ)) (r : ℝ), ψ f < r → ∃ᶠ n in atTop, φ n f < r := by
  let u : ℕ → WeakDual ℝ C(K, ℝ) := fun n => StrongDual.toWeakDual (φ n)
  have hb : ∀ᶠ n in atTop, u n ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : C(K, ℝ) →L[ℝ] ℝ) C := by
    apply Filter.Eventually.of_forall
    intro n
    change ‖φ n - 0‖ ≤ C
    simpa only [sub_zero] using hC n
  obtain ⟨ξ, hξ, hc⟩ :=
    (WeakDual.isCompact_closedBall ℝ (0 : C(K, ℝ) →L[ℝ] ℝ) C).exists_mapClusterPt_of_frequently
      hb.frequently
  let ψ : C(K, ℝ) →L[ℝ] ℝ := WeakDual.toStrongDual ξ
  have hrec (f : C(K, ℝ)) (r : ℝ) (hr : ψ f < r) :
      ∃ᶠ n in atTop, φ n f < r := by
    have he : Continuous (fun ζ : WeakDual ℝ C(K, ℝ) => ζ f) :=
      WeakBilin.eval_continuous _ _
    exact hc.frequently ((isOpen_lt he continuous_const).mem_nhds hr)
  refine ⟨ψ, ?_, ?_, hrec⟩
  · intro f hf
    by_contra h
    obtain ⟨n, hn⟩ := (hrec f 0 (lt_of_not_ge h)).exists
    exact (not_lt_of_ge (hφ n f hf)) hn
  · change ‖ψ - 0‖ ≤ C at hξ
    simpa only [sub_zero] using hξ

end ThesisCommon
