import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.MetricSpace.Basic

/-! # Uniqueness of almost-everywhere constants on overlapping neighborhoods -/

namespace BanachIsometric

open MeasureTheory Set Metric

theorem ae_constants_eq_of_nonnull_inter
    {X Y : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → Y} {s t : Set X} {D D' : Y} (hnonnull : μ (s ∩ t) ≠ 0)
    (hD : ∀ᵐ y ∂μ, y ∈ s → f y = D) (hD' : ∀ᵐ y ∂μ, y ∈ t → f y = D') :
    D = D' := by
  have heq : ∀ᵐ y ∂μ, y ∈ s ∩ t → D = D' := by
    filter_upwards [hD, hD'] with y hy hy'
    intro hmem
    exact (hy hmem.1).symm.trans (hy' hmem.2)
  obtain ⟨y, hy, h⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hnonnull (ae_restrict_of_ae heq)
  exact h hy

theorem ae_constants_eq_on_balls
    {X Y : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) [Measure.IsOpenPosMeasure μ] {f : X → Y} (c : X)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {D D' : Y}
    (hD : ∀ᵐ y ∂μ, y ∈ ball c r → f y = D)
    (hD' : ∀ᵐ y ∂μ, y ∈ ball c s → f y = D') : D = D' := by
  apply ae_constants_eq_of_nonnull_inter μ _ hD hD'
  exact (isOpen_ball.inter isOpen_ball).measure_ne_zero μ
    ⟨c, mem_ball_self hr, mem_ball_self hs⟩

end BanachIsometric
