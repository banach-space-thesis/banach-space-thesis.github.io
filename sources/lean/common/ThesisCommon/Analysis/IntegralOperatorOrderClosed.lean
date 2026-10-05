import ThesisCommon.Analysis.IntegralOperatorMonotoneSup
import ThesisCommon.Analysis.L1DensityOperatorOrder
import Mathlib.Order.Bounds.OrderIso

/-! The positive directed order closure of the genuine integral operators
on sigma-finite L1 spaces, transported through a positive finite density. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SFinite ν]

theorem IsIntegralOperator.of_directed_sup_sigmaFinite
    {s : Set (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)} (hs : s.Nonempty)
    (hI : ∀ T ∈ s, IsIntegralOperator T) (hpos : ∀ T ∈ s, 0 ≤ T)
    (hdir : DirectedOn (· ≤ ·) s) {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hS : IsLUB s S) :
    IsIntegralOperator S := by
  obtain ⟨g, hg, hgpos, hgfin⟩ := exists_positive_finite_density μ
  letI := hgfin
  let e := lOneWithDensityOperatorOrderIso (ν := ν) hg hgpos
  have hI' : ∀ T ∈ e '' s, IsIntegralOperator T := by
    rintro _ ⟨T, hT, rfl⟩
    obtain ⟨k, hk⟩ := hI T hT
    exact ⟨k, hk.withDensity_input hg⟩
  have hpos' : ∀ T ∈ e '' s, 0 ≤ T := by
    rintro _ ⟨T, hT, rfl⟩
    simpa only [e, lOneWithDensityOperatorOrderIso_zero] using e.monotone (hpos T hT)
  have hdir' : DirectedOn (· ≤ ·) (e '' s) := by
    rintro _ ⟨T, hT, rfl⟩ _ ⟨U, hU, rfl⟩
    obtain ⟨V, hV, hTV, hUV⟩ := hdir T hT U hU
    exact ⟨e V, ⟨V, hV, rfl⟩, e.monotone hTV, e.monotone hUV⟩
  obtain ⟨k, hk⟩ := IsIntegralOperator.of_directed_sup (hs.image e) hI' hpos' hdir'
    (e.isLUB_image'.mpr hS)
  exact ⟨k, hk.of_withDensity_input hg hgpos⟩

end ThesisCommon
