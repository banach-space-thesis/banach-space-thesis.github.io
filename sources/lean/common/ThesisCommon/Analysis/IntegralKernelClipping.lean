import ThesisCommon.Analysis.KernelClippingBudget
import ThesisCommon.Analysis.IntegralKernelApproximation
import ThesisCommon.Analysis.WeakCompactClosed

/-! Actual clipped integral operators and weak compactness of budget clipping
from the uniform residual estimate. All approximants are constructed from kernels. -/

noncomputable section
open MeasureTheory Filter Set

namespace ThesisCommon

theorem clipResidual_le_norm_truncatedKernel {X Y : Type*}
    (k : X × Y → ℝ) (t : ℝ) (z : X × Y) :
    clipResidual t (k z) ≤ ‖truncatedKernel t k z‖ := by
  by_cases ht : t ≤ ‖k z‖
  · simpa only [truncatedKernel,
      Set.indicator_of_mem (show z ∈ {w | t ≤ ‖k w‖} from ht)] using clipResidual_le_norm t (k z)
  · have hle : ‖k z‖ ≤ max t 0 := (le_of_lt (lt_of_not_ge ht)).trans (le_max_left _ _)
    rw [show clipResidual t (k z) = 0 from max_eq_right (sub_nonpos.mpr hle)]
    exact norm_nonneg _

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SFinite ν]
variable {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

theorem IsIntegralKernel.clipResidualMass_le_truncatedKernel (hk : IsIntegralKernel k K)
    (t : ℝ) : ∀ᵐ x ∂μ, clipResidualMass ν (fun y => k (x, y)) t ≤
      ∫ y, ‖truncatedKernel t k (x, y)‖ ∂ν := by
  filter_upwards [hk.hasKernelBound_sigmaFinite,
    hk.hasKernelBound_sigmaFinite.truncatedKernel hk.measurable t] with x hx htx
  exact integral_mono (integrable_clipResidual hx.1 t) htx.1.norm
    (fun y => clipResidual_le_norm_truncatedKernel k t (x, y))

/-- The actual bounded operator with the signed-clipped kernel. -/
def IsIntegralKernel.clippedOperator (hk : IsIntegralKernel k K) (t : ℝ) :
    Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  integralKernelOperator (measurable_scalarClip hk.measurable measurable_const)
    (hk.hasKernelBound_sigmaFinite.mono (measurable_scalarClip hk.measurable measurable_const)
      (Eventually.of_forall fun x => Eventually.of_forall fun y => norm_scalarClip_le t (k (x, y))))

theorem IsIntegralKernel.isIntegralKernel_clippedOperator (hk : IsIntegralKernel k K) (t : ℝ) :
    IsIntegralKernel (fun z => scalarClip t (k z)) (hk.clippedOperator t) :=
  isIntegralKernel_integralKernelOperator _ _

/-- Uniform column residual bounds give the corresponding operator norm bound. -/
theorem IsIntegralKernel.norm_sub_clippedOperator_le (hk : IsIntegralKernel k K)
    (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ᵐ x ∂μ, clipResidualMass ν (fun y => k (x, y)) t ≤ ε) :
    ‖K - hk.clippedOperator t‖ ≤ ε := by
  apply ((hk.sub (hk.isIntegralKernel_clippedOperator t)).hasKernelBound_iff_norm_le hε).1
  filter_upwards [hk.hasKernelBound_sigmaFinite, hbound] with x hx hb
  refine ⟨hx.1.sub (integrable_scalarClip hx.1 t), ?_⟩
  simpa only [Pi.sub_apply, norm_sub_scalarClip] using hb

theorem IsIntegralKernel.weaklyCompact_clippedOperator [IsFiniteMeasure ν]
    (hk : IsIntegralKernel k K) (t : ℝ) : IsWeaklyCompactOperator (hk.clippedOperator t) :=
  (hk.isIntegralKernel_clippedOperator t).weaklyCompact_of_bound (le_max_right t 0)
    (Eventually.of_forall fun z => norm_scalarClip_le_level t (k z))

/-- Uniformly vanishing residual column masses give norm approximation by
the bounded signed-clipping operators, hence genuine weak compactness. -/
theorem IsIntegralKernel.weaklyCompact_of_uniform_clipResidual [IsFiniteMeasure ν]
    (hk : IsIntegralKernel k K)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      ∀ᵐ x ∂μ, clipResidualMass ν (fun y => k (x, y)) n ≤ ε) :
    IsWeaklyCompactOperator K := by
  change K ∈ (weaklyCompactSubmodule ℝ (Lp ℝ 1 μ) (Lp ℝ 1 ν) :
    Set (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν))
  rw [← (isClosed_weaklyCompactSubmodule (𝕜 := ℝ)
    (E := Lp ℝ 1 μ) (F := Lp ℝ 1 ν)).closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := hsmall (ε / 2) (by positivity)
  refine ⟨hk.clippedOperator n, hk.weaklyCompact_clippedOperator n, ?_⟩
  rw [dist_eq_norm]
  exact (hk.norm_sub_clippedOperator_le n (by positivity) hn).trans_lt (by linarith)

variable {d : X → ℝ}

theorem IsIntegralKernel.hasKernelBound_budgetClipKernel (hk : IsIntegralKernel k K)
    (hd : Measurable d) : HasKernelBound μ ν (budgetClipKernel ν k d) ‖K‖ :=
  hk.hasKernelBound_sigmaFinite.mono (measurable_budgetClipKernel hk.measurable hd)
    (Eventually.of_forall fun x => Eventually.of_forall fun y => norm_budgetClipKernel_le k d (x, y))

/-- The actual integral operator produced by measurable column-budget clipping. -/
def IsIntegralKernel.budgetClippedOperator (hk : IsIntegralKernel k K) (hd : Measurable d) :
    Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  integralKernelOperator (measurable_budgetClipKernel hk.measurable hd)
    (hk.hasKernelBound_budgetClipKernel hd)

theorem IsIntegralKernel.isIntegralKernel_budgetClippedOperator (hk : IsIntegralKernel k K)
    (hd : Measurable d) :
    IsIntegralKernel (budgetClipKernel ν k d) (hk.budgetClippedOperator hd) :=
  isIntegralKernel_integralKernelOperator _ _

theorem IsIntegralKernel.norm_budgetClippedOperator_le (hk : IsIntegralKernel k K)
    (hd : Measurable d) : ‖hk.budgetClippedOperator hd‖ ≤ ‖K‖ :=
  norm_integralKernelOperator_le _ _ (norm_nonneg K)

/-- The exact error in each column, away from the original null exceptional set. -/
theorem IsIntegralKernel.budgetClippedKernel_error (hk : IsIntegralKernel k K)
    (hd : ∀ᵐ x ∂μ, 0 ≤ d x) :
    ∀ᵐ x ∂μ, (∫ y, ‖k (x, y) - budgetClipKernel ν k d (x, y)‖ ∂ν) =
      min (∫ y, ‖k (x, y)‖ ∂ν) (d x) := by
  filter_upwards [hk.hasKernelBound_sigmaFinite, hd] with x hx hd0
  have heq := budgetClipKernel_column_eq (d := d) hx.1
  simp_rw [show ∀ y, budgetClipKernel ν k d (x, y) =
    budgetClip ν (fun y => k (x, y)) (d x) y from fun y => congrFun heq y]
  exact integral_norm_sub_budgetClip hx.1 hd0

theorem IsIntegralKernel.norm_sub_budgetClippedOperator_le (hk : IsIntegralKernel k K)
    (hd : Measurable d) {D : ℝ} (hD : 0 ≤ D)
    (hd0 : ∀ᵐ x ∂μ, 0 ≤ d x) (hdD : ∀ᵐ x ∂μ, d x ≤ D) :
    ‖K - hk.budgetClippedOperator hd‖ ≤ D := by
  apply ((hk.sub (hk.isIntegralKernel_budgetClippedOperator hd)).hasKernelBound_iff_norm_le hD).1
  filter_upwards [hk.hasKernelBound_sigmaFinite, hk.hasKernelBound_budgetClipKernel hd,
    hk.budgetClippedKernel_error hd0, hdD] with x hkx hhx he hxD
  refine ⟨hkx.1.sub hhx.1, ?_⟩
  change (∫ y, ‖k (x, y) - budgetClipKernel ν k d (x, y)‖ ∂ν) ≤ D
  rw [he]
  exact (min_le_right _ _).trans hxD

/-- Exact residual-tail compatibility for the measurable selected kernel. -/
theorem IsIntegralKernel.clipResidualMass_budgetClippedKernel (hk : IsIntegralKernel k K)
    (hd : ∀ᵐ x ∂μ, 0 ≤ d x) {n : ℝ} (hn : 0 ≤ n) :
    ∀ᵐ x ∂μ, clipResidualMass ν (fun y => budgetClipKernel ν k d (x, y)) n =
      max (clipResidualMass ν (fun y => k (x, y)) n - d x) 0 := by
  filter_upwards [hk.hasKernelBound_sigmaFinite, hd] with x hx hd0
  rw [budgetClipKernel_column_eq hx.1]
  exact clipResidualMass_budgetClip hx.1 hd0 hn

/-- This supplies the weakly compact candidate in the repaired clipping argument:
the uniform excess-tail estimate is exactly the remaining scalar estimate. -/
theorem IsIntegralKernel.weaklyCompact_budgetClippedOperator [IsFiniteMeasure ν]
    (hk : IsIntegralKernel k K) (hd : Measurable d) (hd0 : ∀ᵐ x ∂μ, 0 ≤ d x)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      ∀ᵐ x ∂μ, max (clipResidualMass ν (fun y => k (x, y)) n - d x) 0 ≤ ε) :
    IsWeaklyCompactOperator (hk.budgetClippedOperator hd) := by
  apply (hk.isIntegralKernel_budgetClippedOperator hd).weaklyCompact_of_uniform_clipResidual
  intro ε hε
  obtain ⟨n, hn⟩ := hsmall ε hε
  refine ⟨n, ?_⟩
  filter_upwards [hn, hk.clipResidualMass_budgetClippedKernel hd0
    (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)] with x hx heq
  rwa [heq]

end ThesisCommon
