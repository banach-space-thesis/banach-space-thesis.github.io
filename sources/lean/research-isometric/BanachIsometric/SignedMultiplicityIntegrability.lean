import BanachIsometric.LipschitzSignedArea

/-!
# Actual signed multiplicities are integrable

Absolute branch-integral summability gives a genuine L¹ density, including
when its signed integral is zero. This is needed to use uniqueness against
smooth compactly supported target tests in the analytic degree argument.
-/

namespace BanachIsometric

open MeasureTheory Set Function Filter
open scoped Topology NNReal ENNReal Function

theorem integrable_real_tsum_of_summable_integral_norm
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℕ → α → ℝ}
    (hF : ∀ n, Integrable (F n) μ)
    (hS : Summable (fun n => ∫ x, ‖F n x‖ ∂μ)) :
    Integrable (fun x => ∑' n, F n x) μ := by
  have he (n : ℕ) : (∫⁻ x, ‖F n x‖ₑ ∂μ) = ‖∫ x, ‖F n x‖ ∂μ‖ₑ := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF n), ← ofReal_norm_eq_enorm,
      Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (F n x)))]
  have hfin : (∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ) < ⊤ := by
    rw [funext he]
    exact lt_top_iff_ne_top.mpr
      (ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hS.abs))
  have hlin : (∫⁻ x, ∑' n, ‖F n x‖ₑ ∂μ) < ⊤ := by
    rw [lintegral_tsum (fun n => (hF n).aestronglyMeasurable.enorm)]
    exact hfin
  have ha : ∀ᵐ x ∂μ, Summable (fun n => F n x) := by
    filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum
      (fun n => (hF n).aestronglyMeasurable.enorm)) hlin.ne] with x hx
    have hn : Summable (fun n => (‖F n x‖₊ : ℝ)) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
      exact hx.ne
    exact hn.of_norm
  refine ⟨?_, ?_⟩
  · apply aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ℕ))
      (fun s => s.aestronglyMeasurable_fun_sum (fun n _ => (hF n).aestronglyMeasurable))
    exact ha.mono (fun x hx => hx.hasSum)
  · exact (lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)).trans_lt hlin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem integrable_signedFiberSum_mul_on_regular_set
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {D : E → E →L[ℝ] E} {s : Set E} (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hdet : ∀ x ∈ s, (D x).det ≠ 0)
    (g : E → ℝ) (hint : IntegrableOn (fun x => (D x).det * g (f x)) s μ) :
    Integrable (fun y => signedFiberSum f D s y * g y) μ := by
  obtain ⟨t, hd, ht, hc, hi⟩ := exists_disjoint_measurable_injective_branches μ hs hD hdet
  have hsub (n : ℕ) : t n ⊆ s := by rw [← hc]; exact subset_iUnion t n
  have hDn (n : ℕ) : ∀ x ∈ t n, HasFDerivWithinAt f (D x) (t n) x :=
    fun x hx => (hD x (hsub n hx)).mono (hsub n)
  have hbranch (n : ℕ) : Integrable (signedBranchWeight f D (t n) g) μ :=
    (integrable_signedBranchWeight_iff μ (ht n) (hDn n) (hi n) g).mpr
      (hint.mono_set (hsub n))
  have hnorm : Summable (fun n => ∫ y, ‖signedBranchWeight f D (t n) g y‖ ∂μ) := by
    have hh : IntegrableOn (fun x => ‖(D x).det * g (f x)‖) (⋃ n, t n) μ := by
      rw [hc]
      exact hint.norm
    have hs := (hasSum_integral_iUnion ht hd hh).summable
    simpa only [integral_norm_signedBranchWeight μ (ht _) (hDn _) (hi _) g] using hs
  have hsum := integrable_real_tsum_of_summable_integral_norm hbranch hnorm
  change Integrable (signedBranchSum f D t g) μ at hsum
  exact hsum.congr (ae_of_all _ (fun y => signedBranchSum_eq_signedFiberSum f D s t hd hc hi g y))

theorem integrable_signedRegularMultiplicity_mul (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) {s : Set E} (hs : MeasurableSet s) (g : E → ℝ)
    (hint : IntegrableOn (fun x => (fderiv ℝ f x).det * g (f x)) s μ) :
    Integrable (fun y => signedRegularMultiplicity f s y * g y) μ :=
  integrable_signedFiberSum_mul_on_regular_set μ (hs.inter (measurableSet_differentiableRegularSet f))
    (fun _ hx => hx.2.1.hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx.2.2)
    g (hint.mono_set inter_subset_left)

theorem integrable_signedFiberCount_mul_of_compact_lipschitz
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {C : ℝ≥0}
    (hf : LipschitzWith C f) {s : Set E} (hs : IsCompact s)
    {g : E → ℝ} (hg : Continuous g) :
    Integrable (fun y => (signedFiberCount f (fderiv ℝ f) s y : ℝ) * g y) μ := by
  apply (integrable_signedRegularMultiplicity_mul μ f hs.measurableSet g
    (integrableOn_signedJacobian_mul_comp_of_compact_lipschitz μ hf hs hg)).congr
  filter_upwards [ae_signedRegularMultiplicity_eq_signedFiberCount_of_compact_lipschitz μ hf hs]
    with y hy
  rw [hy]

theorem integrable_signedFiberCount_of_compact_lipschitz
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {C : ℝ≥0}
    (hf : LipschitzWith C f) {s : Set E} (hs : IsCompact s) :
    Integrable (fun y => (signedFiberCount f (fderiv ℝ f) s y : ℝ)) μ := by
  simpa only [mul_one] using
    integrable_signedFiberCount_mul_of_compact_lipschitz μ hf hs (continuous_const (y := (1 : ℝ)))

end BanachIsometric
