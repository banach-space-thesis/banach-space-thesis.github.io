import ThesisCommon.Analysis.IntegralKernelTests
import ThesisCommon.Analysis.ProductMeasurableCountable
import ThesisCommon.Analysis.L1OperatorModulus
import ThesisCommon.LpCut

/-! Countable signed-indicator tests bound the absolute-kernel integral by
the constructed operator modulus. This is the substantive kernel-modulus
identification step on arbitrary input spaces. Countably many input
sets suffice for the particular weighted kernel being tested. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical
namespace ThesisCommon
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

def lOneSignCut (s : Set X) (hs : MeasurableSet s) (f : Lp ℝ 1 μ) : Lp ℝ 1 μ :=
  (2 : ℝ) • lpCut s hs f - f

theorem lOneSignCut_coe (s : Set X) (hs : MeasurableSet s) (f : Lp ℝ 1 μ) :
    lOneSignCut s hs f =ᵐ[μ] fun x => if x ∈ s then f x else -f x := by
  filter_upwards [Lp.coeFn_sub ((2 : ℝ) • lpCut s hs f) f,
    Lp.coeFn_smul (2 : ℝ) (lpCut s hs f), lpCut_coe s hs f] with x hsub hsmul hcut
  change (2 • lpCut s hs f - f) x = _
  rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hcut]
  by_cases hx : x ∈ s
  · simp only [hx, indicator_of_mem, if_pos]
    ring
  · simp [hx]

theorem abs_lOneSignCut (s : Set X) (hs : MeasurableSet s) (f : Lp ℝ 1 μ) :
    |lOneSignCut s hs f| = |f| := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_abs (lOneSignCut s hs f), Lp.coeFn_abs f,
    lOneSignCut_coe s hs f] with x hg hf hcut
  rw [hg, hf, hcut]
  split <;> simp

theorem IsIntegralKernel.apply_signCut {k : X × Y → ℝ}
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hk : IsIntegralKernel k K)
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℝ 1 μ) :
    K (lOneSignCut s hs f) =ᵐ[ν] fun y =>
      2 * (∫ x in s, k (x, y) * f x ∂μ) - ∫ x, k (x, y) * f x ∂μ := by
  filter_upwards [hk.represents (lOneSignCut s hs f), hk.integrable_section f] with y hy hfi
  rw [hy]
  calc
    (∫ x, k (x, y) * lOneSignCut s hs f x ∂μ) =
        ∫ x, 2 * s.indicator (fun x => k (x, y) * f x) x - k (x, y) * f x ∂μ := by
      apply integral_congr_ae
      filter_upwards [lOneSignCut_coe s hs f] with x hx
      by_cases hxs : x ∈ s
      · simp only [hx, hxs, if_pos, indicator_of_mem]
        ring
      · simp [hx, hxs]
    _ = _ := by
      rw [integral_sub ((hfi.indicator hs).const_mul 2) hfi,
        integral_const_mul, integral_indicator hs]

theorem IsIntegralKernel.abs_apply_le_modulus
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hk : IsIntegralKernel k K)
    (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    (fun y => ∫ x, |k (x, y)| * f x ∂μ) ≤ᵐ[ν] lOneOperatorModulus K f := by
  classical
  obtain ⟨C, hcountC, hmeasC, hprod⟩ := exists_countable_left_generators_of_measurable
    (hk.measurable.mul ((Lp.stronglyMeasurable f).measurable.comp measurable_fst))
  let 𝒜 := generateSetAlgebra C
  have hcount : 𝒜.Countable := countable_generateSetAlgebra hcountC
  have hgen : MeasurableSpace.generateFrom 𝒜 = MeasurableSpace.generateFrom C := by
    dsimp only [𝒜]
    exact generateFrom_generateSetAlgebra_eq
  have hmeas (s : Set X) (hs : s ∈ 𝒜) : MeasurableSet s :=
    MeasurableSpace.generateFrom_le hmeasC s
      (hgen ▸ MeasurableSpace.measurableSet_generateFrom hs)
  have htest (s : 𝒜) : ∀ᵐ y ∂ν,
      2 * (∫ x in (s : Set X), k (x, y) * f x ∂μ) - (∫ x, k (x, y) * f x ∂μ) ≤
        (lOneOperatorModulus K f) y := by
    have hdom : K (lOneSignCut s (hmeas s s.2) f) ≤ lOneOperatorModulus K f := by
      apply (le_abs_self _).trans
      simpa only [abs_lOneSignCut, abs_of_nonneg hf] using
        lOneOperatorModulus_dominates K (lOneSignCut s (hmeas s s.2) f)
    filter_upwards [(Lp.coeFn_le _ _).mpr hdom, hk.apply_signCut s (hmeas s s.2) f] with y hy heq
    simpa only [heq] using hy
  letI : Countable 𝒜 := hcount.to_subtype
  have htests : ∀ᵐ y ∂ν, ∀ s : 𝒜,
      2 * (∫ x in (s : Set X), k (x, y) * f x ∂μ) - (∫ x, k (x, y) * f x ∂μ) ≤
        (lOneOperatorModulus K f) y := ae_all_iff.mpr htest
  filter_upwards [hk.integrable_section f, htests] with y hy htests_y
  have hm : @Measurable X ℝ (MeasurableSpace.generateFrom 𝒜) _
      (fun x => k (x, y) * f x) := by
    rw [hgen]
    exact hprod.comp (@measurable_prodMk_right X Y (MeasurableSpace.generateFrom C) mY y)
  have h := integral_abs_le_of_signed_subalgebra_tests isSetAlgebra_generateSetAlgebra hmeas hm hy
    ((lOneOperatorModulus K f) y) (fun s hs => htests_y ⟨s, hs⟩)
  have heq : (∫ x, |k (x, y)| * f x ∂μ) = ∫ x, |k (x, y) * f x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [(Lp.coeFn_nonneg f).mpr hf] with x hx
    simp [abs_mul, abs_of_nonneg hx]
  exact heq.trans_le h

end ThesisCommon
