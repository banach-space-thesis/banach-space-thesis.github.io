import ThesisCommon.Analysis.IntegralKernel
import ThesisCommon.Analysis.L1Lattice
import ThesisCommon.Analysis.IntegralAlgebraPositivity
import ThesisCommon.Analysis.ProductMeasurableCountable

/-! Indicator tests for actual integral kernels. Countable generators for
the particular kernel make the positivity tests simultaneous outside one
null set, without requiring the input sigma-algebra to be countably generated. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

def lOneIndicator (μ : Measure X) [IsFiniteMeasure μ] (s : Set X) (hs : MeasurableSet s) :
    Lp ℝ 1 μ := ((integrable_const (1 : ℝ)).indicator hs).toL1 (s.indicator (fun _ => 1))

theorem lOneIndicator_coe (s : Set X) (hs : MeasurableSet s) :
    lOneIndicator μ s hs =ᵐ[μ] s.indicator (fun _ => (1 : ℝ)) := Integrable.coeFn_toL1 _

theorem lOneIndicator_nonneg (s : Set X) (hs : MeasurableSet s) :
    0 ≤ lOneIndicator μ s hs := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [lOneIndicator_coe (μ := μ) s hs] with x hx
  rw [hx]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- Finite input measure lets the constant-one test recover unweighted
section integrability; the product kernel need not yet be integrable. -/
theorem IsIntegralKernel.integrable_sections {k : X × Y → ℝ}
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hk : IsIntegralKernel k K) :
    ∀ᵐ y ∂ν, Integrable (fun x => k (x, y)) μ := by
  let one : Lp ℝ 1 μ := lOneIndicator μ univ MeasurableSet.univ
  have hone : one =ᵐ[μ] fun _ => (1 : ℝ) := by
    simpa only [indicator_univ] using lOneIndicator_coe (μ := μ) univ MeasurableSet.univ
  filter_upwards [hk.integrable_section one] with y hy
  apply hy.congr
  filter_upwards [hone] with x hx
  simp [hx]

theorem IsIntegralKernel.apply_indicator {k : X × Y → ℝ}
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hk : IsIntegralKernel k K)
    (s : Set X) (hs : MeasurableSet s) :
    K (lOneIndicator μ s hs) =ᵐ[ν] fun y => ∫ x in s, k (x, y) ∂μ := by
  filter_upwards [hk.represents (lOneIndicator μ s hs)] with y hy
  rw [hy, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [lOneIndicator_coe (μ := μ) s hs] with x hx
  by_cases hxs : x ∈ s <;> simp [hx, hxs]

/-- A positive operator with a measurable real kernel has an a.e. nonnegative
kernel. The input measure is finite and the output measure is s-finite. -/
theorem IsIntegralKernel.nonneg_ae_of_positive
    [SFinite ν]
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hk : IsIntegralKernel k K)
    (hK : ∀ f, 0 ≤ f → 0 ≤ K f) : ∀ᵐ z ∂μ.prod ν, 0 ≤ k z := by
  classical
  obtain ⟨C, hcountC, hmeasC, hprod⟩ :=
    exists_countable_left_generators_of_measurable hk.measurable
  let 𝒜 := generateSetAlgebra C
  have hcount : 𝒜.Countable := countable_generateSetAlgebra hcountC
  have hgen : MeasurableSpace.generateFrom 𝒜 = MeasurableSpace.generateFrom C := by
    dsimp only [𝒜]
    exact generateFrom_generateSetAlgebra_eq
  have hmeas (s : Set X) (hs : s ∈ 𝒜) : MeasurableSet s :=
    MeasurableSpace.generateFrom_le hmeasC s
      (hgen ▸ MeasurableSpace.measurableSet_generateFrom hs)
  have htest (s : 𝒜) : ∀ᵐ y ∂ν, 0 ≤ ∫ x in (s : Set X), k (x, y) ∂μ := by
    have hpos := (Lp.coeFn_nonneg _).mpr (hK _ (lOneIndicator_nonneg (μ := μ) s (hmeas s s.2)))
    filter_upwards [hpos, hk.apply_indicator s (hmeas s s.2)] with y hy heq
    simpa only [heq] using hy
  letI : Countable 𝒜 := hcount.to_subtype
  have htests : ∀ᵐ y ∂ν, ∀ s : 𝒜, 0 ≤ ∫ x in (s : Set X), k (x, y) ∂μ :=
    ae_all_iff.mpr htest
  have hsections : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, 0 ≤ k (x, y) := by
    filter_upwards [hk.integrable_sections, htests] with y hy htests_y
    have hmy : @Measurable X ℝ (MeasurableSpace.generateFrom 𝒜) _ (fun x => k (x, y)) := by
      rw [hgen]
      exact hprod.comp (@measurable_prodMk_right X Y (MeasurableSpace.generateFrom C) mY y)
    exact ae_nonneg_of_setIntegral_nonneg_on_subalgebra isSetAlgebra_generateSetAlgebra hmeas hmy hy
      (fun s hs => htests_y ⟨s, hs⟩)
  have hm : MeasurableSet {z : X × Y | 0 ≤ k z} := measurableSet_le measurable_const hk.measurable
  exact (Measure.ae_prod_iff_ae_ae hm).mpr ((Measure.ae_ae_comm hm).mpr hsections)

end ThesisCommon
