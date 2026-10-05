import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Positivity can be tested on a measure-dense algebra. The proof controls
the change in a set integral by the integral of the norm on the symmetric
difference, then uses absolute continuity of an integrable function. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped symmDiff ENNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem norm_setIntegral_sub_le_symmDiff {f : X → ℝ} (hf : Integrable f μ)
    {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ‖(∫ x in s, f x ∂μ) - ∫ x in t, f x ∂μ‖ ≤ ∫ x in s ∆ t, ‖f x‖ ∂μ := by
  rw [← integral_indicator hs, ← integral_indicator ht,
    ← integral_sub (hf.indicator hs) (hf.indicator ht)]
  calc
    ‖∫ x, s.indicator f x - t.indicator f x ∂μ‖ ≤
        ∫ x, ‖s.indicator f x - t.indicator f x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x in s ∆ t, ‖f x‖ ∂μ := by
      rw [← integral_indicator (hs.symmDiff ht)]
      congr 1
      funext x
      by_cases hx : x ∈ s <;> by_cases hy : x ∈ t <;> simp [hx, hy, Set.mem_symmDiff]

theorem exists_tendsto_setIntegral_of_measureDense {𝒜 : Set (Set X)}
    (h𝒜 : μ.MeasureDense 𝒜) {f : X → ℝ} (hf : Integrable f μ)
    (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    ∃ t : ℕ → Set X, (∀ n, t n ∈ 𝒜) ∧
      Tendsto (fun n => ∫ x in t n, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := by
  have hex (n : ℕ) : ∃ t ∈ 𝒜, μ (s ∆ t) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    h𝒜.approx s hs hμs _ (by positivity)
  choose t ht happrox using hex
  have hmeasure : Tendsto (fun n => μ (s ∆ t n)) atTop (𝓝 0) := by
    have hlim := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    simp only [ENNReal.ofReal_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le _) (fun n => (happrox n).le)
  have hnorm := hf.norm.tendsto_setIntegral_nhds_zero hmeasure
  have hdist : Tendsto (fun n => dist (∫ x in s, f x ∂μ) (∫ x in t n, f x ∂μ)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnorm
      (fun _ => dist_nonneg) (fun n => by
        rw [Real.dist_eq]
        exact norm_setIntegral_sub_le_symmDiff hf hs (h𝒜.measurable _ (ht n)))
  have hlim : Tendsto (fun n => ∫ x in t n, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) :=
    tendsto_const_nhds.congr_dist hdist
  exact ⟨t, ht, hlim⟩

/-- A countability hypothesis is not needed for this deterministic test.
It will be used later to make countably many kernel tests hold off one null set. -/
theorem ae_nonneg_of_setIntegral_nonneg_of_measureDense {𝒜 : Set (Set X)}
    (h𝒜 : μ.MeasureDense 𝒜) {f : X → ℝ} (hf : Integrable f μ)
    (hpos : ∀ s ∈ 𝒜, 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  apply ae_nonneg_of_forall_setIntegral_nonneg hf
  intro s hs hμs
  obtain ⟨t, ht, hlim⟩ := exists_tendsto_setIntegral_of_measureDense h𝒜 hf s hs hμs.ne
  exact ge_of_tendsto' hlim (fun n => hpos _ (ht n))

theorem ae_nonneg_of_setIntegral_nonneg_on_algebra [IsFiniteMeasure μ]
    {𝒜 : Set (Set X)} (h𝒜 : IsSetAlgebra 𝒜)
    (hgen : ‹MeasurableSpace X› = MeasurableSpace.generateFrom 𝒜)
    {f : X → ℝ} (hf : Integrable f μ)
    (hpos : ∀ s ∈ 𝒜, 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f :=
  ae_nonneg_of_setIntegral_nonneg_of_measureDense
    (Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ h𝒜 hgen) hf hpos

/-- The integral of |f| is detected by signed indicators 2*1_s-1 from any
generating algebra. This is the scalar duality step of the modulus-kernel proof. -/
theorem exists_tendsto_setIntegral_of_generating_algebra
    {𝒜 : Set (Set X)} (h𝒜 : IsSetAlgebra 𝒜)
    (hgen : ‹MeasurableSpace X› = MeasurableSpace.generateFrom 𝒜)
    {f : X → ℝ} (hf : Integrable f μ) (s : Set X) (hs : MeasurableSet s) :
    ∃ t : ℕ → Set X, (∀ n, t n ∈ 𝒜) ∧
      Tendsto (fun n => ∫ x in t n, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := by
  let ρ := μ.withDensity (fun x => ENNReal.ofReal ‖f x‖)
  letI : IsFiniteMeasure ρ := isFiniteMeasure_withDensity_ofReal hf.norm.2
  have hd := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite ρ h𝒜 hgen
  have hex (n : ℕ) : ∃ t ∈ 𝒜, ρ (s ∆ t) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    hd.approx s hs (measure_ne_top _ _) _ (by positivity)
  choose t ht happrox using hex
  have hbound (n : ℕ) :
      dist (∫ x in s, f x ∂μ) (∫ x in t n, f x ∂μ) ≤ 1 / ((n : ℝ) + 1) := by
    have hsd := hs.symmDiff (hd.measurable _ (ht n))
    have hnorm : (∫ x in s ∆ t n, ‖f x‖ ∂μ) = (ρ (s ∆ t n)).toReal := by
      change _ = (μ.withDensity (fun x => ENNReal.ofReal ‖f x‖) (s ∆ t n)).toReal
      rw [withDensity_apply _ hsd,
        integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable.restrict]
      simp only [ofReal_norm_eq_enorm]
    calc
      dist (∫ x in s, f x ∂μ) (∫ x in t n, f x ∂μ) ≤ ∫ x in s ∆ t n, ‖f x‖ ∂μ := by
        rw [Real.dist_eq]
        exact norm_setIntegral_sub_le_symmDiff hf hs (hd.measurable _ (ht n))
      _ = (ρ (s ∆ t n)).toReal := hnorm
      _ ≤ (ENNReal.ofReal (1 / ((n : ℝ) + 1))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (happrox n).le
      _ = _ := ENNReal.toReal_ofReal (by positivity)
  have hdist : Tendsto (fun n => dist (∫ x in s, f x ∂μ) (∫ x in t n, f x ∂μ)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun _ => dist_nonneg) hbound
  exact ⟨t, ht, tendsto_const_nhds.congr_dist hdist⟩

/-- Signed indicators from a generating algebra detect the absolute integral
for any measure. Approximation uses the finite measure |f| dμ. -/
theorem integral_abs_le_of_signed_algebra_tests
    {𝒜 : Set (Set X)} (h𝒜 : IsSetAlgebra 𝒜)
    (hgen : ‹MeasurableSpace X› = MeasurableSpace.generateFrom 𝒜)
    {f : X → ℝ} (hm : Measurable f) (hf : Integrable f μ) (b : ℝ)
    (hbound : ∀ s ∈ 𝒜, 2 * (∫ x in s, f x ∂μ) - (∫ x, f x ∂μ) ≤ b) :
    (∫ x, |f x| ∂μ) ≤ b := by
  let s : Set X := {x | 0 ≤ f x}
  have hs : MeasurableSet s := measurableSet_le measurable_const hm
  obtain ⟨t, ht, hlim⟩ := exists_tendsto_setIntegral_of_generating_algebra h𝒜 hgen hf s hs
  have hb : 2 * (∫ x in s, f x ∂μ) - (∫ x, f x ∂μ) ≤ b :=
    le_of_tendsto' ((hlim.const_mul 2).sub_const _) (fun n => hbound _ (ht n))
  have heq : (∫ x, |f x| ∂μ) = 2 * (∫ x in s, f x ∂μ) - (∫ x, f x ∂μ) := by
    rw [← integral_indicator hs, ← integral_const_mul,
      ← integral_sub ((hf.indicator hs).const_mul 2) hf]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : 0 ≤ f x
      · simp [s, hx, abs_of_nonneg hx]; ring
      · simp [s, hx, abs_of_neg (lt_of_not_ge hx)]
  exact heq.trans_le hb

/-- Positivity tested on a subalgebra suffices for functions measurable with
respect to that subalgebra. The conclusion uses the original measure. -/
theorem ae_nonneg_of_setIntegral_nonneg_on_subalgebra [IsFiniteMeasure μ]
    {𝒜 : Set (Set X)} (h𝒜 : IsSetAlgebra 𝒜)
    (hmeas : ∀ s ∈ 𝒜, MeasurableSet s)
    {f : X → ℝ} (hm : @Measurable X ℝ (MeasurableSpace.generateFrom 𝒜) _ f)
    (hf : Integrable f μ) (hpos : ∀ s ∈ 𝒜, 0 ≤ ∫ x in s, f x ∂μ) :
    0 ≤ᵐ[μ] f := by
  let hsub : MeasurableSpace.generateFrom 𝒜 ≤ ‹MeasurableSpace X› :=
    MeasurableSpace.generateFrom_le hmeas
  apply ae_le_of_ae_le_trim (hm := hsub)
  apply @ae_nonneg_of_setIntegral_nonneg_on_algebra X (MeasurableSpace.generateFrom 𝒜)
    (μ.trim hsub) inferInstance 𝒜 h𝒜 rfl f (hf.trim hsub hm.stronglyMeasurable)
  intro s hs
  rw [← setIntegral_trim hsub hm.stronglyMeasurable (MeasurableSpace.measurableSet_generateFrom hs)]
  exact hpos s hs

/-- A generating algebra for the whole space is unnecessary when the tested
function is measurable for the smaller sigma-algebra generated by the tests.
Trimming the measure preserves all integrals used in the preceding argument. -/
theorem integral_abs_le_of_signed_subalgebra_tests
    {𝒜 : Set (Set X)} (h𝒜 : IsSetAlgebra 𝒜)
    (hmeas : ∀ s ∈ 𝒜, MeasurableSet s)
    {f : X → ℝ} (hm : @Measurable X ℝ (MeasurableSpace.generateFrom 𝒜) _ f)
    (hf : Integrable f μ) (b : ℝ)
    (hbound : ∀ s ∈ 𝒜, 2 * (∫ x in s, f x ∂μ) - (∫ x, f x ∂μ) ≤ b) :
    (∫ x, |f x| ∂μ) ≤ b := by
  let hsub : MeasurableSpace.generateFrom 𝒜 ≤ ‹MeasurableSpace X› :=
    MeasurableSpace.generateFrom_le hmeas
  have h := @integral_abs_le_of_signed_algebra_tests X (MeasurableSpace.generateFrom 𝒜)
    (μ.trim hsub) 𝒜 h𝒜 rfl f hm (hf.trim hsub hm.stronglyMeasurable) b
    (fun s hs => by
      rw [← setIntegral_trim hsub hm.stronglyMeasurable
        (MeasurableSpace.measurableSet_generateFrom hs),
        ← integral_trim hsub hm.stronglyMeasurable]
      exact hbound s hs)
  have habs : StronglyMeasurable[MeasurableSpace.generateFrom 𝒜] (fun x => |f x|) := by
    letI : MeasurableSpace X := MeasurableSpace.generateFrom 𝒜
    simpa only [Real.norm_eq_abs] using hm.norm.stronglyMeasurable
  rwa [← integral_trim hsub habs] at h

end ThesisCommon
