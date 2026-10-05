import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.RCLike.Lemmas

/-! Genuine uniform simple-function approximation for scalar L∞. The
approximation itself permits arbitrary measures. For finite measures it
also gives approximation by explicit finite sums of indicator classes. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
variable {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
variable {μ : Measure X}

theorem rclike_lInfinity_ae_norm_le_norm (f : Lp 𝕜 ∞ μ) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  filter_upwards [enorm_ae_le_eLpNormEssSup f μ] with x hx
  have ht : eLpNormEssSup f μ ≠ ∞ := by
    simpa only [eLpNorm_exponent_top] using (Lp.memLp f).2.ne
  have hh := ENNReal.toReal_mono ht hx
  simpa only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, Lp.norm_def,
    eLpNorm_exponent_top] using hh

theorem rclike_lInfinity_norm_le_of_ae_bound (f : Lp 𝕜 ∞ μ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  rw [Lp.norm_def, eLpNorm_exponent_top]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hf)).trans_eq
    (ENNReal.toReal_ofReal hC)

theorem exists_simpleFunc_approx_on_finite_balls
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : X → 𝕜) (hf : Measurable f)
    (s : Finset 𝕜) (ε : ℝ) :
    ∃ g : SimpleFunc X 𝕜,
      ∀ x, (∃ c ∈ s, ‖f x - c‖ < ε) → ‖f x - g x‖ < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert c s hc ih =>
    obtain ⟨g, hg⟩ := ih
    let A : Set X := {x | ‖f x - c‖ < ε}
    have hA : MeasurableSet A := measurableSet_lt (hf.sub_const c).norm measurable_const
    refine ⟨(SimpleFunc.const X c).piecewise A hA g, ?_⟩
    intro x hx
    by_cases hxA : x ∈ A
    · simpa only [SimpleFunc.piecewise_apply, if_pos hxA, SimpleFunc.const_apply] using hxA
    · rw [SimpleFunc.piecewise_apply, if_neg hxA]
      apply hg x
      obtain ⟨d, hd, hdist⟩ := hx
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact False.elim (hxA hdist)
      · exact ⟨d, hd, hdist⟩

theorem exists_rclike_lInfinity_simple_approximation
    (f : Lp 𝕜 ∞ μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : SimpleFunc X 𝕜, ‖f - (g.memLp_top μ).toLp g‖ < ε := by
  classical
  letI : MeasurableSpace 𝕜 := borel 𝕜
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  obtain ⟨s, _, hfin, hcover⟩ :=
    (isCompact_closedBall (0 : 𝕜) ‖f‖).finite_cover_balls (half_pos hε)
  obtain ⟨g, hg⟩ := exists_simpleFunc_approx_on_finite_balls f
    (Lp.stronglyMeasurable f).measurable hfin.toFinset (ε/2)
  refine ⟨g, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  apply rclike_lInfinity_norm_le_of_ae_bound _ (half_pos hε).le
  filter_upwards [rclike_lInfinity_ae_norm_le_norm f,
    Lp.coeFn_sub f ((g.memLp_top μ).toLp g), (g.memLp_top μ).coeFn_toLp] with x hx hsub hgx
  rw [hsub, Pi.sub_apply, hgx]
  apply (hg x ?_).le
  have hball : f x ∈ Metric.closedBall (0 : 𝕜) ‖f‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hcover hball)
  exact ⟨c, by simpa using hc, by simpa only [Metric.mem_ball, dist_eq_norm] using hxc⟩

theorem rclike_lInfinity_simple_eq_sum_indicators [IsFiniteMeasure μ]
    (g : SimpleFunc X 𝕜) :
    (g.memLp_top μ).toLp g = ∑ c ∈ g.range,
      indicatorConstLp ∞ (g.measurableSet_fiber c) (measure_ne_top μ _) c := by
  classical
  let I : 𝕜 → Lp 𝕜 ∞ μ := fun c =>
    indicatorConstLp ∞ (g.measurableSet_fiber c) (measure_ne_top μ _) c
  have hsum (s : Finset 𝕜) :
      (fun x => (∑ c ∈ s, I c) x) =ᵐ[μ]
        fun x => ∑ c ∈ s, (g ⁻¹' {c}).indicator (fun _ => c) x := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero 𝕜 ∞ μ
    | @insert c s hc ih =>
      simp only [Finset.sum_insert hc]
      filter_upwards [Lp.coeFn_add (I c) (∑ d ∈ s, I d),
        (indicatorConstLp_coeFn : I c =ᵐ[μ] (g ⁻¹' {c}).indicator (fun _ => c)), ih] with x hx hc' hs
      simp only [hx, Pi.add_apply, hs]
      exact congrArg (fun z => z + ∑ d ∈ s, (g ⁻¹' {d}).indicator (fun _ => d) x) hc'
  apply Lp.ext
  filter_upwards [(g.memLp_top μ).coeFn_toLp, hsum g.range] with x hx hsumx
  rw [hx, hsumx]
  rw [Finset.sum_eq_single (g x)]
  · simp
  · intro c hc hne
    simp [Ne.symm hne]
  · exact fun h => False.elim (h (g.mem_range_self x))

theorem exists_rclike_lInfinity_indicator_sum_approximation [IsFiniteMeasure μ]
    (f : Lp 𝕜 ∞ μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset 𝕜, ∃ A : 𝕜 → Set X, ∃ hA : ∀ c, MeasurableSet (A c),
      ‖f - ∑ c ∈ s, indicatorConstLp ∞ (hA c) (measure_ne_top μ _) c‖ < ε := by
  obtain ⟨g, hg⟩ := exists_rclike_lInfinity_simple_approximation f hε
  refine ⟨g.range, fun c => g ⁻¹' {c}, g.measurableSet_fiber, ?_⟩
  rwa [← rclike_lInfinity_simple_eq_sum_indicators]

end ThesisCommon
