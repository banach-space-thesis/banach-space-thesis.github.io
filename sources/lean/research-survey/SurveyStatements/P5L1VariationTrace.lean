import SurveyStatements.P5L1VariationPointwise
import SurveyStatements.P5Support.LpHaarLevelTraces
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Full-sequence local traces for actual bounded scalar L¹ Haar
multipliers. Concrete branch convergence and dominated convergence give
one bounded measurable density for all measurable local sets. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem stepSymbol_stronglyMeasurable (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (n : ℕ) :
    StronglyMeasurable (stepSymbol 𝕜 d n) := by
  have hs (S : Finset (Fin (2 ^ n))) : StronglyMeasurable
      (fun x => ∑ k ∈ S, (lpHaarCell n k).indicator (fun _ => d n k) x) := by
    induction S using Finset.induction_on with
    | empty => simpa using (stronglyMeasurable_const : StronglyMeasurable (fun _ : ℝ => (0 : 𝕜)))
    | @insert k S hk ih =>
        simp_rw [Finset.sum_insert hk]
        exact (stronglyMeasurable_const.indicator measurableSet_Ioc).add ih
  exact hs Finset.univ

theorem stepSymbol_setIntegral (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (n : ℕ) (s : Set ℝ) :
    (∫ x in s, stepSymbol 𝕜 d n x ∂(volume.restrict (Icc (0 : ℝ) 1))) =
      lpHaarLevelTrace d n s := by
  unfold stepSymbol lpHaarLevelTrace
  rw [integral_finset_sum (μ := (volume.restrict (Icc (0 : ℝ) 1)).restrict s)
    (f := fun k : Fin (2 ^ n) => (lpHaarCell n k).indicator (fun _ : ℝ => d n k))
    Finset.univ (fun k _ => (integrable_const (d n k)).indicator
      (show MeasurableSet (lpHaarCell n k) from measurableSet_Ioc))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_indicator_const (d n k)
      (show MeasurableSet (lpHaarCell n k) from measurableSet_Ioc), measureReal_def,
    Measure.restrict_apply (show MeasurableSet (lpHaarCell n k) from measurableSet_Ioc)]
  simp only [Algebra.smul_def, RCLike.algebraMap_eq_ofReal, Set.inter_comm,
    measureReal_def]

theorem exists_full_trace_density (𝕜 : Type*) [RCLike 𝕜]
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hD : ∀ (n : ℕ) (k : Fin (2 ^ n)),
      D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = d n k • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) :
    ∃ m : ℝ → 𝕜, StronglyMeasurable m ∧
      (∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), ‖m x‖ ≤ ‖D‖) ∧
      (∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
        Tendsto (fun n => stepSymbol 𝕜 d n x) atTop (𝓝 (m x))) ∧
      ∀ s : Set ℝ, Tendsto (fun n => lpHaarLevelTrace d n s) atTop
        (𝓝 (∫ x in s, m x ∂(volume.restrict (Icc (0 : ℝ) 1)))) := by
  have hae : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∃ c : 𝕜, Tendsto (fun n => stepSymbol 𝕜 d n x) atTop (𝓝 c) := by
    filter_upwards [lpHaarLevelCells_cover 0] with x hx
    rw [lpHaarLevelCells_union] at hx
    obtain ⟨c, hc, _⟩ := stepSymbol_pointwise_exists_limit 𝕜 D d hD x hx
    exact ⟨c, hc⟩
  obtain ⟨m, hm, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae
    (fun n => (stepSymbol_stronglyMeasurable 𝕜 d n).aestronglyMeasurable) hae
  have hbound : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), ‖m x‖ ≤ ‖D‖ := by
    filter_upwards [hlim] with x hx
    exact le_of_tendsto hx.norm (Eventually.of_forall
      (fun n => stepSymbol_norm_le 𝕜 D d hD n x))
  refine ⟨m, hm, hbound, hlim, ?_⟩
  intro s
  have ht := tendsto_integral_of_dominated_convergence
    (μ := (volume.restrict (Icc (0 : ℝ) 1)).restrict s) (fun _ : ℝ => ‖D‖)
    (fun n => (stepSymbol_stronglyMeasurable 𝕜 d n).aestronglyMeasurable)
    (integrable_const ‖D‖)
    (fun n => Eventually.of_forall (fun x => stepSymbol_norm_le 𝕜 D d hD n x))
    (ae_restrict_of_ae hlim)
  simpa only [stepSymbol_setIntegral] using ht

end SurveyStatements.P5L1Variation
