import PL1.TailSpikes

/-!
# Finite tail spikes for the constant-rate construction

The same actual coordinate-average events concentrate every probability
measure carried by the displayed common singular carrier. In particular,
they concentrate the constant-rate resolvent as well as the Schur resolvent.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace PL1.TailSpikeEvents
open Walsh Carrier CarrierAsymptotics Noise FiniteCoordinateKernels

theorem tendsto_probability_highEvent_of_commonSet (ν : Measure Walsh.Group)
    [IsProbabilityMeasure ν] (d : ℕ) (hν : ν (commonSet d) = 1) :
    Tendsto (fun r => ν.real (highEvent d r)) atTop (𝓝 1) := by
  have hae : ∀ᵐ x ∂ν, x ∈ commonSet d :=
    (mem_ae_iff_prob_eq_one (measurableSet_commonSet d)).mpr hν
  have hlim : Tendsto (fun r => ∫ x, (highEvent d r).indicator (fun _ => (1 : ℝ)) x ∂ν)
      atTop (𝓝 (∫ _x, (1 : ℝ) ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro r
      exact (measurable_const.indicator (measurableSet_highEvent d r)).aestronglyMeasurable
    · exact integrable_const 1
    · intro r
      exact ae_of_all _ (fun x => by
        by_cases hx : x ∈ highEvent d r <;> simp [hx])
    · filter_upwards [hae] with x hx
      change x ∈ liminf (highEvent d) atTop at hx
      rw [mem_liminf_iff_eventually_mem] at hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with r hr
      simp [hr]
  simpa only [integral_indicator_const _ (measurableSet_highEvent d _),
    integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, mul_one] using hlim

theorem tendsto_constant_resolvent_highEvent (d : ℕ) (t : PositiveTime) :
    Tendsto (fun r => (resolventMeasure constantRates t).real (highEvent d r))
      atTop (𝓝 1) := by
  let := isProbabilityMeasure_resolventMeasure constantRates t.property
  exact tendsto_probability_highEvent_of_commonSet _ d (constant_resolvent_commonSet t d)

theorem exists_constant_highEvent (d : ℕ) (t : PositiveTime) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℕ, haar.real (highEvent d r) < δ ∧
      1 - δ < (resolventMeasure constantRates t).real (highEvent d r) := by
  have hhaar := (tendsto_haar_highEvent d).eventually (gt_mem_nhds hδ)
  have hres := (tendsto_constant_resolvent_highEvent d t).eventually
    (lt_mem_nhds (by linarith : 1 - δ < (1 : ℝ)))
  exact (hhaar.and hres).exists

theorem exists_constant_finite_tail_event (d : ℕ) (t : PositiveTime)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : Finset ℕ) (B : Set Walsh.Group),
      Disjoint S (Finset.range d) ∧ MeasurableSet B ∧ DependsOn S B ∧
      haar.real B < δ ∧ 1 - δ < (resolventMeasure constantRates t).real B := by
  obtain ⟨r, hh, hr⟩ := exists_constant_highEvent d t hδ
  exact ⟨support d r, highEvent d r, support_disjoint_prefix d r,
    measurableSet_highEvent d r, highEvent_dependsOn d r, hh, hr⟩

end PL1.TailSpikeEvents

namespace PL1.TailSpikes
open Noise

theorem exists_constant_family (d : ℕ) (t : PositiveTime) {δ : ℝ} (hδ : 0 < δ) :
    Nonempty (RateFamily constantRates d t δ) :=
  exists_rateFamily_of_event constantRates d t δ
    (TailSpikeEvents.exists_constant_finite_tail_event d t hδ)

end PL1.TailSpikes
