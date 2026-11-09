import PL1.FiniteCoordinateKernels
import PL1.SingularResolvents

/-!
# Finite tail events with small Haar mass and large resolvent mass

The events are the actual coordinate-average events used in the singular-carrier
proof. Their finite supports avoid any prescribed initial segment. Their Haar
probabilities tend to zero, while every positive-time Schur resolvent assigns
probabilities tending to one.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace PL1.TailSpikeEvents
open Walsh Carrier CarrierAsymptotics Noise FiniteCoordinateKernels

/-- The coordinates genuinely used by the dyadic average after deleting `d`. -/
def support (d r : ℕ) : Finset ℕ := (Finset.range (2 ^ r)).image (d + ·)

theorem support_disjoint_prefix (d r : ℕ) :
    Disjoint (support d r) (Finset.range d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hj hjd
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
  have := Finset.mem_range.mp hjd
  omega

theorem highEvent_dependsOn (d r : ℕ) : DependsOn (support d r) (highEvent d r) := by
  classical
  intro x y hxy
  have havg : Carrier.average d r x = Carrier.average d r y := by
    unfold Carrier.average
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg signValue (hxy (d + j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  simp only [highEvent, Set.mem_ofPred_eq, havg]

theorem tendsto_haar_highEvent (d : ℕ) :
    Tendsto (fun r => haar.real (highEvent d r)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    summable_haar_failure_bound.tendsto_atTop_zero
  intro r
  have h := ENNReal.toReal_mono (by finiteness) (haar_highEvent_le d r)
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity :
    0 ≤ (1 / 2 : ℝ) ^ r / (threshold r) ^ 2)] using h

theorem tendsto_schur_resolvent_highEvent (d : ℕ) (t : PositiveTime) :
    Tendsto (fun r => (resolventMeasure schurRates t).real (highEvent d r))
      atTop (𝓝 1) := by
  let := isProbabilityMeasure_resolventMeasure schurRates t.property
  have hae : ∀ᵐ x ∂resolventMeasure schurRates t, x ∈ commonSet d :=
    (mem_ae_iff_prob_eq_one (measurableSet_commonSet d)).mpr
      (schur_resolvent_commonSet t d)
  have hlim : Tendsto (fun r => ∫ x, (highEvent d r).indicator (fun _ => (1 : ℝ)) x
      ∂resolventMeasure schurRates t)
      atTop (𝓝 (∫ _x, (1 : ℝ) ∂resolventMeasure schurRates t)) := by
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

/-- One actual finite tail event simultaneously has the two requested masses. -/
theorem exists_highEvent (d : ℕ) (t : PositiveTime) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℕ, haar.real (highEvent d r) < δ ∧
      1 - δ < (resolventMeasure schurRates t).real (highEvent d r) := by
  have hhaar := (tendsto_haar_highEvent d).eventually (gt_mem_nhds hδ)
  have hres := (tendsto_schur_resolvent_highEvent d t).eventually
    (lt_mem_nhds (by linarith : 1 - δ < (1 : ℝ)))
  exact (hhaar.and hres).exists

theorem exists_finite_tail_event (d : ℕ) (t : PositiveTime) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : Finset ℕ) (B : Set Walsh.Group),
      Disjoint S (Finset.range d) ∧ MeasurableSet B ∧ DependsOn S B ∧
      haar.real B < δ ∧ 1 - δ < (resolventMeasure schurRates t).real B := by
  obtain ⟨r, hh, hr⟩ := exists_highEvent d t hδ
  exact ⟨support d r, highEvent d r, support_disjoint_prefix d r,
    measurableSet_highEvent d r, highEvent_dependsOn d r, hh, hr⟩

end PL1.TailSpikeEvents
