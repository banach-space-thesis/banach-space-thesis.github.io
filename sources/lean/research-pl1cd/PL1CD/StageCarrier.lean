import PL1CD.StageBlockEvents
import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.Cofinite

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace PL1CD.StageParameters

theorem errorBound_summable : Summable errorBound := by
  have h := (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2 : ℕ))).mul_left
    ((16 : ℝ)⁻¹)
  change Summable (fun s : ℕ => (16 * (s : ℝ) ^ 2)⁻¹)
  simpa only [mul_inv] using h

def selectedEvent (A : Set ℕ) (s : ℕ) : Set PL1.Walsh.Group := by
  classical
  exact if s ∈ A then stageEvent s else Set.univ

def carrier (A : Set ℕ) : Set PL1.Walsh.Group :=
  PL1.Carrier.eventualSet (selectedEvent A)

theorem measurableSet_selectedEvent (A : Set ℕ) (s : ℕ) :
    MeasurableSet (selectedEvent A s) := by
  classical
  unfold selectedEvent
  split_ifs
  · exact measurableSet_stageEvent s
  · exact MeasurableSet.univ

theorem measurableSet_carrier (A : Set ℕ) : MeasurableSet (carrier A) :=
  PL1.Carrier.measurableSet_eventualSet (measurableSet_selectedEvent A)

theorem haar_carrier_eq_zero (A : Set ℕ) (hA : A.Infinite) :
    PL1.Walsh.haar (carrier A) = 0 := by
  have hsum : (∑' s, PL1.Walsh.haar (stageEvent s)) ≠ ∞ :=
    PL1.Carrier.tsum_measure_ne_top_of_eventually_le PL1.Walsh.haar stageEvent errorBound
      errorBound_summable (fun s => by unfold errorBound; positivity)
      (by filter_upwards [eventually_ge_atTop 1] with s hs; exact haar_stageEvent_le hs)
  have hzero := measure_limsup_atTop_eq_zero hsum
  have hsubset : carrier A ⊆ limsup stageEvent atTop := by
    intro x hx
    change x ∈ liminf (selectedEvent A) atTop at hx
    rw [mem_liminf_iff_eventually_mem] at hx
    have hfreq : ∃ᶠ s : ℕ in atTop, s ∈ A := by
      simpa only [Nat.cofinite_eq_atTop] using hA.frequently_cofinite
    apply mem_limsup_iff_frequently_mem.mpr
    apply (hfreq.and_eventually hx).mono
    intro s hs
    simpa [selectedEvent, hs.1] using hs.2
  exact le_antisymm ((measure_mono hsubset).trans_eq hzero) bot_le

theorem noise_carrier_eq_one (A : Set ℕ) (u : ℝ≥0) :
    PL1.Noise.measure (rates A) u (carrier A) = 1 := by
  classical
  have hsum : (∑' s, PL1.Noise.measure (rates A) u (selectedEvent A s)ᶜ) ≠ ∞ := by
    apply PL1.Carrier.tsum_measure_ne_top_of_eventually_le _
      (fun s => (selectedEvent A s)ᶜ) errorBound errorBound_summable
      (fun s => by unfold errorBound; positivity)
    filter_upwards [eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop : Tendsto (fun s : ℕ => (s : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop (u : ℝ))] with s hs hsu
    by_cases hsA : s ∈ A
    · simpa [selectedEvent, hsA] using noise_stageEvent_compl_le hs A hsA u hsu
    · simp [selectedEvent, hsA]
  exact PL1.Carrier.measure_eventualSet_eq_one _ _ (measurableSet_selectedEvent A) hsum

theorem exists_common_null_carrier (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set PL1.Walsh.Group, MeasurableSet B ∧ PL1.Walsh.haar B = 0 ∧
      ∀ u : ℝ≥0, PL1.Noise.measure (rates A) u B = 1 :=
  ⟨carrier A, measurableSet_carrier A, haar_carrier_eq_zero A hA, noise_carrier_eq_one A⟩

end PL1CD.StageParameters
