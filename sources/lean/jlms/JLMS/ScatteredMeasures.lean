import JLMS.ScatteredTopology
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# The measure-theoretic core of Rudin's theorem

Regularity gives full mass to the support without a countability assumption
on the topology: compact subsets outside the support admit finite covers by
null open sets. A nonzero atomless remainder would then have a nonempty
support with an isolated point, contradicting atomlessness on a scattered space.
-/

noncomputable section

open Filter Set MeasureTheory Topology
open scoped ENNReal

namespace JLMS

variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]

omit [BorelSpace K] in
/-- Compact sets disjoint from the support are null, using a finite open cover. -/
theorem measure_compact_eq_zero_outside_support (μ : Measure K)
    {C : Set K} (hC : IsCompact C) (hCs : C ⊆ μ.supportᶜ) : μ C = 0 := by
  classical
  have hnull (x : ↥(μ.supportᶜ)) : ∃ U : Set K, x.val ∈ U ∧ IsOpen U ∧ μ U = 0 := by
    have hx := (nhds_basis_opens x.val).notMem_measureSupport.mp x.property
    obtain ⟨U, ⟨hxU, hU⟩, hzero⟩ := hx
    exact ⟨U, hxU, hU, hzero⟩
  choose U hxU hU hzero using hnull
  have hcover : C ⊆ ⋃ x, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hCs hx⟩, hxU ⟨x, hCs hx⟩⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hU hcover
  apply le_antisymm _ bot_le
  calc
    μ C ≤ μ (⋃ x ∈ t, U x) := measure_mono ht
    _ ≤ ∑ x ∈ t, μ (U x) := measure_biUnion_finset_le t U
    _ = 0 := by simp [hzero]

/-- A regular measure is concentrated on its support even on a space with no
countable base. This is separate from mathlib's Lindelöf support theorem. -/
theorem measure_compl_support_eq_zero_of_regular (μ : Measure K) [μ.Regular] :
    μ μ.supportᶜ = 0 := by
  by_contra h
  have hpos : 0 < μ μ.supportᶜ := bot_lt_iff_ne_bot.mpr h
  obtain ⟨C, hCs, hC, hmass⟩ := μ.isOpen_compl_support.exists_lt_isCompact hpos
  rw [measure_compact_eq_zero_outside_support μ hC hCs] at hmass
  exact (lt_irrefl 0) hmass

theorem measure_support_nonempty_of_regular (μ : Measure K) [μ.Regular] (hμ : μ ≠ 0) :
    μ.support.Nonempty := by
  by_contra h
  have hs : μ.support = ∅ := not_nonempty_iff_eq_empty.mp h
  have hz := measure_compl_support_eq_zero_of_regular μ
  rw [hs, compl_empty] at hz
  exact hμ (Measure.measure_univ_eq_zero.mp hz)

omit [TopologicalSpace K] [BorelSpace K] in
/-- There are only countably many points of positive mass in a finite measure. -/
theorem countable_measure_atoms [MeasurableSingletonClass K] (μ : Measure K) [IsFiniteMeasure μ] :
    Set.Countable {x : K | 0 < μ {x}} := by
  simpa using Measure.countable_meas_level_set_pos (μ := μ) measurable_id

variable [T2Space K]

/-- The atomicity assertion underlying Rudin: a finite regular measure on a
scattered Hausdorff space assigns zero mass to the complement of its point atoms. -/
theorem measure_compl_atoms_eq_zero_of_scattered (hK : IsScattered K)
    (μ : Measure K) [IsFiniteMeasure μ] [μ.Regular] :
    μ ({x : K | 0 < μ {x}}ᶜ) = 0 := by
  classical
  let S : Set K := {x | 0 < μ {x}}
  let ν := μ.restrict Sᶜ
  letI : ν.Regular := Measure.Regular.restrict_of_measure_ne_top (measure_ne_top μ Sᶜ)
  have hsingle (x : K) : ν {x} = 0 := by
    change μ.restrict Sᶜ {x} = 0
    rw [Measure.restrict_apply (measurableSet_singleton x)]
    by_cases hx : x ∈ S
    · have he : ({x} : Set K) ∩ Sᶜ = ∅ := by
        ext y
        simp only [mem_inter_iff, mem_singleton_iff, mem_compl_iff, mem_empty_iff_false, iff_false]
        rintro ⟨rfl, hy⟩
        exact hy hx
      rw [he, measure_empty]
    · have hz : μ {x} = 0 := le_antisymm (le_of_not_gt hx) bot_le
      exact measure_mono_null inter_subset_left hz
  have hν : ν = 0 := by
    by_contra h
    obtain ⟨x, hx, U, hU, hinter⟩ := hK ν.support (measure_support_nonempty_of_regular ν h)
    have hxU : x ∈ U := by
      have : x ∈ ν.support ∩ U := by rw [hinter]; exact mem_singleton x
      exact this.2
    have hmass : 0 < ν U := (Measure.mem_support_iff_forall x).mp hx U (hU.mem_nhds hxU)
    have heq : ν U = ν {x} := calc
      ν U = ν (U ∩ ν.support) :=
        (measure_inter_conull (measure_compl_support_eq_zero_of_regular ν)).symm
      _ = ν {x} := by rw [inter_comm, hinter]
    rw [heq, hsingle x] at hmass
    exact (lt_irrefl 0) hmass
  exact Measure.restrict_eq_zero.mp hν

/-- The finite regular measure is the sum of its countably many weighted
Dirac masses. The index set is the actual set of positive point atoms. -/
theorem measure_eq_sum_atoms_of_scattered (hK : IsScattered K)
    (μ : Measure K) [IsFiniteMeasure μ] [μ.Regular] :
    μ = Measure.sum (fun x : ↥{x : K | 0 < μ {x}} => μ {x.val} • Measure.dirac x.val) := by
  classical
  let S : Set K := {x | 0 < μ {x}}
  have hS := countable_measure_atoms μ
  have hconull : ∀ᵐ x ∂μ, x ∈ S := measure_compl_atoms_eq_zero_of_scattered hK μ
  have heq : S = ⋃ x : S, ({x.val} : Set K) := by
    ext x
    simp
  letI : Countable S := hS.to_subtype
  calc
    μ = μ.restrict S := (Measure.restrict_eq_self_of_ae_mem hconull).symm
    _ = μ.restrict (⋃ x : S, ({x.val} : Set K)) := by rw [← heq]
    _ = Measure.sum (fun x : S => μ.restrict {x.val}) := by
      apply Measure.restrict_iUnion
      · intro x y hxy
        exact disjoint_singleton.mpr (Subtype.coe_ne_coe.mpr hxy)
      · intro x
        exact measurableSet_singleton x.val
    _ = Measure.sum (fun x : S => μ {x.val} • Measure.dirac x.val) := by
      congr 1
      funext x
      exact Measure.restrict_singleton μ x.val

end JLMS
