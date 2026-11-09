import PEMS.StrictlyLocalizableDecomposition
import ThesisCommon.Analysis.L1OperatorSigmaFiniteRange
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! The exact countable-coordinate assertion of Lemma 4.13 for the
specified decomposition of the output measure space. -/

noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped ENNReal Function

namespace PEMS

variable {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

/-- Lemma 4.13. For any specified strictly localizable decomposition, the
range is contained in the `ℓ¹` sum over a single countable subset of its
indices. Vanishing of the other coordinates is expressed in the actual
partition isometry. Section 4 is stated over the reals. -/
theorem lemma_4_13_countable_range
    (s : J → Set Y) (hs : ∀ j, MeasurableSet (s j)) (_hf : ∀ j, ν (s j) < ⊤)
    (hd : Pairwise (Disjoint on s)) (_hc : (⋃ j, s j) = univ)
    (_hloc : ∀ A : Set Y, MeasurableSet A ↔ ∀ j, MeasurableSet (A ∩ s j))
    (hsum : ∀ A : Set Y, MeasurableSet A → ν A = ∑' j, ν (A ∩ s j))
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ∃ J₀ : Set J, J₀.Countable ∧ ∀ f j, j ∉ J₀ →
      decomposableLpPartitionEquiv (𝕜 := ℝ) (by norm_num) s hs hd
        (sum_restrict_eq_of_apply s hsum) (T f) j = 0 := by
  obtain ⟨Θ, hΘ, hσ, hT⟩ := exists_sigmaFinite_range_part T
  letI := hσ
  refine ⟨{j | 0 < ν.restrict Θ (s j)},
    Measure.countable_meas_pos_of_disjoint_iUnion (μ := ν.restrict Θ) hs hd, ?_⟩
  intro f j hj
  have hzero : ν (s j ∩ Θ) = 0 := by
    simpa only [Set.mem_setOf_eq, not_lt, nonpos_iff_eq_zero, Measure.restrict_apply (hs j)]
      using hj
  change lebesgueLpRestrict (𝕜 := ℝ) (s j) (T f) = 0
  have hTf : T f =ᵐ[ν.restrict (s j)] 0 := by
    change ∀ᵐ y ∂ν.restrict (s j), T f y = 0
    have hTout : ∀ᵐ y ∂ν.restrict Θᶜ, T f y = 0 := hT f
    rw [ae_restrict_iff' (hs j)]
    filter_upwards [(ae_restrict_iff' hΘ.compl).mp hTout,
      measure_eq_zero_iff_ae_notMem.mp hzero] with y hy hnot hys
    exact hy (fun hyΘ => hnot ⟨hys, hyΘ⟩)
  apply Lp.ext
  filter_upwards [lebesgueLpRestrict_coe (𝕜 := ℝ) (s j) (T f), hTf,
    Lp.coeFn_zero ℝ 1 (ν.restrict (s j))] with y h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

end PEMS
