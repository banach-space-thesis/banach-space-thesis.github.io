import ThesisCommon.Analysis.IntervalKernelUniformSelection
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-! Small Cantor subsets of positive compact sets for atomless measures. -/
noncomputable section
open MeasureTheory Filter Topology
namespace ThesisCommon

theorem compact_positive_contains_small_cantor
    (ν : Measure UnitInterval) [NoAtoms ν] {K : Set UnitInterval}
    (hK : IsCompact K) (hpos : 0 < ν K) {r : ℝ} (hr : 0 < r) :
    ∃ f : (ℕ → Bool) → UnitInterval, Continuous f ∧ Function.Injective f ∧
      Set.range f ⊆ K ∧ ∀ x y, dist (f x) (f y) ≤ r := by
  have hunc : ¬K.Countable := fun h => hpos.ne' (h.measure_zero ν)
  obtain ⟨P, hP, hPne, hPK⟩ :=
    exists_perfect_nonempty_of_isClosed_of_not_countable hK.isClosed hunc
  obtain ⟨D, _, hD, _, _⟩ := hP.small_diam_splitting hPne (ENNReal.ofReal_pos.mpr hr)
  obtain ⟨f, hfD, hfcont, hfinj⟩ := hD.1.exists_nat_bool_injection hD.2.1
  refine ⟨f, hfcont, hfinj, hfD.trans (hD.2.2.1.trans hPK), ?_⟩
  intro x y
  have hd := (EMetric.edist_le_diam_of_mem (hfD ⟨x, rfl⟩) (hfD ⟨y, rfl⟩)).trans hD.2.2.2
  rw [edist_dist] at hd
  exact (ENNReal.ofReal_le_ofReal_iff hr.le).mp hd

theorem intervalKernel_small_cantor_selection
    {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜)
    (ν : Measure UnitInterval) [IsFiniteMeasure ν] [NoAtoms ν] (hν : ν Set.univ ≠ 0) :
    ∃ (Q : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (n : ℕ)
      (f : (ℕ → Bool) → UnitInterval),
      (Q = T ∨ Q = ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) - T) ∧
      Continuous f ∧ Function.Injective f ∧
      (∀ x, 1 / 2 ≤ ‖intervalOperatorAtom Q (f x)‖) ∧
      Continuous (fun x => intervalOperatorAtom Q (f x)) ∧
      (∀ x, intervalKernelResidualMass Q n (f x) < 1 / 4) ∧
      (∀ x y, dist (f x) (f y) ≤ (1 / (n + 1 : ℝ)) / 4) := by
  obtain ⟨Q, K, hQ, hK, hpos, hlarge, hcont, hunif⟩ :=
    intervalKernel_compact_uniform_selection T ν hν
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hunif (1 / 4) (by norm_num)).exists
  have hr : 0 < (1 / (n + 1 : ℝ)) / 4 := by positivity
  obtain ⟨f, hfcont, hfinj, hfK, hdiam⟩ := compact_positive_contains_small_cantor ν hK hpos hr
  refine ⟨Q, n, f, hQ, hfcont, hfinj, fun x => hlarge _ (hfK ⟨x, rfl⟩), ?_, ?_, hdiam⟩
  · exact hcont.comp_continuous hfcont (fun x => hfK ⟨x, rfl⟩)
  · intro x
    have h := hn (f x) (hfK ⟨x, rfl⟩)
    simpa only [Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg (intervalKernelResidualMass_nonneg Q n (f x))] using h

end ThesisCommon
