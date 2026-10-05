import ThesisCommon.Analysis.RegularMeasureContinuousBounds

/-! The recursive step in sharp disjoint-open-set selection. A recurrent
regular measure controls the accumulated continuous neighborhoods; each
new neighborhood retains almost all the prescribed mass. -/
noncomputable section
open Set MeasureTheory Topology Filter
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

theorem exists_isCompact_real_mass_gt (μ : Measure K) [IsFiniteMeasure μ] [μ.Regular]
    {A : Set K} (hA : MeasurableSet A) {r : ℝ} (hr : r < μ.real A) :
    ∃ F ⊆ A, IsCompact F ∧ r < μ.real F := by
  by_cases hr0 : r < 0
  · exact ⟨∅, empty_subset _, isCompact_empty, by simpa using hr0⟩
  have hr0' : 0 ≤ r := le_of_not_gt hr0
  obtain ⟨F, hFA, hF, hm⟩ := hA.exists_lt_isCompact
    ((ENNReal.ofReal_lt_iff_lt_toReal hr0' (measure_ne_top μ A)).mpr hr)
  exact ⟨F, hFA, hF,
    (ENNReal.ofReal_lt_iff_lt_toReal hr0' (measure_ne_top μ F)).mp hm⟩

theorem exists_regularMeasure_open_step
    (μ : ℕ → Measure K) [∀ n, IsFiniteMeasure (μ n)] [∀ n, (μ n).Regular]
    (ν : Measure K) [IsFiniteMeasure ν] [ν.Regular]
    (hrec : ∀ (f : C(K, ℝ)) (r : ℝ), (∫ x, f x ∂ν) < r →
      ∃ᶠ n in atTop, (∫ x, f x ∂μ n) < r)
    (A : ℕ → Set K) (hA : ∀ n, MeasurableSet (A n))
    (hAd : Pairwise (fun i j => Disjoint (A i) (A j)))
    {c ε : ℝ} (hmass : ∀ n, c < (μ n).real (A n)) (hε : 0 < ε)
    (N : ℕ) (D : Set K) (hD : IsCompact D) (q : C(K, ℝ))
    (hq : 0 ≤ q) (hDq : ∀ x ∈ D, 1 ≤ q x) (hqi : (∫ x, q x ∂ν) < ε / 2) :
    ∃ i ≥ N, ∃ U : Set K, IsOpen U ∧ Disjoint (closure U) D ∧
      c - ε < (μ i).real U ∧ ∃ b : C(K, ℝ), 0 ≤ b ∧
        (∀ x ∈ closure U, 1 ≤ b x) ∧ (∫ x, (q + b) x ∂ν) < ε / 2 := by
  have hgap : 0 < ε / 2 - ∫ x, q x ∂ν := sub_pos.mpr hqi
  have hsmall : ∀ᶠ n in atTop, ν.real (A n) < ε / 2 - ∫ x, q x ∂ν :=
    (summable_measure_toReal hA hAd).tendsto_atTop_zero.eventually (gt_mem_nhds hgap)
  obtain ⟨i, hμq, hi, hνA⟩ :=
    ((hrec q (ε / 2) hqi).and_eventually ((eventually_ge_atTop N).and hsmall)).exists
  have hμD : (μ i).real D < ε / 2 :=
    (measureReal_le_continuousMap_integral (μ i) q hq hD.measurableSet hDq).trans_lt hμq
  have hdiff : c - ε < (μ i).real (A i \ D) := by
    have h := le_measureReal_diff (μ := μ i) (s₁ := A i) (s₂ := D)
    have hm := hmass i
    linarith
  obtain ⟨F, hFA, hF, hFm⟩ := exists_isCompact_real_mass_gt (μ i)
    ((hA i).diff hD.measurableSet) hdiff
  have hνF : ν.real F < ε / 2 - ∫ x, q x ∂ν :=
    (measureReal_mono (hFA.trans diff_subset)).trans_lt hνA
  obtain ⟨U, hU, hFU, hUD, b, hb, hbU, hbi⟩ :=
    exists_continuousMap_small_open_neighborhood ν hF hD.isClosed.isOpen_compl
      (fun x hx => (hFA hx).2) hνF
  refine ⟨i, hi, U, hU, disjoint_left.mpr (fun x hx hxD => hUD hx hxD),
    hFm.trans_le (measureReal_mono hFU), b, fun x => (hb x).1,
    fun x hx => (hbU x hx).ge, ?_⟩
  have hqint : Integrable q ν :=
      q.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace q)
  have hbint : Integrable b ν :=
      b.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace b)
  change (∫ x, q x + b x ∂ν) < ε / 2
  rw [integral_add hqint hbint]
  linarith

end ThesisCommon
