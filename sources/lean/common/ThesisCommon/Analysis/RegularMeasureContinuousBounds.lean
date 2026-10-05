import ThesisCommon.Analysis.RegularMeasureCutoff

/-! Elementary sharp mass estimates and small continuous neighborhoods
for finite regular measures on compact Hausdorff spaces. -/
noncomputable section
open Set MeasureTheory Topology
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

theorem continuousMap_integral_le_open_mass (μ : Measure K) [IsFiniteMeasure μ]
    (f : C(K, ℝ)) {U : Set K} (hf : ∀ x, f x ≤ 1)
    (hs : ∀ x ∉ U, f x = 0) : ∫ x, f x ∂μ ≤ μ.real U := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs]
  have hi : Integrable f (μ.restrict U) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have h := integral_mono_ae hi (integrable_const (1 : ℝ))
    (Filter.Eventually.of_forall hf)
  simpa using h

theorem measureReal_le_continuousMap_integral (μ : Measure K) [IsFiniteMeasure μ]
    (f : C(K, ℝ)) (hf : 0 ≤ f) {D : Set K} (hD : MeasurableSet D)
    (hDf : ∀ x ∈ D, 1 ≤ f x) : μ.real D ≤ ∫ x, f x ∂μ := by
  have hi : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have h : (∫ x in D, (1 : ℝ) ∂μ) ≤ ∫ x in D, f x ∂μ :=
    setIntegral_mono_on (integrable_const (1 : ℝ)) hi.integrableOn hD hDf
  have h' : μ.real D ≤ ∫ x in D, f x ∂μ := by simpa using h
  exact h'.trans
    (setIntegral_le_integral hi (Filter.Eventually.of_forall hf))

theorem exists_continuousMap_small_open_neighborhood (μ : Measure K)
    [IsFiniteMeasure μ] [μ.Regular] {F O : Set K}
    (hF : IsCompact F) (hO : IsOpen O) (hFO : F ⊆ O)
    {r : ℝ} (hr : μ.real F < r) :
    ∃ U : Set K, IsOpen U ∧ F ⊆ U ∧ closure U ⊆ O ∧
      ∃ f : C(K, ℝ), (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x ∈ closure U, f x = 1) ∧ (∫ x, f x ∂μ) < r := by
  have hr0 : 0 < r := measureReal_nonneg.trans_lt hr
  have hr' : μ F < ENNReal.ofReal r := by
    exact (ENNReal.toReal_lt_toReal (measure_ne_top μ F) ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal hr0.le] using hr)
  obtain ⟨V, hFV, hV, hVm⟩ := F.exists_isOpen_lt_of_lt (ENNReal.ofReal r) hr'
  have hW : IsOpen (V ∩ O) := hV.inter hO
  obtain ⟨U, hU, hFU, hUW⟩ := hF.exists_isOpen_closure_subset
    (hW.mem_nhdsSet.mpr (subset_inter hFV hFO))
  obtain ⟨f, hfU, hfW, _, hf⟩ := exists_continuous_one_zero_of_isCompact
    (isClosed_closure.isCompact) hW.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hUW)
  refine ⟨U, hU, hFU, hUW.trans inter_subset_right, f, hf, hfU, ?_⟩
  have hVr : μ.real V < r :=
    by simpa only [ENNReal.toReal_ofReal hr0.le] using
      (ENNReal.toReal_lt_toReal (measure_ne_top μ V) ENNReal.ofReal_ne_top).mpr hVm
  exact (continuousMap_integral_le_open_mass μ f (fun x => (hf x).2)
    (fun x hx => hfW hx)).trans_lt
      ((measureReal_mono inter_subset_left).trans_lt hVr)

end ThesisCommon
