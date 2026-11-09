import ThesisCommon.Analysis.LpHaarMeanEstimates

/-! Dyadic averaging fixes the child-level Haar vectors and annihilates their
parent-level averages.  All statements concern actual Lp operators. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical Function
namespace ThesisCommon

theorem lpHaarExtend_const {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]
    (s : Set α) (hs : MeasurableSet s) (c : 𝕜) :
    lebesgueLpExtend (𝕜 := 𝕜) s hs (Lp.const p (μ.restrict s) c) =
      indicatorConstLp p hs (measure_ne_top μ s) c := by
  apply Lp.ext
  have hc := (ae_restrict_iff' hs).mp (Lp.coeFn_const p (μ.restrict s) c)
  filter_upwards [lebesgueLpExtend_coe (𝕜 := 𝕜) s hs (Lp.const p (μ.restrict s) c),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := measure_ne_top μ s) (c := c), hc]
    with x h₁ h₂ h₃
  rw [h₁, h₂]
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx]
    exact h₃ hx
  · simp [hx]

theorem lpHaarPartitionMean_fix_indicator {𝕜 α ι : Type*} [RCLike 𝕜] [MeasurableSpace α]
    [Countable ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]
    (hp : p ≠ ∞) (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i)
    (hm : ∀ i, μ (s i) ≠ 0) (i : ι) (c : 𝕜) :
    lpHaarPartitionMean hp s hs hd hc hm (indicatorConstLp p (hs i) (measure_ne_top μ (s i)) c) =
      indicatorConstLp p (hs i) (measure_ne_top μ (s i)) c := by
  rw [← lpHaarExtend_const (s i) (hs i) c]
  apply (lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp s hs hd hc).injective
  apply lp.ext
  funext j
  rw [lpHaarPartitionMean_coordinate]
  change lpHaarMean hp (lebesgueLpRestrict (𝕜 := 𝕜) (s j)
      (lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i) (Lp.const p (μ.restrict (s i)) c))) =
    lebesgueLpRestrict (𝕜 := 𝕜) (s j)
      (lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i) (Lp.const p (μ.restrict (s i)) c))
  by_cases hji : j = i
  · subst j
    rw [lebesgueLpRestrict_extend]
    exact lpHaarMean_const hp (by simpa only [Measure.restrict_apply_univ] using hm i) c
  · rw [lebesgueLpRestrict_extend_disjoint (hs j) (hs i) (hd hji), map_zero]

theorem lpHaarDyadicMean_fix_cell (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n k : ℕ) (hk : k < 2 ^ n) (c : 𝕜) :
    lpHaarDyadicMean 𝕜 p hp n
      (indicatorConstLp p.val (show MeasurableSet (lpHaarCell n k) from measurableSet_Ioc)
        (measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _) c) =
      indicatorConstLp p.val measurableSet_Ioc
        (measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarCell n k)) c :=
  lpHaarPartitionMean_fix_indicator hp (fun k : Fin (2 ^ n) => lpHaarCell n k)
    (fun _ => measurableSet_Ioc) (lpHaarLevelCells_disjoint n) (lpHaarLevelCells_cover n)
    (lpHaarLevelCells_nonzero n) ⟨k, hk⟩ c

theorem lpHaarDyadicMean_fix_haar (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n k : ℕ) (hk : k < 2 ^ n) :
    lpHaarDyadicMean 𝕜 p hp (n + 1) (lpHaarDyadic 𝕜 p n k) = lpHaarDyadic 𝕜 p n k := by
  have hk₁ : 2 * k < 2 ^ (n + 1) := by rw [pow_succ]; omega
  have hk₂ : 2 * k + 1 < 2 ^ (n + 1) := by rw [pow_succ]; omega
  unfold lpHaarDyadic lpHaarVector
  rw [map_sub, lpHaarDyadicMean_fix_cell 𝕜 p hp (n + 1) (2 * k) hk₁,
    lpHaarDyadicMean_fix_cell 𝕜 p hp (n + 1) (2 * k + 1) hk₂]

theorem lpHaarDyadic_restrict_other_parent (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n k j : ℕ) (hjk : j ≠ k) :
    lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n j) (lpHaarDyadic 𝕜 p n k) = 0 := by
  apply Lp.ext
  filter_upwards [lebesgueLpRestrict_coe (𝕜 := 𝕜) (lpHaarCell n j) (lpHaarDyadic 𝕜 p n k),
    ae_restrict_of_ae (lpHaarDyadic_zero_off 𝕜 p n k),
    ae_restrict_mem (show MeasurableSet (lpHaarCell n j) from measurableSet_Ioc),
    Lp.coeFn_zero 𝕜 p.val ((volume.restrict (Icc (0 : ℝ) 1)).restrict (lpHaarCell n j))]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₄]
  exact h₂ (fun hx => Set.disjoint_left.mp (lpHaarCell_disjoint_sameLevel n hjk) h₃ hx)

theorem lpHaarDyadicMean_kill_haar (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n k : ℕ) (hk : k < 2 ^ n) :
    lpHaarDyadicMean 𝕜 p hp n (lpHaarDyadic 𝕜 p n k) = 0 := by
  apply (lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp
    (fun j : Fin (2 ^ n) => lpHaarCell n j) (fun _ => measurableSet_Ioc)
    (lpHaarLevelCells_disjoint n) (lpHaarLevelCells_cover n)).injective
  apply lp.ext
  funext j
  change lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n j)
    (lpHaarDyadicMean 𝕜 p hp n (lpHaarDyadic 𝕜 p n k)) = _
  rw [lpHaarDyadicMean_coordinate]
  rw [map_zero]
  change lpHaarMean hp (lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n j) (lpHaarDyadic 𝕜 p n k)) = 0
  by_cases hjk : j.val = k
  · have hi : ∫ x, lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarDyadic 𝕜 p n k) x
        ∂((volume.restrict (Icc (0 : ℝ) 1)).restrict (lpHaarCell n k)) = 0 := by
      rw [integral_congr_ae (lebesgueLpRestrict_coe (𝕜 := 𝕜) (lpHaarCell n k)
        (lpHaarDyadic 𝕜 p n k)),
        setIntegral_eq_integral_of_ae_compl_eq_zero (lpHaarDyadic_zero_off 𝕜 p n k),
        lpHaarDyadic_integral_zero 𝕜 p n k hk]
    rw [hjk, lpHaarMean_apply, hi, mul_zero, map_zero]
  · rw [lpHaarDyadic_restrict_other_parent 𝕜 p n k j hjk, map_zero]

end ThesisCommon
