import ThesisCommon.Analysis.LpHaarStepDensity

/-! A finite step function's Lp norm depends only on its coefficients and
the measures of its disjoint atoms. This is the distribution calculation
underlying faithful Haar blocks, for real and complex coefficients. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable {𝕜 α ι : Type*} [RCLike 𝕜] [MeasurableSpace α] [Fintype ι]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]

def lpHaarPartitionStep (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i)) (a : ι → 𝕜) :
    Lp 𝕜 p μ := ∑ i, indicatorConstLp p (hs i) (measure_ne_top μ (s i)) (a i)

theorem lpHaarPartitionStep_coordinates (hp : p ≠ ∞)
    (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (a : ι → 𝕜) (i : ι) :
    lebesgueLpPartitionEquiv (𝕜 := 𝕜) hp s hs hd hc
      (lpHaarPartitionStep s hs a) i = Lp.const p (μ.restrict (s i)) (a i) := by
  have heq : lebesgueLpPartitionEquiv (𝕜 := 𝕜) hp s hs hd hc
      (lpHaarPartitionStep s hs a) =
      ∑ j, lp.single p j (Lp.const p (μ.restrict (s j)) (a j)) := by
    change lebesgueLpPartition (𝕜 := 𝕜) hp s hs hd hc (lpHaarPartitionStep s hs a) = _
    rw [lpHaarPartitionStep, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← lpHaarExtend_const (s j) (hs j) (a j)]
    exact lebesgueLpPartition_extend hp s hs hd hc j _
  rw [heq]
  simp [lp.coeFn_sum, lp.coeFn_single]

theorem lpHaarPartitionStep_norm_eq (hp : p ≠ ∞)
    (s t : ι → Set α) (hs : ∀ i, MeasurableSet (s i)) (ht : ∀ i, MeasurableSet (t i))
    (hds : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hdt : Pairwise (fun i j => Disjoint (t i) (t j)))
    (hcs : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (hct : ∀ᵐ x ∂μ, x ∈ ⋃ i, t i)
    (hm : ∀ i, μ (s i) = μ (t i)) (a : ι → 𝕜) :
    ‖lpHaarPartitionStep (p := p) (μ := μ) s hs a‖ =
      ‖lpHaarPartitionStep (p := p) (μ := μ) t ht a‖ := by
  let A := lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp s hs hds hcs
  let B := lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp t ht hdt hct
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [← A.norm_map (lpHaarPartitionStep s hs a), ← B.norm_map (lpHaarPartitionStep t ht a),
    lp.norm_eq_tsum_rpow hpR, lp.norm_eq_tsum_rpow hpR]
  congr 1
  apply tsum_congr
  intro i
  change ‖lebesgueLpPartitionEquiv (𝕜 := 𝕜) hp s hs hds hcs
    (lpHaarPartitionStep s hs a) i‖ ^ p.toReal =
    ‖lebesgueLpPartitionEquiv (𝕜 := 𝕜) hp t ht hdt hct (lpHaarPartitionStep t ht a) i‖ ^ p.toReal
  rw [lpHaarPartitionStep_coordinates hp s hs hds hcs,
    lpHaarPartitionStep_coordinates hp t ht hdt hct,
    Lp.norm_const' _ _ _ hp0 hp, Lp.norm_const' _ _ _ hp0 hp]
  simp only [measureReal_def, Measure.restrict_apply_univ, hm]

end ThesisCommon
