import SurveyStatements.P5FiniteAverages
import SurveyStatements.P5Support.LebesgueLpPartition

/-! Equal-measure finite partitions preserve the norm of genuine Banach-valued
step functions. This extends the scalar partition transport argument. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5

variable {𝕜 α E ι : Type*} [RCLike 𝕜] [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [Fintype ι]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]

theorem vectorLpExtend_const (s : Set α) (hs : MeasurableSet s) (c : E) :
    P5Support.lebesgueLpExtend (𝕜 := 𝕜) s hs (Lp.const p (μ.restrict s) c) =
      indicatorConstLp p hs (measure_ne_top μ s) c := by
  apply Lp.ext
  have hc := (ae_restrict_iff' hs).mp (Lp.coeFn_const p (μ.restrict s) c)
  filter_upwards [P5Support.lebesgueLpExtend_coe (𝕜 := 𝕜) s hs
    (Lp.const p (μ.restrict s) c),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := measure_ne_top μ s) (c := c), hc]
    with x h₁ h₂ h₃
  rw [h₁, h₂]
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx]
    exact h₃ hx
  · simp [hx]

def vectorLpPartitionStep (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i))
    (a : ι → E) : Lp E p μ :=
  ∑ i, indicatorConstLp p (hs i) (measure_ne_top μ (s i)) (a i)

include 𝕜

theorem vectorLpPartitionStep_coordinates (hp : p ≠ ∞)
    (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (a : ι → E) (i : ι) :
    P5Support.lebesgueLpPartitionEquiv (𝕜 := 𝕜) hp s hs hd hc
      (vectorLpPartitionStep s hs a) i = Lp.const p (μ.restrict (s i)) (a i) := by
  have heq : P5Support.lebesgueLpPartitionEquiv (𝕜 := 𝕜) hp s hs hd hc
      (vectorLpPartitionStep s hs a) =
      ∑ j, lp.single p j (Lp.const p (μ.restrict (s j)) (a j)) := by
    change P5Support.lebesgueLpPartition (𝕜 := 𝕜) hp s hs hd hc
      (vectorLpPartitionStep s hs a) = _
    rw [vectorLpPartitionStep, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← vectorLpExtend_const (𝕜 := 𝕜) (s j) (hs j) (a j)]
    exact P5Support.lebesgueLpPartition_extend hp s hs hd hc j _
  rw [heq]
  simp [lp.coeFn_sum, lp.coeFn_single]

theorem vectorLpPartitionStep_norm_eq (hp : p ≠ ∞)
    (s t : ι → Set α) (hs : ∀ i, MeasurableSet (s i)) (ht : ∀ i, MeasurableSet (t i))
    (hds : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hdt : Pairwise (fun i j => Disjoint (t i) (t j)))
    (hcs : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (hct : ∀ᵐ x ∂μ, x ∈ ⋃ i, t i)
    (hm : ∀ i, μ (s i) = μ (t i)) (a : ι → E) :
    ‖vectorLpPartitionStep (p := p) (μ := μ) s hs a‖ =
      ‖vectorLpPartitionStep (p := p) (μ := μ) t ht a‖ := by
  let A := P5Support.lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := E) hp s hs hds hcs
  let B := P5Support.lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := E) hp t ht hdt hct
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [← A.norm_map (vectorLpPartitionStep s hs a),
    ← B.norm_map (vectorLpPartitionStep t ht a),
    lp.norm_eq_tsum_rpow hpR, lp.norm_eq_tsum_rpow hpR]
  congr 1
  apply tsum_congr
  intro i
  change ‖P5Support.lebesgueLpPartitionEquiv (𝕜 := 𝕜) hp s hs hds hcs
    (vectorLpPartitionStep s hs a) i‖ ^ p.toReal =
    ‖P5Support.lebesgueLpPartitionEquiv (𝕜 := 𝕜) hp t ht hdt hct
      (vectorLpPartitionStep t ht a) i‖ ^ p.toReal
  rw [vectorLpPartitionStep_coordinates (𝕜 := 𝕜) hp s hs hds hcs,
    vectorLpPartitionStep_coordinates (𝕜 := 𝕜) hp t ht hdt hct,
    Lp.norm_const' _ _ _ hp0 hp, Lp.norm_const' _ _ _ hp0 hp]
  simp only [measureReal_def, Measure.restrict_apply_univ, hm]

end SurveyStatements.P5
