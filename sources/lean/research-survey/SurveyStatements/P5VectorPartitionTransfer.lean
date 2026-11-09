import SurveyStatements.P5VectorPartitionNorm
import SurveyStatements.P5Support.LpHaarPartitionMean

/-! Actual contractive transport between equal-measure finite partitions
for Banach-valued Lp functions. These maps are the finite outer-coordinate
embedding and reading maps used in the mixed Bochner space. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5

variable {𝕜 α E ι : Type*} [RCLike 𝕜] [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [Fintype ι]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]

def vectorLpPartitionMean (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (hm : ∀ i, μ (s i) ≠ 0) :
    Lp E p μ →L[𝕜] Lp E p μ :=
  let A := P5Support.lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := E) hp s hs hd hc
  let D := P5Support.lpHaarCoordinateContraction
    (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp)
    (fun i => finiteLpMean (𝕜 := 𝕜) (E := E) (μ := μ.restrict (s i)) hp)
    (fun i => finiteLpMean_norm_le hp (by simpa using hm i))
  A.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (D.comp A.toContinuousLinearEquiv.toContinuousLinearMap)

theorem vectorLpPartitionMean_coordinate (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (hm : ∀ i, μ (s i) ≠ 0)
    (f : Lp E p μ) (i : ι) :
    P5Support.lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := E) hp s hs hd hc
      (vectorLpPartitionMean (𝕜 := 𝕜) hp s hs hd hc hm f) i =
      finiteLpMean (𝕜 := 𝕜) (μ := μ.restrict (s i)) hp
        (P5Support.lebesgueLpPartitionEquiv (𝕜 := 𝕜) hp s hs hd hc f i) := by
  simp only [vectorLpPartitionMean, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem vectorLpPartitionMean_norm_le (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (hm : ∀ i, μ (s i) ≠ 0) (f : Lp E p μ) :
    ‖vectorLpPartitionMean (𝕜 := 𝕜) hp s hs hd hc hm f‖ ≤ ‖f‖ := by
  let A := P5Support.lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := E) hp s hs hd hc
  change ‖A.symm (P5Support.lpHaarCoordinateContraction
    (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp)
    (fun i => finiteLpMean (𝕜 := 𝕜) (E := E) (μ := μ.restrict (s i)) hp)
    (fun i => finiteLpMean_norm_le hp (by simpa using hm i)) (A f))‖ ≤ ‖f‖
  rw [A.symm.norm_map]
  exact (P5Support.lpHaarCoordinateContraction_norm _ _ _ (A f)).trans_eq (A.norm_map f)

theorem vectorLpPartitionMean_eq_sum (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (hm : ∀ i, μ (s i) ≠ 0) (f : Lp E p μ) :
    vectorLpPartitionMean (𝕜 := 𝕜) hp s hs hd hc hm f =
      ∑ i, P5Support.lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i)
        (finiteLpMean (𝕜 := 𝕜) hp (P5Support.lebesgueLpRestrict (𝕜 := 𝕜) (s i) f)) := by
  apply (P5Support.lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := E) hp s hs hd hc).injective
  rw [map_sum]
  change P5Support.lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := E) hp s hs hd hc
    (vectorLpPartitionMean (𝕜 := 𝕜) hp s hs hd hc hm f) =
      ∑ i, P5Support.lebesgueLpPartition (𝕜 := 𝕜) hp s hs hd hc
        (P5Support.lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i)
          (finiteLpMean (𝕜 := 𝕜) hp (P5Support.lebesgueLpRestrict (𝕜 := 𝕜) (s i) f)))
  simp_rw [P5Support.lebesgueLpPartition_extend]
  apply lp.ext
  funext j
  rw [vectorLpPartitionMean_coordinate (𝕜 := 𝕜)]
  simp [lp.coeFn_sum, lp.coeFn_single]
  rfl

def vectorLpPartitionAverage (hp : p ≠ ∞) (s : Set α) : Lp E p μ →L[𝕜] E :=
  (μ.real s : 𝕜)⁻¹ • ((finiteLpIntegral (𝕜 := 𝕜) (μ := μ.restrict s) hp).comp
    (P5Support.lebesgueLpRestrict (𝕜 := 𝕜) s))

def vectorLpIndicator (s : Set α) (hs : MeasurableSet s) : E →L[𝕜] Lp E p μ :=
  (P5Support.lebesgueLpExtend (𝕜 := 𝕜) s hs).toContinuousLinearMap.comp
    (Lp.constL p (μ.restrict s) 𝕜)

theorem vectorLpIndicator_apply (s : Set α) (hs : MeasurableSet s) (c : E) :
    vectorLpIndicator (𝕜 := 𝕜) s hs c = indicatorConstLp p hs (measure_ne_top μ s) c :=
  vectorLpExtend_const (𝕜 := 𝕜) s hs c

def vectorLpPartitionTransfer (hp : p ≠ ∞) (s t : ι → Set α)
    (ht : ∀ i, MeasurableSet (t i)) : Lp E p μ →L[𝕜] Lp E p μ :=
  ∑ i, (vectorLpIndicator (𝕜 := 𝕜) (t i) (ht i)).comp
    (vectorLpPartitionAverage hp (s i))

theorem vectorLpPartitionTransfer_apply (hp : p ≠ ∞) (s t : ι → Set α)
    (ht : ∀ i, MeasurableSet (t i)) (f : Lp E p μ) :
    vectorLpPartitionTransfer (𝕜 := 𝕜) hp s t ht f =
      vectorLpPartitionStep t ht (fun i => vectorLpPartitionAverage (𝕜 := 𝕜) hp (s i) f) := by
  simp only [vectorLpPartitionTransfer, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, vectorLpIndicator_apply, vectorLpPartitionStep]

theorem vectorLpPartitionMean_eq_step (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (hm : ∀ i, μ (s i) ≠ 0) (f : Lp E p μ) :
    vectorLpPartitionMean (𝕜 := 𝕜) hp s hs hd hc hm f =
      vectorLpPartitionStep s hs (fun i => vectorLpPartitionAverage (𝕜 := 𝕜) hp (s i) f) := by
  rw [vectorLpPartitionMean_eq_sum]
  unfold vectorLpPartitionStep
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteLpMean_apply (𝕜 := 𝕜) (μ := μ.restrict (s i)),
    vectorLpExtend_const (𝕜 := 𝕜) (p := p) (μ := μ) (s i) (hs i)]
  simp only [vectorLpPartitionAverage, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, measureReal_def, Measure.restrict_apply_univ]

theorem norm_vectorLpPartitionTransfer_le (hp : p ≠ ∞) (s t : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (ht : ∀ i, MeasurableSet (t i))
    (hds : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hdt : Pairwise (fun i j => Disjoint (t i) (t j)))
    (hcs : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (hct : ∀ᵐ x ∂μ, x ∈ ⋃ i, t i)
    (hm : ∀ i, μ (s i) ≠ 0) (heq : ∀ i, μ (s i) = μ (t i)) :
    ‖vectorLpPartitionTransfer (𝕜 := 𝕜) (E := E) (μ := μ) hp s t ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul, vectorLpPartitionTransfer_apply,
    ← vectorLpPartitionStep_norm_eq (𝕜 := 𝕜) hp s t hs ht hds hdt hcs hct heq,
    ← vectorLpPartitionMean_eq_step hp s hs hds hcs hm]
  exact vectorLpPartitionMean_norm_le hp s hs hds hcs hm f

end SurveyStatements.P5
