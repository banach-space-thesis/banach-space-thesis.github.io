import ThesisCommon.Analysis.LpPartitionNormTransfer

/-! Contractive finite-rank transport between measurable partitions whose
corresponding atoms have equal measures. These are the finite embedding
and reading operators for faithful Haar systems in actual interval Lp. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable {𝕜 α ι : Type*} [RCLike 𝕜] [MeasurableSpace α] [Fintype ι]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]

def lpHaarPartitionAverage (hp : p ≠ ∞) (s : Set α) : Lp 𝕜 p μ →L[𝕜] 𝕜 :=
  (μ.real s : 𝕜)⁻¹ • ((lpHaarFiniteIntegral (μ := μ.restrict s) hp).comp
    (lebesgueLpRestrict (𝕜 := 𝕜) s))

theorem lpHaarPartitionAverage_apply (hp : p ≠ ∞) (s : Set α) (f : Lp 𝕜 p μ) :
    lpHaarPartitionAverage hp s f = (μ.real s : 𝕜)⁻¹ *
      ∫ x, lebesgueLpRestrict (𝕜 := 𝕜) s f x ∂μ.restrict s := rfl

def lpHaarPartitionTransfer (hp : p ≠ ∞) (s t : ι → Set α)
    (ht : ∀ i, MeasurableSet (t i)) : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  ∑ i, (lpHaarPartitionAverage hp (s i)).smulRight
    (indicatorConstLp p (ht i) (measure_ne_top μ (t i)) (1 : 𝕜))

theorem lpHaarPartitionTransfer_apply (hp : p ≠ ∞) (s t : ι → Set α)
    (ht : ∀ i, MeasurableSet (t i)) (f : Lp 𝕜 p μ) :
    lpHaarPartitionTransfer hp s t ht f =
      lpHaarPartitionStep t ht (fun i => lpHaarPartitionAverage hp (s i) f) := by
  simp only [lpHaarPartitionTransfer, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, lpHaarPartitionStep]
  apply Finset.sum_congr rfl
  intro i _
  exact (lpHaarIndicator_smul (t i) (ht i) (lpHaarPartitionAverage hp (s i) f)).symm

theorem lpHaarPartitionMean_eq_step (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (hm : ∀ i, μ (s i) ≠ 0) (f : Lp 𝕜 p μ) :
    lpHaarPartitionMean hp s hs hd hc hm f =
      lpHaarPartitionStep s hs (fun i => lpHaarPartitionAverage hp (s i) f) := by
  rw [lpHaarPartitionMean_eq_sum]
  unfold lpHaarPartitionStep
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [lpHaarMean_apply, lpHaarExtend_const, lpHaarPartitionAverage_apply]
  simp only [measureReal_def, Measure.restrict_apply_univ]

theorem lpHaarPartitionTransfer_norm_le (hp : p ≠ ∞) (s t : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (ht : ∀ i, MeasurableSet (t i))
    (hds : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hdt : Pairwise (fun i j => Disjoint (t i) (t j)))
    (hcs : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (hct : ∀ᵐ x ∂μ, x ∈ ⋃ i, t i)
    (hpositive : ∀ i, μ (s i) ≠ 0) (hm : ∀ i, μ (s i) = μ (t i)) :
    ‖lpHaarPartitionTransfer (𝕜 := 𝕜) (p := p) (μ := μ) hp s t ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul, lpHaarPartitionTransfer_apply,
    ← lpHaarPartitionStep_norm_eq hp s t hs ht hds hdt hcs hct hm,
    ← lpHaarPartitionMean_eq_step hp s hs hds hcs hpositive]
  exact lpHaarPartitionMean_norm hp s hs hds hcs hpositive f

theorem lpHaarPartitionAverage_indicator (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hm : ∀ i, μ (s i) ≠ 0) (i j : ι) (c : 𝕜) :
    lpHaarPartitionAverage hp (s j)
      (indicatorConstLp p (hs i) (measure_ne_top μ (s i)) c) = if j = i then c else 0 := by
  rw [lpHaarPartitionAverage_apply, ← lpHaarExtend_const (s i) (hs i) c]
  by_cases hji : j = i
  · subst j
    rw [lebesgueLpRestrict_extend, integral_congr_ae (Lp.coeFn_const p (μ.restrict (s i)) c)]
    have hne : (μ.real (s i) : 𝕜) ≠ 0 := by
      exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hm i, measure_ne_top μ (s i)⟩)
    simp only [Function.const_apply, integral_const, measureReal_def,
      Measure.restrict_apply_univ, Algebra.smul_def, RCLike.algebraMap_eq_ofReal, if_pos rfl]
    change (μ.real (s i) : 𝕜)⁻¹ * ((μ.real (s i) : 𝕜) * c) = _
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    simp
  · rw [lebesgueLpRestrict_extend_disjoint (hs j) (hs i) (hd hji)]
    rw [integral_congr_ae (Lp.coeFn_zero 𝕜 p (μ.restrict (s j)))]
    simp only [Pi.zero_apply, integral_zero, mul_zero, if_neg hji]

theorem lpHaarPartitionTransfer_indicator (hp : p ≠ ∞) (s t : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (ht : ∀ i, MeasurableSet (t i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (hm : ∀ i, μ (s i) ≠ 0)
    (i : ι) (c : 𝕜) :
    lpHaarPartitionTransfer hp s t ht
      (indicatorConstLp p (hs i) (measure_ne_top μ (s i)) c) =
        indicatorConstLp p (ht i) (measure_ne_top μ (t i)) c := by
  rw [lpHaarPartitionTransfer_apply]
  unfold lpHaarPartitionStep
  simp_rw [lpHaarPartitionAverage_indicator hp s hs hd hm]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg hji, lpHaarIndicator_smul]
    exact zero_smul _ _
  · simp

end ThesisCommon
