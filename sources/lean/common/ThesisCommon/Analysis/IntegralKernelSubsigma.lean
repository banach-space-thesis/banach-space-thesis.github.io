import ThesisCommon.Analysis.L1Subsigma
import ThesisCommon.Analysis.IntegralKernelApproximation
import ThesisCommon.Analysis.ProductMeasurableCountableRight

/-! Actual kernel operators on two trimmed sigma algebras. Joint
measurability of the same kernel transfers its column bound and yields
intertwining of the constructed operators, including every truncation. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {X Y : Type*} {m₀ : MeasurableSpace X} {n₀ : MeasurableSpace Y}
variable {μ : @Measure X m₀} {ν : @Measure Y n₀}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable {m : MeasurableSpace X} {n : MeasurableSpace Y}
variable {k : X × Y → ℝ} {C : ℝ}

theorem HasKernelBound.subsigma (hm : m ≤ m₀) (hn : n ≤ n₀)
    (hk : @Measurable (X × Y) ℝ (m.prod n) (borel ℝ) k)
    (hb : @HasKernelBound ℝ _ X Y m₀ n₀ μ ν k C) :
    @HasKernelBound ℝ _ X Y m n (μ.trim hm) (ν.trim hn) k C := by
  have hkx (x : X) : StronglyMeasurable[n] (fun y => k (x, y)) :=
    (hk.comp (@measurable_prodMk_left X Y m n x)).stronglyMeasurable
  have hb' : ∀ᵐ x ∂μ, Integrable (fun y => k (x, y)) (ν.trim hn) ∧
      (∫ y, ‖k (x, y)‖ ∂ν.trim hn) ≤ C := by
    filter_upwards [hb] with x hx
    refine ⟨hx.1.trim hn (hkx x), ?_⟩
    rw [← integral_trim hn (hkx x).norm]
    exact hx.2
  have hmeas : MeasurableSet[m] {x | Integrable (fun y => k (x, y)) (ν.trim hn) ∧
      (∫ y, ‖k (x, y)‖ ∂ν.trim hn) ≤ C} :=
    (@measurableSet_integrable X Y ℝ m n (ν.trim hn) _ _
      (fun x y => k (x, y)) hk.stronglyMeasurable).inter
      (measurableSet_le (hk.stronglyMeasurable.norm.integral_prod_right').measurable measurable_const)
  change ∀ᵐ x ∂μ.trim hm, Integrable (fun y => k (x, y)) (ν.trim hn) ∧
    (∫ y, ‖k (x, y)‖ ∂ν.trim hn) ≤ C
  rw [ae_iff]
  change (μ.trim hm) {x | Integrable (fun y => k (x, y)) (ν.trim hn) ∧
    (∫ y, ‖k (x, y)‖ ∂ν.trim hn) ≤ C}ᶜ = 0
  rw [trim_measurableSet_eq hm hmeas.compl]
  exact hb'

theorem IsIntegralKernel.subsigma_intertwines
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hk : @IsIntegralKernel ℝ _ X Y m₀ n₀ μ ν k K)
    (hm : m ≤ m₀) (hn : n ≤ n₀)
    {K' : Lp ℝ 1 (μ.trim hm) →L[ℝ] Lp ℝ 1 (ν.trim hn)}
    (hk' : @IsIntegralKernel ℝ _ X Y m n (μ.trim hm) (ν.trim hn) k K') :
    (lOneSubsigmaEmbedding ν hn).toContinuousLinearMap.comp K' =
      K.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hfirst := lOneSubsigmaEmbedding_ae_eq μ hm f
  filter_upwards [lOneSubsigmaEmbedding_ae_eq ν hn (K' f),
    ae_eq_of_ae_eq_trim (hk'.represents f),
    @IsIntegralKernel.represents ℝ _ X Y m₀ n₀ μ ν k K hk
      (lOneSubsigmaEmbedding μ hm f)] with y hy₁ hy₂ hy₃
  change (lOneSubsigmaEmbedding ν hn (K' f)) y =
    (K (lOneSubsigmaEmbedding μ hm f)) y
  rw [hy₁, hy₂, hy₃]
  have hsection : StronglyMeasurable[m] (fun x => k (x, y) * f x) :=
    ((hk'.measurable.comp (@measurable_prodMk_right X Y m n y)).stronglyMeasurable).mul
      (Lp.stronglyMeasurable f)
  rw [← integral_trim hm hsection]
  apply integral_congr_ae
  filter_upwards [hfirst] with x hx
  rw [hx]

/-- The constructed restricted operator uses the unchanged kernel itself,
and the same intertwinings hold at every real truncation threshold. -/
theorem IsIntegralKernel.exists_subsigma_restriction
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hk : @IsIntegralKernel ℝ _ X Y m₀ n₀ μ ν k K)
    (hm : m ≤ m₀) (hn : n ≤ n₀)
    (hkmn : @Measurable (X × Y) ℝ (m.prod n) (borel ℝ) k) :
    ∃ (K' : Lp ℝ 1 (μ.trim hm) →L[ℝ] Lp ℝ 1 (ν.trim hn))
      (hk' : @IsIntegralKernel ℝ _ X Y m n (μ.trim hm) (ν.trim hn) k K'),
      (lOneSubsigmaEmbedding ν hn).toContinuousLinearMap.comp K' =
        K.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap ∧
      ∀ r : ℝ, (lOneSubsigmaEmbedding ν hn).toContinuousLinearMap.comp (hk'.truncatedOperator r) =
        (@IsIntegralKernel.truncatedOperator X Y m₀ n₀ μ ν k K _ _ hk r).comp
          (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap := by
  have hb : @HasKernelBound ℝ _ X Y m n (μ.trim hm) (ν.trim hn) k ‖K‖ :=
    HasKernelBound.subsigma hm hn hkmn
      (@IsIntegralKernel.hasKernelBound X Y m₀ n₀ μ ν k K _ _ hk)
  let K' := @integralKernelOperator ℝ _ X Y m n (μ.trim hm) (ν.trim hn) _ _ k hkmn ‖K‖ hb
  have hk' : @IsIntegralKernel ℝ _ X Y m n (μ.trim hm) (ν.trim hn) k K' :=
    @isIntegralKernel_integralKernelOperator ℝ _ X Y m n (μ.trim hm) (ν.trim hn) _ _ k hkmn ‖K‖ hb
  refine ⟨K', hk', hk.subsigma_intertwines hm hn hk', ?_⟩
  intro r
  exact (@IsIntegralKernel.truncatedOperator_represents X Y m₀ n₀ μ ν k K _ _ hk r).subsigma_intertwines hm hn
    (hk'.truncatedOperator_represents r)

end ThesisCommon
