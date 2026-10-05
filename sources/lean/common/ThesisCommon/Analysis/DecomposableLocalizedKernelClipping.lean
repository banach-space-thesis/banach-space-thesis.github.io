import ThesisCommon.Analysis.DecomposablePositiveKernelClipping
import ThesisCommon.Analysis.L1AdjointOneRestriction

/-! Common-budget clipping into a fixed finite-measure output part.
The ambient output measure and the index set of finite input pieces may
both be arbitrary. All error mass outside the output part is retained. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Function ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem exists_positive_weaklyCompact_decomposable_localized_budget_approx
    (s : I → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    [∀ i, IsFiniteMeasure (μ.restrict (s i))]
    (Θ : Set Y) (hΘ : MeasurableSet Θ) [IsFiniteMeasure (ν.restrict Θ)]
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (S : ∀ i, Lp ℝ 1 (μ.restrict (s i)) →L[ℝ] Lp ℝ 1 ν)
    (K : ∀ i, Lp ℝ 1 (μ.restrict (s i)) →L[ℝ] Lp ℝ 1 (ν.restrict Θ))
    (hS : ∀ i, 0 ≤ S i) (k : I → X × Y → ℝ)
    (hk : ∀ i, IsIntegralKernel (k i) (K i)) (hpos : ∀ i z, 0 ≤ k i z)
    (hT : ∀ i, T.comp (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i)).toContinuousLinearMap =
      S i + (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp (K i))
    (C : ℝ) (hC : 0 ≤ C) (hK : ∀ i, ‖K i‖ ≤ C)
    (c : ℝ) (hc : 0 ≤ c)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ i,
      ‖S i + (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
        ((hk i).truncatedOperator n)‖ ≤ c + ε) :
    ∃ H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ),
      IsWeaklyCompactOperator H ∧ 0 ≤ H ∧
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H ≤ T ∧
      ‖T - (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H‖ ≤ c := by
  let E := (lebesgueLpExtend (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := ν) Θ hΘ).toContinuousLinearMap
  let g := fun i => positiveAdjointOneDensity (S i) (hS i)
  let d := fun i x => c - g i x
  have hSnorm (i : I) : ‖S i‖ ≤ c := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := htail ε hε
    have hp : 0 ≤ (hk i).truncatedOperator n :=
      ((hk i).truncatedOperator_represents n).positive_of_nonneg_ae
        (Eventually.of_forall fun z => indicator_nonneg (fun w _ => hpos i w) z)
    have he := lebesgueL1Extend_comp_nonneg Θ hΘ hp
    apply le_trans _ (hn i)
    apply norm_le_norm_of_abs_le_abs
    rw [abs_of_nonneg (hS i), abs_of_nonneg (add_nonneg (hS i) he)]
    exact le_add_of_nonneg_right he
  have hd0 (i : I) : ∀ᵐ x ∂μ.restrict (s i), 0 ≤ d i x :=
    Eventually.of_forall fun x => sub_nonneg.mpr
      ((positiveAdjointOneDensity_bounds (S i) (hS i) x).2.trans (hSnorm i))
  have hdmeas (i : I) : Measurable (d i) :=
    measurable_const.sub (measurable_positiveAdjointOneDensity (S i) (hS i))
  let A := fun i => (hk i).budgetClippedOperator (hdmeas i)
  have hA : ∀ i, ‖A i‖ ≤ C := fun i =>
    ((hk i).norm_budgetClippedOperator_le (hdmeas i)).trans (hK i)
  have hApos (i : I) : 0 ≤ A i :=
    ((hk i).isIntegralKernel_budgetClippedOperator (hdmeas i)).positive_of_nonneg_ae
      (Eventually.of_forall fun z => budgetClipKernel_nonneg (hpos i) (d i) z)
  have hAK (i : I) : A i ≤ K i := sub_nonneg.mp
    (((hk i).sub ((hk i).isIntegralKernel_budgetClippedOperator (hdmeas i))).positive_of_nonneg_ae
      (Eventually.of_forall fun z => sub_nonneg.mpr
        (budgetClipKernel_le_self (hpos i) (d i) z)))
  let H := decomposableL1Operator s hμ A C hC hA
  have hpiece (i : I) : H.comp
      (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i)).toContinuousLinearMap = A i := by
    apply ContinuousLinearMap.ext
    intro f
    exact decomposableL1Operator_extend s hs hd hμ A C hC hA i f
  have hweak : IsWeaklyCompactOperator H := by
    apply weaklyCompact_decomposableL1Operator_of_uniform_clipResidual s hs hd hμ A
      (fun i => budgetClipKernel (ν.restrict Θ) (k i) (d i))
      (fun i => (hk i).isIntegralKernel_budgetClippedOperator (hdmeas i)) C hC hA
    intro ε hε
    obtain ⟨n, hn⟩ := htail ε hε
    refine ⟨n, fun i => ?_⟩
    filter_upwards [(hk i).clipResidualMass_budgetClippedKernel (hd0 i) (Nat.cast_nonneg n),
      positive_extended_integral_tail_mass_le_norm Θ hΘ (hS i) (hk i) (hpos i) n,
      (hk i).clipResidualMass_le_truncatedKernel n] with x he hb hr
    rw [he]
    apply max_le _ hε.le
    have hni := hn i
    dsimp only [d, g]
    linarith
  have herror (i : I) : (T - E.comp H).comp
      (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i)).toContinuousLinearMap =
        S i + E.comp (K i - A i) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc, hT i, hpiece i,
      ContinuousLinearMap.comp_sub]
    change S i + E.comp (K i) - E.comp (A i) = S i + (E.comp (K i) - E.comp (A i))
    abel
  refine ⟨H, hweak, decomposableL1Operator_nonneg s hμ A C hC hA hApos, ?_, ?_⟩
  · apply sub_nonneg.mp
    apply lOneOperator_nonneg_of_decomposable_pieces s hs hd hμ (T - E.comp H)
    intro i
    rw [herror i]
    exact add_nonneg (hS i) (lebesgueL1Extend_comp_nonneg Θ hΘ (sub_nonneg.mpr (hAK i)))
  · apply decomposableL1Operator_norm_le_of_pieces s hs hd hμ (T - E.comp H) c hc
    intro i
    rw [herror i]
    apply (norm_positive_add_extended_integral_le_iff Θ hΘ (hS i) (sub_nonneg.mpr (hAK i))
      ((hk i).sub ((hk i).isIntegralKernel_budgetClippedOperator (hdmeas i))) hc).mpr
    filter_upwards [(hk i).budgetClippedKernel_error (hd0 i)] with x he
    have hnorm : ∀ y, ‖k i (x, y) - budgetClipKernel (ν.restrict Θ) (k i) (d i) (x, y)‖ =
        k i (x, y) - budgetClipKernel (ν.restrict Θ) (k i) (d i) (x, y) := fun y =>
      Real.norm_of_nonneg (sub_nonneg.mpr
        (budgetClipKernel_le_self (hpos i) (d i) (x, y)))
    simp only [hnorm] at he
    rw [he]
    have hm := min_le_right (∫ y, ‖k i (x, y)‖ ∂ν.restrict Θ) (d i x)
    dsimp only [d, g] at hm
    linarith

end ThesisCommon
