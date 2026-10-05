import ThesisCommon.Analysis.DecomposableL1WeakCompact
import ThesisCommon.Analysis.DecomposableL1Order
import ThesisCommon.Analysis.PositiveFiniteKernelBestApproximation

/-! Positive clipping with one global budget on arbitrary-index finite
input pieces. A uniform tail estimate produces one genuinely weakly
compact glued operator with the prescribed error bound. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Function ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]

theorem exists_positive_weaklyCompact_decomposable_budget_approx
    (s : I → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    [∀ i, IsFiniteMeasure (μ.restrict (s i))]
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (S K : ∀ i, Lp ℝ 1 (μ.restrict (s i)) →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ i, 0 ≤ S i) (k : I → X × Y → ℝ)
    (hk : ∀ i, IsIntegralKernel (k i) (K i)) (hpos : ∀ i z, 0 ≤ k i z)
    (hT : ∀ i, T.comp (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i)).toContinuousLinearMap =
      S i + K i)
    (C : ℝ) (hC : 0 ≤ C) (hK : ∀ i, ‖K i‖ ≤ C)
    (c : ℝ) (hc : 0 ≤ c)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ i, ‖S i + (hk i).truncatedOperator n‖ ≤ c + ε) :
    ∃ H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν,
      IsWeaklyCompactOperator H ∧ 0 ≤ H ∧ H ≤ T ∧ ‖T - H‖ ≤ c := by
  let g := fun i => positiveAdjointOneDensity (S i) (hS i)
  let d := fun i x => c - g i x
  have hSnorm (i : I) : ‖S i‖ ≤ c := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := htail ε hε
    have hp : 0 ≤ (hk i).truncatedOperator n :=
      ((hk i).truncatedOperator_represents n).positive_of_nonneg_ae
        (Eventually.of_forall fun z => indicator_nonneg (fun w _ => hpos i w) z)
    apply le_trans _ (hn i)
    apply norm_le_norm_of_abs_le_abs
    rw [abs_of_nonneg (hS i), abs_of_nonneg (add_nonneg (hS i) hp)]
    exact le_add_of_nonneg_right hp
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
      (fun i => budgetClipKernel ν (k i) (d i))
      (fun i => (hk i).isIntegralKernel_budgetClippedOperator (hdmeas i)) C hC hA
    intro ε hε
    obtain ⟨n, hn⟩ := htail ε hε
    refine ⟨n, fun i => ?_⟩
    filter_upwards [(hk i).clipResidualMass_budgetClippedKernel (hd0 i) (Nat.cast_nonneg n),
      positive_integral_tail_mass_le_norm (hS i) (hk i) (hpos i) n,
      (hk i).clipResidualMass_le_truncatedKernel n] with x he hb hr
    rw [he]
    apply max_le _ hε.le
    have hni := hn i
    dsimp only [d, g]
    linarith
  refine ⟨H, hweak, decomposableL1Operator_nonneg s hμ A C hC hA hApos, ?_, ?_⟩
  · apply sub_nonneg.mp
    apply lOneOperator_nonneg_of_decomposable_pieces s hs hd hμ (T - H)
    intro i
    rw [ContinuousLinearMap.sub_comp, hT i, hpiece i]
    exact sub_nonneg.mpr ((hAK i).trans (le_add_of_nonneg_left (hS i)))
  · apply decomposableL1Operator_norm_le_of_pieces s hs hd hμ (T - H) c hc
    intro i
    rw [ContinuousLinearMap.sub_comp, hT i, hpiece i,
      show S i + K i - A i = S i + (K i - A i) by abel]
    apply (norm_positive_add_integral_le_iff (hS i) (sub_nonneg.mpr (hAK i))
      ((hk i).sub ((hk i).isIntegralKernel_budgetClippedOperator (hdmeas i))) hc).mpr
    filter_upwards [(hk i).budgetClippedKernel_error (hd0 i)] with x he
    have hnorm : ∀ y, ‖k i (x, y) - budgetClipKernel ν (k i) (d i) (x, y)‖ =
        k i (x, y) - budgetClipKernel ν (k i) (d i) (x, y) := fun y =>
      Real.norm_of_nonneg (sub_nonneg.mpr (budgetClipKernel_le_self (hpos i) (d i) (x, y)))
    simp only [hnorm] at he
    rw [he]
    have hm := min_le_right (∫ y, ‖k i (x, y)‖ ∂ν) (d i x)
    dsimp only [d, g] at hm
    linarith

end ThesisCommon
