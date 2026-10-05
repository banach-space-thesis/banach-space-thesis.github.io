import ThesisCommon.Analysis.DecomposableL1BoundedRange
import ThesisCommon.Analysis.PositiveKernelClipping

/-! Positive bounded-range approximants to the glued integral kernels.
The single residual threshold is uniform over the arbitrary index set. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Function ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]

theorem decomposableL1Operator_exists_positive_boundedRange_approx
    (s : I → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    [∀ i, SigmaFinite (μ.restrict (s i))]
    (A : ∀ i, Lp ℝ 1 (μ.restrict (s i)) →L[ℝ] Lp ℝ 1 ν)
    (k : I → X × Y → ℝ) (hk : ∀ i, IsIntegralKernel (k i) (A i))
    (hpos : ∀ i z, 0 ≤ k i z)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ i,
      ∀ᵐ x ∂μ.restrict (s i), clipResidualMass ν (fun y => k i (x, y)) n ≤ ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν,
      0 ≤ B ∧ B ≤ decomposableL1Operator s hμ A C hC hA ∧
      ‖decomposableL1Operator s hμ A C hC hA - B‖ < ε ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ f, ∀ᵐ y ∂ν, ‖B f y‖ ≤ D * ‖f‖ := by
  let T := decomposableL1Operator s hμ A C hC hA
  obtain ⟨n, hn⟩ := hsmall (ε / 2) (by positivity)
  let B := fun i => (hk i).clippedOperator n
  have hB : ∀ i, ‖B i‖ ≤ C := fun i => ((hk i).norm_clippedOperator_le n).trans (hA i)
  let R := decomposableL1Operator s hμ B C hC hB
  have hBpos (i : I) : 0 ≤ B i :=
    ((hk i).isIntegralKernel_clippedOperator n).positive_of_nonneg_ae
      (Eventually.of_forall fun z => scalarClip_nonneg n (hpos i z))
  have hBA (i : I) : B i ≤ A i := sub_nonneg.mp
    (((hk i).sub ((hk i).isIntegralKernel_clippedOperator n)).positive_of_nonneg_ae
      (Eventually.of_forall fun z => sub_nonneg.mpr (scalarClip_le_self n (hpos i z))))
  have heq (i : I) : (T - R).comp
      (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i)).toContinuousLinearMap = A i - B i := by
    apply ContinuousLinearMap.ext
    intro f
    change T (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i) f) -
      R (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i) f) = A i f - B i f
    rw [show T (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i) f) = A i f from
      decomposableL1Operator_extend s hs hd hμ A C hC hA i f,
      show R (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i) f) = B i f from
      decomposableL1Operator_extend s hs hd hμ B C hC hB i f]
  refine ⟨R, decomposableL1Operator_nonneg s hμ B C hC hB hBpos, ?_, ?_,
    max (n : ℝ) 0, le_max_right _ _, ?_⟩
  · apply sub_nonneg.mp
    apply lOneOperator_nonneg_of_decomposable_pieces s hs hd hμ (T - R)
    intro i
    rw [heq i]
    exact sub_nonneg.mpr (hBA i)
  · apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
    apply decomposableL1Operator_norm_le_of_pieces s hs hd hμ (T - R) (ε / 2) (by positivity)
    intro i
    rw [heq i]
    exact (hk i).norm_sub_clippedOperator_le n (by positivity) (hn i)
  · apply decomposableL1Operator_apply_norm_le_of_bound s hμ B C hC hB
    intro i f
    exact ((hk i).isIntegralKernel_clippedOperator n).apply_norm_le_of_bound
      (Eventually.of_forall fun z => norm_scalarClip_le_level n (k i z)) f

end ThesisCommon
