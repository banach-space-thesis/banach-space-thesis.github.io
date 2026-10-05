import ThesisCommon.Analysis.DecomposableL1Operators
import ThesisCommon.Analysis.IntegralKernelClipping

/-! Uniform kernel clipping on arbitrary-index L1 decompositions.
The bounded approximations factor through the same actual L2 space, so
the conclusion uses more than separate weak compactness of the pieces. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Function
namespace ThesisCommon
variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]
variable (s : I → Set X) (hs : ∀ i, MeasurableSet (s i))
  (hd : Pairwise (Disjoint on s))
  (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)

include hs hd in
theorem weaklyCompact_decomposableL1Operator_of_bounded_range
    (A : ∀ i, Lp ℝ 1 (μ.restrict (s i)) →L[ℝ] Lp ℝ 1 ν)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ i f, ∀ᵐ y ∂ν, ‖A i f y‖ ≤ D * ‖f‖) :
    IsWeaklyCompactOperator (decomposableL1Operator s hμ A C hC hA) := by
  let B := fun i => boundedRangeLTwo (A i) (hbound i) hD
  have hB : ∀ i, ‖B i‖ ≤ lTwoFiniteMeasureConstant ν * D := fun i =>
    norm_boundedRangeLTwo_le (A i) (hbound i) hD
  let R := decomposableL1Operator s hμ B (lTwoFiniteMeasureConstant ν * D)
    (mul_nonneg lTwoFiniteMeasureConstant_nonneg hD) hB
  have heq : (lTwoToLOne ν).comp R = decomposableL1Operator s hμ A C hC hA := by
    apply decomposableL1Operator_unique s hs hd hμ A C hC hA
    intro i
    apply ContinuousLinearMap.ext
    intro f
    change lTwoToLOne ν (R (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i) f)) = A i f
    rw [show R (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i) f) = B i f from
      decomposableL1Operator_extend s hs hd hμ B _ _ hB i f]
    exact DFunLike.congr_fun (lTwoToLOne_comp_boundedRangeLTwo (A i) (hbound i) hD) f
  rw [← heq]
  exact weaklyCompact_of_hilbert_factorization R (lTwoToLOne ν)

variable [∀ i, SigmaFinite (μ.restrict (s i))]

theorem IsIntegralKernel.norm_clippedOperator_le
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} [SigmaFinite μ]
    (hk : IsIntegralKernel k K) (t : ℝ) : ‖hk.clippedOperator t‖ ≤ ‖K‖ :=
  norm_integralKernelOperator_le _ _ (norm_nonneg K)

include hs hd in
theorem weaklyCompact_decomposableL1Operator_of_uniform_clipResidual
    (A : ∀ i, Lp ℝ 1 (μ.restrict (s i)) →L[ℝ] Lp ℝ 1 ν)
    (k : I → X × Y → ℝ) (hk : ∀ i, IsIntegralKernel (k i) (A i))
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ i,
      ∀ᵐ x ∂μ.restrict (s i), clipResidualMass ν (fun y => k i (x, y)) n ≤ ε) :
    IsWeaklyCompactOperator (decomposableL1Operator s hμ A C hC hA) := by
  let T := decomposableL1Operator s hμ A C hC hA
  change T ∈ (weaklyCompactSubmodule ℝ (Lp ℝ 1 μ) (Lp ℝ 1 ν) :
    Set (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν))
  rw [← (isClosed_weaklyCompactSubmodule (𝕜 := ℝ)
    (E := Lp ℝ 1 μ) (F := Lp ℝ 1 ν)).closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := hsmall (ε / 2) (by positivity)
  let B := fun i => (hk i).clippedOperator n
  have hB : ∀ i, ‖B i‖ ≤ C := fun i => ((hk i).norm_clippedOperator_le n).trans (hA i)
  let R := decomposableL1Operator s hμ B C hC hB
  have hweak : IsWeaklyCompactOperator R := by
    apply weaklyCompact_decomposableL1Operator_of_bounded_range s hs hd hμ B C hC hB
      (show (0 : ℝ) ≤ max (n : ℝ) 0 from le_max_right _ _) 
    intro i f
    exact ((hk i).isIntegralKernel_clippedOperator n).apply_norm_le_of_bound
      (Eventually.of_forall fun z => norm_scalarClip_le_level n (k i z)) f
  refine ⟨R, hweak, ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
  apply decomposableL1Operator_norm_le_of_pieces s hs hd hμ (T - R) (ε / 2) (by positivity)
  intro i
  have heq : (T - R).comp (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i)).toContinuousLinearMap =
      A i - B i := by
    apply ContinuousLinearMap.ext
    intro f
    change T (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i) f) -
      R (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i) f) = A i f - B i f
    rw [show T (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i) f) = A i f from
      decomposableL1Operator_extend s hs hd hμ A C hC hA i f,
      show R (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i) f) = B i f from
      decomposableL1Operator_extend s hs hd hμ B C hC hB i f]
  rw [heq]
  exact (hk i).norm_sub_clippedOperator_le n (by positivity) (hn i)

end ThesisCommon
