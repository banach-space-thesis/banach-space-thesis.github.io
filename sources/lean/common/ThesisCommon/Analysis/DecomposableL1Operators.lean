import ThesisCommon.Analysis.DecomposableLpPartition
import ThesisCommon.Analysis.LpOneFamilyOperators

/-! Gluing uniformly bounded operators on arbitrary disjoint measurable
pieces, through the constructed actual L1 decomposition. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Function Classical
namespace ThesisCommon
variable {𝕜 X E I F : Type*} [RCLike 𝕜] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {μ : Measure X}

theorem decomposableLp_hasSum_extensions {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (s : I → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ) (f : Lp E p μ) :
    HasSum (fun i => lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i)
      (lebesgueLpRestrict (𝕜 := 𝕜) (s i) f)) f := by
  let e := decomposableLpPartitionEquiv (𝕜 := 𝕜) (E := E) hp s hs hd hμ
  have h := (lp.hasSum_single hp (e f)).map
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap e.symm.continuous
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply] at h
  simpa only [Function.comp_def, e, decomposableLpPartitionEquiv_symm_single,
    decomposableLpPartitionEquiv_apply] using h

def decomposableL1Operator (s : I → Set X)
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    (A : ∀ i, Lp E 1 (μ.restrict (s i)) →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) : Lp E 1 μ →L[𝕜] F :=
  (lpOneFamilyOperator A C hC hA).comp
    (decomposableLpPartition (by norm_num : (1 : ENNReal) ≠ ⊤) s hμ).toContinuousLinearMap

theorem decomposableL1Operator_apply (s : I → Set X)
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    (A : ∀ i, Lp E 1 (μ.restrict (s i)) →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (f : Lp E 1 μ) :
    decomposableL1Operator s hμ A C hC hA f =
      ∑' i, A i (lebesgueLpRestrict (𝕜 := 𝕜) (s i) f) := rfl

theorem norm_decomposableL1Operator_le (s : I → Set X)
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    (A : ∀ i, Lp E 1 (μ.restrict (s i)) →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) :
    ‖decomposableL1Operator s hμ A C hC hA‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  have h := norm_tsum_lpOneFamily_operators_le A C hC hA
    (decomposableLpPartition (𝕜 := 𝕜) (by norm_num : (1 : ENNReal) ≠ ⊤) s hμ f)
  simpa only [LinearIsometry.norm_map] using h

theorem decomposableL1Operator_extend (s : I → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    (A : ∀ i, Lp E 1 (μ.restrict (s i)) →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (i : I)
    (f : Lp E 1 (μ.restrict (s i))) :
    decomposableL1Operator s hμ A C hC hA
      (lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i) f) = A i f := by
  change lpOneFamilyOperator A C hC hA
    (decomposableLpPartition (by norm_num : (1 : ENNReal) ≠ ⊤) s hμ
      (lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i) f)) = _
  rw [decomposableLpPartition_extend _ s hs hd hμ i f, lpOneFamilyOperator_single]

theorem decomposableL1Operator_unique (s : I → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    (A : ∀ i, Lp E 1 (μ.restrict (s i)) →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (T : Lp E 1 μ →L[𝕜] F)
    (hT : ∀ i, T.comp (lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i)).toContinuousLinearMap = A i) :
    T = decomposableL1Operator s hμ A C hC hA := by
  let e := decomposableLpPartitionEquiv (𝕜 := 𝕜) (E := E)
    (by norm_num : (1 : ENNReal) ≠ ⊤) s hs hd hμ
  have hcomp : T.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      lpOneFamilyOperator A C hC hA := by
    apply lpOneFamilyOperator_unique
    intro i
    apply ContinuousLinearMap.ext
    intro f
    change T (e.symm (lp.single 1 i f)) = A i f
    rw [show e.symm (lp.single 1 i f) = lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i) f from
      decomposableLpPartitionEquiv_symm_single _ s hs hd hμ i f]
    exact DFunLike.congr_fun (hT i) f
  apply ContinuousLinearMap.ext
  intro f
  have h := DFunLike.congr_fun hcomp (e f)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply] using h

theorem decomposableL1Operator_norm_le_of_pieces (s : I → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    (T : Lp E 1 μ →L[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T.comp (lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i)).toContinuousLinearMap‖ ≤ C) :
    ‖T‖ ≤ C := by
  let A := fun i => T.comp (lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i)).toContinuousLinearMap
  have heq := decomposableL1Operator_unique s hs hd hμ A C hC hT T (fun _ => rfl)
  rw [heq]
  exact norm_decomposableL1Operator_le s hμ A C hC hT

end ThesisCommon
