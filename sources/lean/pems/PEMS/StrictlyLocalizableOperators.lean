import PEMS.StrictlyLocalizableDecomposition
import ThesisCommon.Analysis.DecomposableL1Operators

/-! Actual operator gluing over the finite pieces of a strictly localizable
measure space, as used in the strictly localizable stage of the paper. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS
variable {X 𝕜 F : Type*} [MeasurableSpace X] [RCLike 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] {μ : Measure X}

theorem strictlyLocalizable_L1_hasSum (hμ : StrictlyLocalizable μ) (f : Lp 𝕜 1 μ) :
    HasSum (fun i : strictlyLocalizableParts hμ =>
      lebesgueLpExtend (𝕜 := 𝕜) i.val (strictlyLocalizablePart_measurable hμ i)
        (lebesgueLpRestrict (𝕜 := 𝕜) i.val f)) f :=
  decomposableLp_hasSum_extensions (by norm_num) _
    (strictlyLocalizablePart_measurable hμ) (strictlyLocalizableParts_disjoint hμ)
    (strictlyLocalizable_sum_restrict hμ) f

def strictlyLocalizableOperatorGlue (hμ : StrictlyLocalizable μ)
    (A : ∀ i : strictlyLocalizableParts hμ, Lp 𝕜 1 (μ.restrict i.val) →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) : Lp 𝕜 1 μ →L[𝕜] F :=
  decomposableL1Operator _ (strictlyLocalizable_sum_restrict hμ) A C hC hA

theorem strictlyLocalizableOperatorGlue_apply (hμ : StrictlyLocalizable μ)
    (A : ∀ i : strictlyLocalizableParts hμ, Lp 𝕜 1 (μ.restrict i.val) →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (f : Lp 𝕜 1 μ) :
    strictlyLocalizableOperatorGlue hμ A C hC hA f =
      ∑' i, A i (lebesgueLpRestrict (𝕜 := 𝕜) i.val f) := rfl

theorem norm_strictlyLocalizableOperatorGlue_le (hμ : StrictlyLocalizable μ)
    (A : ∀ i : strictlyLocalizableParts hμ, Lp 𝕜 1 (μ.restrict i.val) →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) :
    ‖strictlyLocalizableOperatorGlue hμ A C hC hA‖ ≤ C :=
  norm_decomposableL1Operator_le _ (strictlyLocalizable_sum_restrict hμ) A C hC hA

theorem strictlyLocalizableOperatorGlue_extend (hμ : StrictlyLocalizable μ)
    (A : ∀ i : strictlyLocalizableParts hμ, Lp 𝕜 1 (μ.restrict i.val) →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (i : strictlyLocalizableParts hμ) (f : Lp 𝕜 1 (μ.restrict i.val)) :
    strictlyLocalizableOperatorGlue hμ A C hC hA
      (lebesgueLpExtend (𝕜 := 𝕜) i.val (strictlyLocalizablePart_measurable hμ i) f) = A i f :=
  decomposableL1Operator_extend _ (strictlyLocalizablePart_measurable hμ)
    (strictlyLocalizableParts_disjoint hμ) (strictlyLocalizable_sum_restrict hμ) A C hC hA i f

theorem strictlyLocalizableOperatorGlue_unique (hμ : StrictlyLocalizable μ)
    (A : ∀ i : strictlyLocalizableParts hμ, Lp 𝕜 1 (μ.restrict i.val) →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (T : Lp 𝕜 1 μ →L[𝕜] F)
    (hT : ∀ i, T.comp (lebesgueLpExtend (𝕜 := 𝕜) i.val
      (strictlyLocalizablePart_measurable hμ i)).toContinuousLinearMap = A i) :
    T = strictlyLocalizableOperatorGlue hμ A C hC hA :=
  decomposableL1Operator_unique _ (strictlyLocalizablePart_measurable hμ)
    (strictlyLocalizableParts_disjoint hμ) (strictlyLocalizable_sum_restrict hμ) A C hC hA T hT

theorem strictlyLocalizable_operator_norm_le_of_pieces (hμ : StrictlyLocalizable μ)
    (T : Lp 𝕜 1 μ →L[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i : strictlyLocalizableParts hμ,
      ‖T.comp (lebesgueLpExtend (𝕜 := 𝕜) i.val
        (strictlyLocalizablePart_measurable hμ i)).toContinuousLinearMap‖ ≤ C) : ‖T‖ ≤ C :=
  decomposableL1Operator_norm_le_of_pieces _ (strictlyLocalizablePart_measurable hμ)
    (strictlyLocalizableParts_disjoint hμ) (strictlyLocalizable_sum_restrict hμ) T C hC hT

end PEMS
