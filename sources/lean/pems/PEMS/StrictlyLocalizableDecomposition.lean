import PEMS.MeasureDefinitions
import ThesisCommon.Analysis.DecomposableLpPartition

/-! The actual L1 direct-sum decomposition following Definition 3.3.
The partition and isometry are constructed from strict localizability. -/
noncomputable section
open MeasureTheory Set ThesisCommon
open scoped ENNReal Function Classical
namespace PEMS
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def strictlyLocalizableParts (hμ : StrictlyLocalizable μ) : Set (Set X) := hμ.choose

theorem strictlyLocalizablePart_measurable (hμ : StrictlyLocalizable μ)
    (i : strictlyLocalizableParts hμ) : MeasurableSet i.val :=
  (hμ.choose_spec.1 i.val i.property).1

theorem strictlyLocalizablePart_finite (hμ : StrictlyLocalizable μ)
    (i : strictlyLocalizableParts hμ) : μ i.val < ⊤ :=
  (hμ.choose_spec.1 i.val i.property).2

theorem strictlyLocalizablePart_isFiniteMeasure (hμ : StrictlyLocalizable μ)
    (i : strictlyLocalizableParts hμ) : IsFiniteMeasure (μ.restrict i.val) :=
  isFiniteMeasure_restrict.mpr (strictlyLocalizablePart_finite hμ i).ne

theorem strictlyLocalizableParts_disjoint (hμ : StrictlyLocalizable μ) :
    Pairwise (Disjoint on (fun i : strictlyLocalizableParts hμ => i.val)) := by
  intro i j hij
  exact hμ.choose_spec.2.1 i.property j.property (fun h => hij (Subtype.ext h))

theorem strictlyLocalizable_sum_restrict (hμ : StrictlyLocalizable μ) :
    Measure.sum (fun i : strictlyLocalizableParts hμ => μ.restrict i.val) = μ :=
  sum_restrict_eq_of_apply (fun i : strictlyLocalizableParts hμ => i.val)
    hμ.choose_spec.2.2.2.2

/-- The genuine ell-one decomposition into finite-measure L1 spaces, over
an unrestricted index set, for both real and complex scalars. -/
def strictlyLocalizableL1Equiv (𝕜 : Type*) [RCLike 𝕜] (hμ : StrictlyLocalizable μ) :
    Lp 𝕜 1 μ ≃ₗᵢ[𝕜] lp (fun i : strictlyLocalizableParts hμ => Lp 𝕜 1 (μ.restrict i.val)) 1 :=
  decomposableLpPartitionEquiv (by norm_num) _ (strictlyLocalizablePart_measurable hμ)
    (strictlyLocalizableParts_disjoint hμ) (strictlyLocalizable_sum_restrict hμ)

theorem strictlyLocalizableL1Equiv_apply (𝕜 : Type*) [RCLike 𝕜]
    (hμ : StrictlyLocalizable μ) (f : Lp 𝕜 1 μ) (i : strictlyLocalizableParts hμ) :
    strictlyLocalizableL1Equiv 𝕜 hμ f i = lebesgueLpRestrict (𝕜 := 𝕜) i.val f := rfl

theorem strictlyLocalizableL1Equiv_symm_single (𝕜 : Type*) [RCLike 𝕜]
    (hμ : StrictlyLocalizable μ) (i : strictlyLocalizableParts hμ)
    (f : Lp 𝕜 1 (μ.restrict i.val)) :
    (strictlyLocalizableL1Equiv 𝕜 hμ).symm (lp.single 1 i f) =
      lebesgueLpExtend (𝕜 := 𝕜) i.val (strictlyLocalizablePart_measurable hμ i) f := by
  convert decomposableLpPartitionEquiv_symm_single (𝕜 := 𝕜) (by norm_num) _
    (strictlyLocalizablePart_measurable hμ) (strictlyLocalizableParts_disjoint hμ)
    (strictlyLocalizable_sum_restrict hμ) i f using 1
  congr 1
  apply lp.ext
  funext j
  by_cases hji : j = i
  · subst j
    simp only [lp.single_apply_self]
  · simp [lp.single_apply, hji]

end PEMS
