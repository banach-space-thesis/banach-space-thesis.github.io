import Posets.MatrixDomination
import Posets.SupportingStatements
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

/-! Borel ingredients for the acceptance/rejection dichotomy. These theorems
establish measurability of compact matrix restrictions. They do not assume or
claim the missing Borel square dichotomy or matrix rejection construction. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology MeasureTheory
namespace Posets

/-- The subset of natural numbers represented by a binary sequence. -/
def cantorSet (p : ℕ → Bool) : Set ℕ := {n | p n = true}

@[simp] theorem cantorSet_cantorCode (A : Set ℕ) : cantorSet (cantorCode A) = A := by
  ext n
  simp [cantorSet, cantorCode]

@[simp] theorem cantorCode_cantorSet (p : ℕ → Bool) : cantorCode (cantorSet p) = p := by
  funext n
  simp [cantorCode, cantorSet]

variable {𝕜 : Type} [RCLike 𝕜]

local instance : MeasurableSpace (ℕ → Bool) := borel (ℕ → Bool)
local instance : BorelSpace (ℕ → Bool) := ⟨rfl⟩
local instance : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool)) := borel _
local instance : BorelSpace ((ℕ → Bool) × (ℕ → Bool)) := ⟨rfl⟩

theorem measurable_cantor_restriction_tail_nnnorm (M : ScalarMatrix 𝕜) (j k n : ℕ) :
    Measurable (fun p : (ℕ → Bool) × (ℕ → Bool) =>
      ‖matrixTail 𝕜 (matrixRestriction 𝕜 M (cantorSet p.1) (cantorSet p.2)) j k n‖₊) := by
  have hs : MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | p.2 k = true ∧ p.1 n = true} :=
    ((isClosed_eq ((continuous_apply k).comp continuous_snd) continuous_const).measurableSet).inter
      ((isClosed_eq ((continuous_apply n).comp continuous_fst) continuous_const).measurableSet)
  by_cases h : j < n
  · simpa [matrixTail, matrixRestriction, cantorSet, h, apply_ite] using
      (measurable_const.ite hs measurable_const : Measurable
        (fun p : (ℕ → Bool) × (ℕ → Bool) => if p.2 k = true ∧ p.1 n = true then ‖M k n‖₊ else 0))
  · simp only [matrixTail, if_neg h, nnnorm_zero]
    exact measurable_const

theorem measurable_cantor_restriction_tail_norm (M : ScalarMatrix 𝕜) (j : ℕ) :
    Measurable (fun p : (ℕ → Bool) × (ℕ → Bool) =>
      matrixNorm 𝕜 (matrixTail 𝕜 (matrixRestriction 𝕜 M (cantorSet p.1) (cantorSet p.2)) j)) := by
  apply Measurable.iSup
  intro k
  have h := (Measurable.nnreal_tsum (fun n => measurable_cantor_restriction_tail_nnnorm M j k n)).coe_nnreal_real
  simpa only [NNReal.coe_tsum, coe_nnnorm] using h

/-- Compactness of restrictions is Borel in both the input and output subsets. -/
theorem measurableSet_acceptsPair_cantor (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M) :
    MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | AcceptsPair 𝕜 (cantorSet p.1) (cantorSet p.2) M} := by
  have h := measurableSet_tendsto (l := atTop) (𝓝 (0 : ℝ))
    (fun j => measurable_cantor_restriction_tail_norm M j)
  simpa only [AcceptsPair, IsCompactMatrix, boundedRows_matrixRestriction M hM,
    true_and] using h

/-- The one-set compactness predicate used in the cited descriptive-set proof. -/
theorem measurableSet_self_acceptsPair_cantor (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M) :
    MeasurableSet {p : ℕ → Bool | AcceptsPair 𝕜 (cantorSet p) (cantorSet p) M} := by
  have hd : Continuous (fun p : ℕ → Bool => (p, p)) := continuous_id.prodMk continuous_id
  have hm : Measurable (fun p : ℕ → Bool => (p, p)) := hd.measurable
  exact MeasurableSet.preimage (f := fun p : ℕ → Bool => (p, p))
    (measurableSet_acceptsPair_cantor M hM) hm

end Posets
