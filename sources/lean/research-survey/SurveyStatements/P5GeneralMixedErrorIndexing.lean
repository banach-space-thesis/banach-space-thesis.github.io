import SurveyStatements.P5HaarBase
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-! The three off-diagonal classes exhaust the product matrix. These are
index identities only; operator boundedness is provided by the actual strip
and mixed-error constructions. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal Classical

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜]

def GeneralMixedStripIndex :=
  {q : DyadicIndex × DyadicIndex // q.1 ≠ q.2}

def GeneralMixedNuclearIndex :=
  {q : (DyadicIndex × DyadicIndex) × (DyadicIndex × DyadicIndex) //
    q.1.1 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2}

theorem generalMixed_subtype_single_sum {α : Type*} (P : α → Prop)
    (a : α) (c : 𝕜) :
    (∑' x : {b // P b}, if x.val = a then c else 0) = if P a then c else 0 := by
  by_cases ha : P a
  · rw [if_pos ha]
    let x₀ : {b // P b} := ⟨a, ha⟩
    rw [tsum_eq_single x₀]
    · simp [x₀]
    · intro x hx
      apply if_neg
      intro h
      apply hx
      exact Subtype.ext h
  · rw [if_neg ha]
    have hz : ∀ x : {b // P b}, (if x.val = a then c else 0) = 0 := by
      intro x
      apply if_neg
      intro h
      exact ha (h ▸ x.property)
    simp_rw [hz]
    exact tsum_zero

theorem generalMixed_matrix_classes_exhaust
    (a : DyadicIndex → DyadicIndex → DyadicIndex → DyadicIndex → 𝕜)
    (A B I R : DyadicIndex) :
    a A B I R =
      (if (A, B) = (I, R) then a I R I R else 0) +
      (if A = I ∧ B ≠ R then a I B I R else 0) +
      (if A ≠ I ∧ B = R then a A R I R else 0) +
      (if A ≠ I ∧ B ≠ R then a A B I R else 0) := by
  by_cases hA : A = I <;> by_cases hB : B = R <;> simp [hA, hB]

end SurveyStatements.P5
