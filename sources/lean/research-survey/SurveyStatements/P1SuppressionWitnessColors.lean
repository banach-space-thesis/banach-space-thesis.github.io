import SurveyStatements.P1SuppressionWitnesses
import Mathlib.Data.Nat.Pairing
import Mathlib.Algebra.Order.Floor.Semiring

/-! A bounded natural-number color records a witness's fixed finite phase
pair and its unit-width mass interval. The bound depends only on the first
point of the full coefficient support. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def UnitSuppressionWitness.phaseIndex {e : ℕ → X} {A : Finset ℂ}
    (w : UnitSuppressionWitness e A) : Fin (Fintype.card (↥A × ↥A)) :=
  Fintype.equivFin (↥A × ↥A) (⟨w.phaseCoeff, w.phaseCoeff_mem⟩, ⟨w.phaseValue, w.phaseValue_mem⟩)

def UnitSuppressionWitness.color {e : ℕ → X} {A : Finset ℂ}
    (w : UnitSuppressionWitness e A) : ℕ := Nat.pair w.phaseIndex.val ⌊w.mass⌋₊

def unitSuppressionColorBudget (A : Finset ℂ) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (Fintype.card (↥A × ↥A)))).product
    (Finset.range (witnessMassBudget k + 2))).sup (fun p => Nat.pair p.1.val p.2)

theorem UnitSuppressionWitness.color_bound {e : ℕ → X} {A : Finset ℂ}
    (w : UnitSuppressionWitness e A) :
    w.color ≤ unitSuppressionColorBudget A (sInf (w.coefficients.support : Set ℕ)) := by
  have hfloor : ⌊w.mass⌋₊ ≤ witnessMassBudget (sInf (w.coefficients.support : Set ℕ)) + 1 := by
    apply Nat.floor_le_of_le
    rw [w.first_support]
    simpa only [Nat.cast_add, Nat.cast_one] using w.mass_bound
  exact Finset.le_sup
    (s := (Finset.univ : Finset (Fin (Fintype.card (↥A × ↥A)))).product
      (Finset.range (witnessMassBudget (sInf (w.coefficients.support : Set ℕ)) + 2)))
    (b := (w.phaseIndex, ⌊w.mass⌋₊))
    (f := fun p : Fin (Fintype.card (↥A × ↥A)) × ℕ => Nat.pair p.1.val p.2)
    (Finset.mem_product.mpr ⟨Finset.mem_univ w.phaseIndex,
      Finset.mem_range.mpr (show ⌊w.mass⌋₊ <
        witnessMassBudget (sInf (w.coefficients.support : Set ℕ)) + 2 by omega)⟩)

theorem UnitSuppressionWitness.phase_eq_of_color_eq {e : ℕ → X} {A : Finset ℂ}
    (w v : UnitSuppressionWitness e A) (h : w.color = v.color) :
    w.phaseCoeff = v.phaseCoeff ∧ w.phaseValue = v.phaseValue := by
  have hi := (Nat.pair_eq_pair.mp h).1
  have ht := (Fintype.equivFin (↥A × ↥A)).injective (Fin.ext hi)
  exact ⟨congrArg (fun p : ↥A × ↥A => p.1.val) ht,
    congrArg (fun p : ↥A × ↥A => p.2.val) ht⟩

theorem UnitSuppressionWitness.mass_near_of_color_eq {e : ℕ → X} {A : Finset ℂ}
    (w v : UnitSuppressionWitness e A) (h : w.color = v.color) : v.mass - 1 ≤ w.mass := by
  have hf := (Nat.pair_eq_pair.mp h).2
  have hw : (⌊w.mass⌋₊ : ℝ) ≤ w.mass := Nat.floor_le (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hv : v.mass < (⌊v.mass⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one v.mass
  rw [← hf] at hv
  linarith

end SurveyStatements.P1
