import SurveyStatements.P1L1Separation
import SurveyStatements.P1ClassicalSequences

/-! Transfer from actual isomorphic copies of complex ℓ₁, with arbitrary
isomorphism constants. The finite-block proof supplies the distortion step. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace SurveyStatements.P1

theorem norm_l1UnitVector_linearCombination (b : ℕ →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ l1UnitVector b‖ = coefficientL1Mass b := by
  classical
  have hsingle (i : ℕ) : b i • l1UnitVector i = lp.single 1 i (b i) := by
    simp [l1UnitVector, ← lp.single_smul]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, hsingle, coefficientL1Mass]
  simpa using lp.norm_sum_single (E := fun _ : ℕ => ℂ) (p := 1)
    (by norm_num) (fun i => b i) b.support

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Any bounded below complex-linear embedding of actual ℓ₁ supplies the
source conclusion. No near-isometry premise is required. -/
theorem l1_embedding_toroidal_elton_odell (T : ComplexL1 →L[ℂ] X) {L : ℝ}
    (hL : 0 < L) (hlower : ∀ v : ComplexL1, L * ‖v‖ ≤ ‖T v‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  apply l1_equivalent_sequence_toroidal_elton_odell (T ∘ l1UnitVector) (U := ‖T‖) hL
  · intro b
    have hEq : Finsupp.linearCombination ℂ (T ∘ l1UnitVector) b =
        T (Finsupp.linearCombination ℂ l1UnitVector b) :=
      (Finsupp.apply_linearCombination ℂ T.toLinearMap l1UnitVector b).symm
    rw [hEq, ← norm_l1UnitVector_linearCombination b]
    exact hlower _
  · intro b
    have hEq : Finsupp.linearCombination ℂ (T ∘ l1UnitVector) b =
        T (Finsupp.linearCombination ℂ l1UnitVector b) :=
      (Finsupp.apply_linearCombination ℂ T.toLinearMap l1UnitVector b).symm
    rw [hEq, ← norm_l1UnitVector_linearCombination b]
    exact T.le_opNorm _

/-- The source ℓ₁-copy case for a genuine continuous linear equivalence onto
a subspace of the ambient complex normed space. -/
theorem l1_isomorphicCopy_toroidal_elton_odell (S : Submodule ℂ X)
    (T : ComplexL1 ≃L[ℂ] S) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  let J : ComplexL1 →L[ℂ] X := S.subtypeL.comp T.toContinuousLinearMap
  have hpos : 0 < ‖T.symm.toContinuousLinearMap‖ + 1 := by positivity
  apply l1_embedding_toroidal_elton_odell J (L := (‖T.symm.toContinuousLinearMap‖ + 1)⁻¹)
    (inv_pos.mpr hpos)
  intro v
  change (‖T.symm.toContinuousLinearMap‖ + 1)⁻¹ * ‖v‖ ≤ ‖T v‖
  rw [← div_eq_inv_mul, div_le_iff₀ hpos]
  have hbound := T.symm.toContinuousLinearMap.le_opNorm (T v)
  simp only [ContinuousLinearEquiv.coe_coe, T.symm_apply_apply] at hbound
  nlinarith [norm_nonneg (T v)]

end SurveyStatements.P1
