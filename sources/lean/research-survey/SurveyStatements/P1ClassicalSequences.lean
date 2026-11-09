import SurveyStatements.P1AlmostIsometric
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! The exact toroidal separation of the unit-vector sequence in complex ℓ₁. -/

noncomputable section

set_option autoImplicit false

namespace SurveyStatements.P1

/-- Complex ℓ₁, with mathlib's actual sum norm and completeness. -/
abbrev ComplexL1 := lp (fun _ : ℕ => ℂ) 1

/-- The canonical ℓ₁ unit vector. -/
def l1UnitVector (n : ℕ) : ComplexL1 := lp.single 1 n 1

@[simp] theorem norm_l1UnitVector (n : ℕ) : ‖l1UnitVector n‖ = 1 := by
  simpa [l1UnitVector] using lp.norm_single (E := fun _ : ℕ => ℂ) (p := 1)
    (by norm_num) n (1 : ℂ)

/-- The norm stays exactly two under every unimodular phase. -/
theorem l1UnitVector_phase_distance {n m : ℕ} (hnm : n ≠ m)
    {θ : ℂ} (hθ : θ ∈ unitScalars) :
    ‖l1UnitVector n - θ • l1UnitVector m‖ = 2 := by
  apply le_antisymm
  · have h := norm_sub_le (l1UnitVector n) (θ • l1UnitVector m)
    norm_num [norm_smul, unitScalars_norm hθ] at h ⊢
    exact h
  · have h := lp.sum_rpow_le_norm_rpow (p := 1) (by norm_num)
      (l1UnitVector n - θ • l1UnitVector m) ({n, m} : Finset ℕ)
    norm_num [l1UnitVector, lp.coeFn_sub, lp.coeFn_smul, lp.single_apply,
      hnm, Ne.symm hnm, unitScalars_norm hθ] at h ⊢
    exact h

theorem l1UnitVector_toroidalDistance {n m : ℕ} (hnm : n ≠ m) :
    toroidalDistance (l1UnitVector n) (l1UnitVector m) = 2 := by
  apply le_antisymm
  · have h := toroidalDistance_le_phase (l1UnitVector n) (l1UnitVector m)
      one_mem_unitScalars
    rwa [l1UnitVector_phase_distance hnm one_mem_unitScalars] at h
  · apply (le_toroidalDistance_iff _ _ _).mpr
    intro θ hθ
    exact le_of_eq (l1UnitVector_phase_distance hnm hθ).symm

/-- A fully proved classical ℓ₁ case of toroidal Elton–Odell. -/
theorem l1_toroidal_elton_odell :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → ComplexL1,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  refine ⟨1, by norm_num, l1UnitVector, norm_l1UnitVector, ?_⟩
  intro n m hnm θ hθ
  rw [l1UnitVector_phase_distance hnm hθ]
  norm_num

end SurveyStatements.P1
