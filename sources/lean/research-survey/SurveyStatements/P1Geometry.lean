import SurveyStatements.P1Definitions
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
Kernel-checked toroidal geometry and transfer lemmas used in Problem 1.
No result in this module depends on the unresolved main theorem.
-/

noncomputable section

set_option autoImplicit false

namespace SurveyStatements.P1

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

@[simp] theorem one_mem_unitScalars : (1 : ℂ) ∈ unitScalars := by
  simp [unitScalars]

theorem unitScalars_norm {θ : ℂ} (hθ : θ ∈ unitScalars) : ‖θ‖ = 1 := hθ

theorem unitScalars_ne_zero {θ : ℂ} (hθ : θ ∈ unitScalars) : θ ≠ 0 := by
  intro h
  simpa [h, unitScalars] using hθ

theorem unitScalars_inv {θ : ℂ} (hθ : θ ∈ unitScalars) : θ⁻¹ ∈ unitScalars := by
  simp [unitScalars, norm_inv, unitScalars_norm hθ]

theorem unitScalars_mul {θ φ : ℂ} (hθ : θ ∈ unitScalars) (hφ : φ ∈ unitScalars) :
    θ * φ ∈ unitScalars := by
  simp [unitScalars, norm_mul, unitScalars_norm hθ, unitScalars_norm hφ]

theorem norm_unit_smul {θ : ℂ} (hθ : θ ∈ unitScalars) (x : X) : ‖θ • x‖ = ‖x‖ := by
  rw [norm_smul, unitScalars_norm hθ, one_mul]

theorem phase_norm_inverse_symmetry (x y : X) {θ : ℂ} (hθ : θ ∈ unitScalars) :
    ‖x - θ • y‖ = ‖y - θ⁻¹ • x‖ := by
  have hid : θ • (y - θ⁻¹ • x) = -(x - θ • y) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (unitScalars_ne_zero hθ), one_smul]
    abel
  have hnorm := norm_unit_smul hθ (y - θ⁻¹ • x)
  rw [hid, norm_neg] at hnorm
  exact hnorm

private theorem phaseDistances_nonempty (x y : X) :
    {r : ℝ | ∃ θ ∈ unitScalars, r = ‖x - θ • y‖}.Nonempty := by
  exact ⟨‖x - (1 : ℂ) • y‖, 1, one_mem_unitScalars, rfl⟩

private theorem phaseDistances_bddBelow (x y : X) :
    BddBelow {r : ℝ | ∃ θ ∈ unitScalars, r = ‖x - θ • y‖} := by
  refine ⟨0, ?_⟩
  rintro r ⟨θ, _, rfl⟩
  exact norm_nonneg _

theorem toroidalDistance_nonneg (x y : X) : 0 ≤ toroidalDistance x y := by
  exact le_csInf (phaseDistances_nonempty x y) (by
    rintro r ⟨θ, _, rfl⟩
    exact norm_nonneg _)

theorem toroidalDistance_le_phase (x y : X) {θ : ℂ} (hθ : θ ∈ unitScalars) :
    toroidalDistance x y ≤ ‖x - θ • y‖ := by
  exact csInf_le (phaseDistances_bddBelow x y) ⟨θ, hθ, rfl⟩

theorem le_toroidalDistance_iff (x y : X) (r : ℝ) :
    r ≤ toroidalDistance x y ↔ ∀ θ ∈ unitScalars, r ≤ ‖x - θ • y‖ := by
  constructor
  · intro h θ hθ
    exact h.trans (toroidalDistance_le_phase x y hθ)
  · intro h
    apply le_csInf (phaseDistances_nonempty x y)
    rintro s ⟨θ, hθ, rfl⟩
    exact h θ hθ

theorem toroidalDistance_le_norm_sub (x y : X) : toroidalDistance x y ≤ ‖x - y‖ := by
  simpa using toroidalDistance_le_phase x y one_mem_unitScalars

theorem toroidalDistance_symm (x y : X) : toroidalDistance x y = toroidalDistance y x := by
  apply le_antisymm
  · apply (le_toroidalDistance_iff _ _ _).mpr
    intro θ hθ
    rw [phase_norm_inverse_symmetry y x hθ]
    exact toroidalDistance_le_phase x y (unitScalars_inv hθ)
  · apply (le_toroidalDistance_iff _ _ _).mpr
    intro θ hθ
    rw [phase_norm_inverse_symmetry x y hθ]
    exact toroidalDistance_le_phase y x (unitScalars_inv hθ)

@[simp] theorem toroidalDistance_self (x : X) : toroidalDistance x x = 0 := by
  exact le_antisymm (by simpa using toroidalDistance_le_norm_sub x x)
    (toroidalDistance_nonneg x x)

theorem separated_iff_toroidalDistance {ε : ℝ} {x : ℕ → X} :
    IsToroidallySeparated ε x ↔ ∀ n m, n ≠ m → 1 + ε ≤ toroidalDistance (x n) (x m) := by
  simp only [IsToroidallySeparated, le_toroidalDistance_iff]

theorem separated_injective {ε : ℝ} (hε : -1 < ε) {x : ℕ → X}
    (hx : IsToroidallySeparated ε x) : Function.Injective x := by
  intro n m hnm
  by_contra hne
  have h := hx n m hne 1 one_mem_unitScalars
  simp only [one_smul, hnm, sub_self, norm_zero] at h
  linarith

theorem separated_mono {ε η : ℝ} {x : ℕ → X} (hx : IsToroidallySeparated ε x)
    (h : η ≤ ε) : IsToroidallySeparated η x := by
  intro n m hnm θ hθ
  exact (add_le_add_left h 1).trans (hx n m hnm θ hθ)

theorem separated_subsequence {ε : ℝ} {x : ℕ → X} (hx : IsToroidallySeparated ε x)
    {f : ℕ → ℕ} (hf : Function.Injective f) : IsToroidallySeparated ε (x ∘ f) := by
  intro n m hnm θ hθ
  exact hx (f n) (f m) (fun h => hnm (hf h)) θ hθ

/-- Toroidal norm differences change by at most the sum of endpoint errors. -/
theorem phase_norm_perturbation (x y x' y' : X) {θ : ℂ} (hθ : θ ∈ unitScalars) :
    ‖x - θ • y‖ ≤ ‖x' - θ • y'‖ + ‖x - x'‖ + ‖y - y'‖ := by
  have hid : x - θ • y = (x' - θ • y') + (x - x') - θ • (y - y') := by
    simp only [smul_sub]
    abel
  rw [hid]
  calc
    ‖(x' - θ • y') + (x - x') - θ • (y - y')‖
        ≤ ‖(x' - θ • y') + (x - x')‖ + ‖θ • (y - y')‖ := norm_sub_le _ _
    _ ≤ (‖x' - θ • y'‖ + ‖x - x'‖) + ‖y - y'‖ := by
      rw [norm_unit_smul hθ]
      exact add_le_add_right (norm_add_le _ _) _

theorem separated_perturbation {ε δ : ℝ} {x y : ℕ → X}
    (hx : IsToroidallySeparated ε x) (hxy : ∀ n, ‖x n - y n‖ ≤ δ) :
    IsToroidallySeparated (ε - 2 * δ) y := by
  intro n m hnm θ hθ
  have h1 := hx n m hnm θ hθ
  have h2 := phase_norm_perturbation (x n) (x m) (y n) (y m) hθ
  have h3 := hxy n
  have h4 := hxy m
  linarith

theorem separated_linearIsometry {ε : ℝ} {x : ℕ → E}
    (hx : IsToroidallySeparated ε x) (T : E →ₗᵢ[ℂ] X) :
    IsToroidallySeparated ε (fun n => T (x n)) := by
  intro n m hnm θ hθ
  simpa only [← T.map_smul, ← T.map_sub, T.norm_map] using hx n m hnm θ hθ

end SurveyStatements.P1
