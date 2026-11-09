import SurveyStatements.P1RosenthalDiagonal
import Mathlib.Analysis.SpecificLimits.Basic

/-! Absence of a weak-Cauchy subsequence forces a positive scalar tail
diameter obstruction stable under every further subsequence. -/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def HasScalarTailDiameter (s : ℕ → X) (ε : ℝ) : Prop :=
  ∀ f : X →L[ℂ] ℂ, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
    ‖f (s i) - f (s j)‖ ≤ ε * ‖f‖

theorem not_scalar_tail_diameter_exists_unit_functional (s : ℕ → X) {ε : ℝ}
    (hno : ¬ HasScalarTailDiameter s ε) :
    ∃ f : X →L[ℂ] ℂ, ‖f‖ = 1 ∧
      ∀ N : ℕ, ∃ i ≥ N, ∃ j ≥ N, ε < ‖f (s i) - f (s j)‖ := by
  classical
  unfold HasScalarTailDiameter at hno
  push_neg at hno
  obtain ⟨f, hosc⟩ := hno
  have hfne : f ≠ 0 := by
    intro hf
    obtain ⟨i, hi, j, hj, hlt⟩ := hosc 0
    simp only [hf, norm_zero, mul_zero, ContinuousLinearMap.zero_apply,
      sub_self] at hlt
    exact lt_irrefl 0 hlt
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hfne
  let z : ℂ := (‖f‖ : ℂ)⁻¹
  have hz : ‖z‖ = ‖f‖⁻¹ := by
    simp only [z, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfpos]
  refine ⟨z • f, ?_, ?_⟩
  · rw [norm_smul, hz, inv_mul_cancel₀ hfpos.ne']
  · intro N
    obtain ⟨i, hi, j, hj, hlt⟩ := hosc N
    refine ⟨i, hi, j, hj, ?_⟩
    change ε < ‖z • f (s i) - z • f (s j)‖
    rw [← smul_sub, norm_smul, hz]
    exact (lt_inv_mul_iff₀' hfpos).mpr hlt

theorem no_weakCauchy_subsequence_exists_stable_scalar_obstruction (s : ℕ → X)
    (hno : ¬ ∃ μ : ℕ → ℕ, StrictMono μ ∧ IsWeakCauchySequence (s ∘ μ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ν : ℕ → ℕ, StrictMono ν ∧
      ∀ κ : ℕ → ℕ, StrictMono κ → ¬ HasScalarTailDiameter (s ∘ ν ∘ κ) ε := by
  classical
  by_contra hnot
  push_neg at hnot
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let A := {v : ℕ → ℕ // StrictMono v}
  let identity : A := ⟨id, strictMono_id⟩
  have hex (n : ℕ) (v : A) :
      ∃ κ : ℕ → ℕ, StrictMono κ ∧ HasScalarTailDiameter (s ∘ v.val ∘ κ) (ε n) :=
    hnot (ε n) (hεpos n) v.val v.property
  let κ (n : ℕ) (v : A) : ℕ → ℕ := (hex n v).choose
  have hκ (n : ℕ) (v : A) : StrictMono (κ n v) := (hex n v).choose_spec.1
  have hbound (n : ℕ) (v : A) : HasScalarTailDiameter (s ∘ v.val ∘ κ n v) (ε n) :=
    (hex n v).choose_spec.2
  let next (n : ℕ) (v : A) : A := ⟨v.val ∘ κ n v, v.property.comp (hκ n v)⟩
  let v : ℕ → A := Nat.rec (next 0 identity) (fun n q => next (n + 1) q)
  let ν : ℕ → ℕ → ℕ := fun n => (v n).val
  have hν (n : ℕ) : StrictMono (ν n) := (v n).property
  have hnest (n : ℕ) : Set.range (ν (n + 1)) ⊆ Set.range (ν n) := by
    rintro a ⟨i, hi⟩
    exact ⟨κ (n + 1) (v n) i, hi⟩
  have hdiam (n : ℕ) : HasScalarTailDiameter (s ∘ ν n) (ε n) := by
    cases n with
    | zero => exact hbound 0 identity
    | succ n => exact hbound (n + 1) (v n)
  exact hno (nestedSubsequences_scalar_diameter_diagonal s ν hν hnest ε hε hdiam)

end SurveyStatements.P1
