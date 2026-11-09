import SurveyStatements.P1AlmostIsometric
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! The source's explicit complex c₀ sequence and its √2 toroidal bound. -/

noncomputable section

set_option autoImplicit false

open Filter Topology

namespace SurveyStatements.P1

/-- The genuine sup-norm space of complex sequences vanishing at infinity. -/
abbrev ComplexC0 := ZeroAtInftyContinuousMap ℕ ℂ

/-- The sequence `e₀ + ⋯ + eₙ - eₙ₊₁` in complex c₀. -/
def c0UnitSequence (n : ℕ) : ComplexC0 where
  toFun k := if k ≤ n then 1 else if k = n + 1 then -1 else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) (cocompact ℕ) (𝓝 0)).congr'
    filter_upwards [(Set.finite_Iic (n + 1)).isCompact.compl_mem_cocompact] with k hk
    have hk' : n + 1 < k := by simpa using hk
    simp [show ¬ k ≤ n by omega, show k ≠ n + 1 by omega]

@[simp] theorem c0UnitSequence_apply (n k : ℕ) :
    c0UnitSequence n k = if k ≤ n then 1 else if k = n + 1 then -1 else 0 := rfl

@[simp] theorem norm_c0UnitSequence (n : ℕ) : ‖c0UnitSequence n‖ = 1 := by
  apply le_antisymm
  · change ‖(c0UnitSequence n).toBCF‖ ≤ 1
    apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
    intro k
    change ‖c0UnitSequence n k‖ ≤ 1
    by_cases h : k ≤ n
    · simp [h]
    · by_cases h' : k = n + 1 <;> simp [h, h']
  · have h := (c0UnitSequence n).toBCF.norm_coe_le_norm 0
    simpa using h

/-- Two scalar phase differences cannot both have modulus below √2. -/
theorem sqrt_two_le_max_phase {θ : ℂ} (hθ : θ ∈ unitScalars) :
    Real.sqrt 2 ≤ max ‖1 - θ‖ ‖1 + θ‖ := by
  have hsum : ‖1 - θ‖ ^ 2 + ‖1 + θ‖ ^ 2 = 4 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub, Complex.normSq_add]
    simp only [Complex.normSq_eq_norm_sq, unitScalars_norm hθ, norm_one, one_pow]
    ring
  have ha : 0 ≤ ‖(1 : ℂ) - θ‖ := norm_nonneg _
  have hb : 0 ≤ ‖(1 : ℂ) + θ‖ := norm_nonneg _
  have hmax : 0 ≤ max ‖1 - θ‖ ‖1 + θ‖ := ha.trans (le_max_left _ _)
  apply (Real.sqrt_le_left hmax).mpr
  have h1 := le_max_left ‖(1 : ℂ) - θ‖ ‖1 + θ‖
  have h2 := le_max_right ‖(1 : ℂ) - θ‖ ‖1 + θ‖
  nlinarith

theorem c0UnitSequence_phase_lower_of_lt {n m : ℕ} (hnm : n < m)
    {θ : ℂ} (hθ : θ ∈ unitScalars) :
    Real.sqrt 2 ≤ ‖c0UnitSequence n - θ • c0UnitSequence m‖ := by
  have hfirst := (c0UnitSequence n - θ • c0UnitSequence m).toBCF.norm_coe_le_norm 0
  have hnext := (c0UnitSequence n - θ • c0UnitSequence m).toBCF.norm_coe_le_norm (n + 1)
  have hfirst' : ‖(1 : ℂ) - θ‖ ≤ ‖c0UnitSequence n - θ • c0UnitSequence m‖ := by
    simpa using hfirst
  have hnext' : ‖(1 : ℂ) + θ‖ ≤ ‖c0UnitSequence n - θ • c0UnitSequence m‖ := by
    have hn : ¬ n + 1 ≤ n := by omega
    have hm : n + 1 ≤ m := hnm
    have hnext0 : ‖(-1 : ℂ) - θ‖ ≤ ‖c0UnitSequence n - θ • c0UnitSequence m‖ := by
      simpa [hn, hm] using hnext
    rwa [show (-1 : ℂ) - θ = -(1 + θ) by ring, norm_neg] at hnext0
  exact (sqrt_two_le_max_phase hθ).trans (max_le hfirst' hnext')

theorem c0UnitSequence_phase_lower {n m : ℕ} (hnm : n ≠ m)
    {θ : ℂ} (hθ : θ ∈ unitScalars) :
    Real.sqrt 2 ≤ ‖c0UnitSequence n - θ • c0UnitSequence m‖ := by
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact c0UnitSequence_phase_lower_of_lt hlt hθ
  · rw [phase_norm_inverse_symmetry (c0UnitSequence n) (c0UnitSequence m) hθ]
    exact c0UnitSequence_phase_lower_of_lt hgt (unitScalars_inv hθ)

theorem c0UnitSequence_toroidalDistance {n m : ℕ} (hnm : n ≠ m) :
    Real.sqrt 2 ≤ toroidalDistance (c0UnitSequence n) (c0UnitSequence m) := by
  apply (le_toroidalDistance_iff _ _ _).mpr
  intro θ hθ
  exact c0UnitSequence_phase_lower hnm hθ

/-- A fully proved classical c₀ case of toroidal Elton–Odell. -/
theorem c0_toroidal_elton_odell :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → ComplexC0,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  have hsqrt : 1 < Real.sqrt 2 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 : ℝ) < 2)
    simpa using h
  refine ⟨Real.sqrt 2 - 1, sub_pos.mpr hsqrt, c0UnitSequence, norm_c0UnitSequence, ?_⟩
  intro n m hnm θ hθ
  simpa using c0UnitSequence_phase_lower hnm hθ

end SurveyStatements.P1
