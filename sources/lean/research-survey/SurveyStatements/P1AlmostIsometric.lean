import SurveyStatements.P1Transfer

/-! The almost-isometric transfer lemma `p1-first:lem:transfer` in the source. -/

noncomputable section

set_option autoImplicit false

namespace SurveyStatements.P1

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Source almost-isometric transfer estimate, with precisely its constants. -/
theorem almostIsometric_transfer_bound (T : E →ₗ[ℂ] X)
    {δ σ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hlower : ∀ v, (1 - δ) * ‖v‖ ≤ ‖T v‖)
    (hupper : ∀ v, ‖T v‖ ≤ (1 + δ) * ‖v‖)
    {u : ℕ → E} (hu : ∀ n, ‖u n‖ = 1)
    (hs : ∀ n m, n ≠ m → σ ≤ toroidalDistance (u n) (u m)) :
    (∀ n, ‖unitNormalize (T (u n))‖ = 1) ∧
      ∀ n m, n ≠ m →
        ((1 - δ) * σ - 2 * δ) / (1 + δ) ≤
          toroidalDistance (unitNormalize (T (u n))) (unitNormalize (T (u m))) := by
  have ha : ∀ n, 1 - δ ≤ ‖T (u n)‖ ∧ ‖T (u n)‖ ≤ 1 + δ := by
    intro n
    constructor
    · simpa [hu n] using hlower (u n)
    · simpa [hu n] using hupper (u n)
  have hpos : ∀ n, 0 < ‖T (u n)‖ := by
    intro n
    have h := (ha n).1
    linarith
  have hnzero : ∀ n, T (u n) ≠ 0 := fun n => norm_pos_iff.mp (hpos n)
  refine ⟨fun n => norm_unitNormalize (hnzero n), ?_⟩
  intro n m hnm
  apply (le_toroidalDistance_iff _ _ _).mpr
  intro θ hθ
  have hsphase := (le_toroidalDistance_iff _ _ _).mp (hs n m hnm) θ hθ
  have hlow := hlower (u n - θ • u m)
  rw [map_sub, map_smul] at hlow
  have hlower' : (1 - δ) * σ ≤ ‖T (u n) - θ • T (u m)‖ := by
    exact (mul_le_mul_of_nonneg_left hsphase (by linarith)).trans hlow
  have heq : T (u n) - θ • T (u m) =
      (‖T (u n)‖ : ℂ) •
        (unitNormalize (T (u n)) - θ • unitNormalize (T (u m))) +
      ((‖T (u n)‖ - ‖T (u m)‖ : ℝ) : ℂ) • (θ • unitNormalize (T (u m))) := by
    simp only [Complex.ofReal_sub, sub_smul, smul_sub]
    rw [norm_smul_unitNormalize,
      smul_comm (‖T (u n)‖ : ℂ) θ,
      smul_comm (‖T (u m)‖ : ℂ) θ, norm_smul_unitNormalize]
    abel
  have hnorm : ‖T (u n) - θ • T (u m)‖ ≤
      ‖T (u n)‖ * ‖unitNormalize (T (u n)) - θ • unitNormalize (T (u m))‖ +
        |‖T (u n)‖ - ‖T (u m)‖| := by
    rw [heq]
    convert norm_add_le
      ((‖T (u n)‖ : ℂ) •
        (unitNormalize (T (u n)) - θ • unitNormalize (T (u m))))
      (((‖T (u n)‖ - ‖T (u m)‖ : ℝ) : ℂ) •
        (θ • unitNormalize (T (u m)))) using 1
    simp [norm_smul, norm_unit_smul hθ, norm_unitNormalize (hnzero m),
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have habs : |‖T (u n)‖ - ‖T (u m)‖| ≤ 2 * δ := by
    rw [abs_le]
    constructor <;> have h1 := ha n <;> have h2 := ha m <;> linarith
  have hmult : ‖T (u n)‖ *
      ‖unitNormalize (T (u n)) - θ • unitNormalize (T (u m))‖ ≤
      (1 + δ) * ‖unitNormalize (T (u n)) - θ • unitNormalize (T (u m))‖ :=
    mul_le_mul_of_nonneg_right (ha n).2 (norm_nonneg _)
  apply (div_le_iff₀ (by linarith : 0 < 1 + δ)).mpr
  nlinarith

/-- The transfer estimate is strictly above one under the source's threshold. -/
theorem transfer_bound_gt_one {δ σ : ℝ} (hδ0 : 0 < δ) (hσ : 1 < σ)
    (hδ : δ < (σ - 1) / (σ + 3)) :
    1 < ((1 - δ) * σ - 2 * δ) / (1 + δ) := by
  have hσ3 : 0 < σ + 3 := by linarith
  have hδ' := (lt_div_iff₀ hσ3).mp hδ
  apply (lt_div_iff₀ (by linarith : 0 < 1 + δ)).mpr
  nlinarith

/-- A sufficiently small almost-isometric distortion preserves the conclusion
of toroidal Elton–Odell. This is the last sentence of the source transfer lemma. -/
theorem almostIsometric_transfer (T : E →ₗ[ℂ] X)
    {δ σ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ : 1 < σ)
    (hδ : δ < (σ - 1) / (σ + 3))
    (hlower : ∀ v, (1 - δ) * ‖v‖ ≤ ‖T v‖)
    (hupper : ∀ v, ‖T v‖ ≤ (1 + δ) * ‖v‖)
    {u : ℕ → E} (hu : ∀ n, ‖u n‖ = 1)
    (hs : ∀ n m, n ≠ m → σ ≤ toroidalDistance (u n) (u m)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  obtain ⟨hx, hd⟩ := almostIsometric_transfer_bound T hδ0 hδ1 hlower hupper hu hs
  refine ⟨((1 - δ) * σ - 2 * δ) / (1 + δ) - 1,
    sub_pos.mpr (transfer_bound_gt_one hδ0 hσ hδ),
    fun n => unitNormalize (T (u n)), hx, ?_⟩
  apply separated_iff_toroidalDistance.mpr
  intro n m hnm
  simpa using hd n m hnm

end SurveyStatements.P1
