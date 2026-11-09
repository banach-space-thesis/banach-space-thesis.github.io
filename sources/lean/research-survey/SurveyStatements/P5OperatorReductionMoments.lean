import SurveyStatements.P5Support.HaarSignSecondMoment

/-! Finite centered quadratic moments for the actual signed block diagonal.
The matrix need not be symmetric and the scalar field may be real or complex.
All expectations are explicit averages over the finite sign cube. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

def scalarSign (b : Bool) : 𝕜 := if b then 1 else -1

theorem scalarSign_mul (b : Bool) (z : 𝕜) :
    scalarSign b * z = signedValue b z := by
  cases b <;> simp [scalarSign, signedValue]

def centeredQuadraticForm {n : ℕ} (a : Fin n → Fin n → 𝕜)
    (θ : Fin n → Bool) : 𝕜 :=
  ∑ i, ∑ j, if i = j then 0 else scalarSign (θ i) * scalarSign (θ j) * a i j

theorem centeredQuadraticForm_eq_diagonal_error {n : ℕ}
    (a : Fin n → Fin n → 𝕜) (θ : Fin n → Bool) :
    centeredQuadraticForm a θ =
      (∑ i, ∑ j, scalarSign (θ i) * scalarSign (θ j) * a i j) - ∑ i, a i i := by
  have hrow (i : Fin n) :
      (∑ j, scalarSign (θ i) * scalarSign (θ j) * a i j) =
        a i i + ∑ j, if i = j then 0 else scalarSign (θ i) * scalarSign (θ j) * a i j := by
    have hs : scalarSign (𝕜 := 𝕜) (θ i) * scalarSign (θ i) = 1 := by
      cases θ i <;> simp [scalarSign]
    have hterm (j : Fin n) :
        scalarSign (θ i) * scalarSign (θ j) * a i j =
          (if i = j then a i i else 0) +
            (if i = j then 0 else scalarSign (θ i) * scalarSign (θ j) * a i j) := by
      by_cases hij : i = j
      · subst j
        simp [hs]
      · simp [hij]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib]
    simp
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  simp only [centeredQuadraticForm]
  ring

theorem centeredQuadraticForm_cons {n : ℕ}
    (a : Fin (n + 1) → Fin (n + 1) → 𝕜) (b : Bool) (θ : Fin n → Bool) :
    centeredQuadraticForm a (Fin.cons b θ) =
      centeredQuadraticForm (fun i j => a i.succ j.succ) θ +
        signedValue b (∑ j, signedValue (θ j) (a 0 j.succ + a j.succ 0)) := by
  have hzero (j : Fin n) : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  simp only [← scalarSign_mul, Finset.mul_sum, mul_add]
  simp only [centeredQuadraticForm, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.succ_ne_zero, hzero, Fin.succ_inj,
    if_true, if_false, zero_add, Finset.sum_add_distrib]
  have hcomm (j : Fin n) :
      scalarSign (θ j) * scalarSign b * a j.succ 0 =
        scalarSign b * (scalarSign (θ j) * a j.succ 0) := by ring
  have hassoc (j : Fin n) :
      scalarSign b * scalarSign (θ j) * a 0 j.succ =
        scalarSign b * (scalarSign (θ j) * a 0 j.succ) := by ring
  simp_rw [hcomm, hassoc]
  ring

theorem norm_add_sub_square (x y : 𝕜) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  simp only [RCLike.norm_sq_eq_def, map_add, map_sub]
  ring

theorem norm_add_square_le (x y : 𝕜) :
    ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := norm_add_sub_square x y
  nlinarith [sq_nonneg ‖x - y‖]

theorem norm_sub_add_square (x y : 𝕜) :
    ‖x - y‖ ^ 2 + ‖x + y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  rw [add_comm, norm_add_sub_square]

def offDiagonalSquareSum {n : ℕ} (a : Fin n → Fin n → 𝕜) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else ‖a i j‖ ^ 2

theorem offDiagonalSquareSum_cons {n : ℕ}
    (a : Fin (n + 1) → Fin (n + 1) → 𝕜) :
    offDiagonalSquareSum a =
      offDiagonalSquareSum (fun i j => a i.succ j.succ) +
        ∑ j : Fin n, (‖a 0 j.succ‖ ^ 2 + ‖a j.succ 0‖ ^ 2) := by
  have hzero (j : Fin n) : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  simp only [offDiagonalSquareSum, Fin.sum_univ_succ, Fin.succ_ne_zero,
    hzero, Fin.succ_inj, if_true, if_false, zero_add,
    Finset.sum_add_distrib]
  ring

theorem centeredQuadraticForm_variance_le {n : ℕ} (a : Fin n → Fin n → 𝕜) :
    mean (fun θ => ‖centeredQuadraticForm a θ‖ ^ 2) ≤
      2 * offDiagonalSquareSum a := by
  induction n with
  | zero => simp [centeredQuadraticForm, offDiagonalSquareSum, mean]
  | succ n ih =>
    rw [mean_succ, ← mean_add]
    simp only [centeredQuadraticForm_cons, signedValue, Bool.false_eq_true,
      if_false, if_true, ← sub_eq_add_neg]
    simp_rw [norm_sub_add_square]
    rw [mean_add, mean_mul_left, mean_mul_left]
    have hlinear := haar_sign_second_moment (fun j : Fin n => a 0 j.succ + a j.succ 0)
    simp only [signedValue] at hlinear
    rw [hlinear]
    have hsum : (∑ j : Fin n, ‖a 0 j.succ + a j.succ 0‖ ^ 2) ≤
        2 * ∑ j : Fin n, (‖a 0 j.succ‖ ^ 2 + ‖a j.succ 0‖ ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => norm_add_square_le _ _)
    rw [offDiagonalSquareSum_cons]
    have htail := ih (fun i j => a i.succ j.succ)
    linarith

/-- The normalized centered form is exactly the off-diagonal error of a
uniform signed block. The estimate has the required inverse-square factor. -/
theorem normalized_centeredQuadraticForm_variance_le {n : ℕ}
    (a : Fin n → Fin n → 𝕜) :
    mean (fun θ => ‖(n : 𝕜)⁻¹ * centeredQuadraticForm a θ‖ ^ 2) ≤
      2 * ((n : ℝ)⁻¹) ^ 2 * offDiagonalSquareSum a := by
  have hnorm (θ : Fin n → Bool) :
      ‖(n : 𝕜)⁻¹ * centeredQuadraticForm a θ‖ ^ 2 =
        ((n : ℝ)⁻¹) ^ 2 * ‖centeredQuadraticForm a θ‖ ^ 2 := by
    simp [norm_mul, norm_inv, mul_pow]
  simp_rw [hnorm]
  rw [mean_mul_left]
  have h := mul_le_mul_of_nonneg_left (centeredQuadraticForm_variance_le a)
    (sq_nonneg ((n : ℝ)⁻¹))
  calc
    _ ≤ ((n : ℝ)⁻¹) ^ 2 * (2 * offDiagonalSquareSum a) := h
    _ = _ := by ring

/-- Finite selection applies jointly to linear, quadratic, and trace
balancing errors once their actual second moments have been estimated. -/
theorem finite_sign_simultaneous_small {m n : ℕ}
    (f : Fin m → (Fin n → Bool) → 𝕜) {ε : ℝ} (hε : 0 < ε)
    (hsmall : (∑ r, mean (fun θ => ‖f r θ‖ ^ 2)) < ε ^ 2) :
    ∃ θ : Fin n → Bool, ∀ r, ‖f r θ‖ < ε := by
  have hex : ∃ θ : Fin n → Bool, (∑ r, ‖f r θ‖ ^ 2) < ε ^ 2 := by
    by_contra h
    push_neg at h
    have havg := mean_mono h
    rw [mean_const, mean_sum] at havg
    linarith
  obtain ⟨θ, hθ⟩ := hex
  refine ⟨θ, fun r => ?_⟩
  have hr : ‖f r θ‖ ^ 2 ≤ ∑ s, ‖f s θ‖ ^ 2 :=
    Finset.single_le_sum (f := fun s : Fin m => ‖f s θ‖ ^ 2)
      (fun s _ => sq_nonneg _) (Finset.mem_univ r)
  nlinarith [norm_nonneg (f r θ)]

end SurveyStatements.P5OperatorReduction
