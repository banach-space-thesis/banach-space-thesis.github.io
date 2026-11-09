import ThesisCommon.Analysis.GrothendieckMoments
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.RCLike.Basic

/-! A finite first-moment Khintchine estimate from the exact second and
fourth moments. The constants are deliberately conservative and uniform in
the number of signs. No probabilistic theorem is assumed. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
open Grothendieck

theorem rademacher_second_le_three_first_sq {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, a i ^ 2) ≤ 3 * mean (fun ε => |rademacher a ε|) ^ 2 := by
  let f : (Fin n → Bool) → ℝ := fun ε => |rademacher a ε|
  let q := ∑ i, a i ^ 2
  let A := mean f
  let B := mean (fun ε => f ε ^ 3)
  have hq : 0 ≤ q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA : 0 ≤ A := mean_nonneg fun ε => abs_nonneg _
  have hB : 0 ≤ B := mean_nonneg fun ε => by dsimp [f]; positivity
  have hsecond : mean (fun ε => f ε ^ 2) = q := by
    simpa only [f, sq_abs] using rademacher_second a
  have hfourth : mean (fun ε => f ε ^ 4) ≤ 3 * q ^ 2 := by
    simpa only [f, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs]
      using rademacher_fourth_le a
  have hroot (ε : Fin n → Bool) : Real.sqrt (f ε) ^ 2 = f ε :=
    Real.sq_sqrt (abs_nonneg _)
  have hcs₁ := mean_mul_sq_le (fun ε => Real.sqrt (f ε))
    (fun ε => f ε * Real.sqrt (f ε))
  have hprod : (fun ε => Real.sqrt (f ε) * (f ε * Real.sqrt (f ε))) =
      (fun ε => f ε ^ 2) := by
    funext ε
    nlinarith [hroot ε]
  have hg : (fun ε => (f ε * Real.sqrt (f ε)) ^ 2) =
      (fun ε => f ε ^ 3) := by
    funext ε
    rw [mul_pow, hroot]
    ring
  rw [hprod, hg, hsecond] at hcs₁
  simp only [hroot] at hcs₁
  have hcs₂ := mean_mul_sq_le f (fun ε => f ε ^ 2)
  have hcub : (fun ε => f ε * f ε ^ 2) = (fun ε => f ε ^ 3) := by
    funext ε
    ring
  have hpow : (fun ε => (f ε ^ 2) ^ 2) = (fun ε => f ε ^ 4) := by
    funext ε
    ring
  rw [hcub, hpow, hsecond] at hcs₂
  have hBsq : B ^ 2 ≤ 3 * q ^ 3 := by
    dsimp only [B]
    exact hcs₂.trans (by nlinarith [mul_le_mul_of_nonneg_left hfourth hq])
  have hq4 : q ^ 4 ≤ 3 * A ^ 2 * q ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left hBsq (sq_nonneg A)
    change q ^ 2 ≤ A * B at hcs₁
    nlinarith [sq_nonneg (q ^ 2 - A * B)]
  by_cases hzero : q = 0
  · dsimp only [q] at hzero
    rw [hzero]
    positivity
  have hpos : 0 < q ^ 3 := pow_pos (lt_of_le_of_ne hq (Ne.symm hzero)) _
  have heq : q ^ 4 = q * q ^ 3 := by ring
  rw [heq] at hq4
  exact (mul_le_mul_iff_of_pos_right hpos).mp hq4

end ThesisCommon
