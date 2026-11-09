import ThesisCommon.Analysis.Cotype
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-! Finite-sign estimates used in the UPFP forward and backward reductions.
The expectation is an explicit finite average, with exactly 2^n sign vectors.
These estimates expand the paper's numerical contradiction, without assuming
any coordinate-selection or diagonal-reduction conclusion.
-/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {X : Type*} [NormedAddCommGroup X] {q C : ℝ}

/-- Uniformly bounding every signed sum bounds the cotype power sum. -/
theorem HasRademacherCotype.sum_rpow_le_of_sign_bound
    (h : HasRademacherCotype X q C) {n : ℕ} (x : Fin n → X)
    {M : ℝ} (_hM : 0 ≤ M)
    (hsign : ∀ ε : Fin n → Bool, ‖∑ i, if ε i then x i else -x i‖ ≤ M) :
    ∑ i, ‖x i‖ ^ q ≤ C ^ q * M ^ q := by
  have hq : 0 ≤ q := (by norm_num : (0 : ℝ) ≤ 2).trans h.1
  have hC : 0 ≤ C := zero_le_one.trans h.2.1
  have hc : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  have hsum : (∑ ε : Fin n → Bool, ‖∑ i, if ε i then x i else -x i‖ ^ q)
      ≤ (2 : ℝ) ^ n * M ^ q := by
    calc
      _ ≤ ∑ _ε : Fin n → Bool, M ^ q := Finset.sum_le_sum fun ε _ =>
        Real.rpow_le_rpow (norm_nonneg _) (hsign ε) hq
      _ = _ := by simp [hc]
  calc
    _ ≤ C ^ q * ((2 : ℝ) ^ n)⁻¹ *
        ∑ ε : Fin n → Bool, ‖∑ i, if ε i then x i else -x i‖ ^ q := h.2.2 n x
    _ ≤ C ^ q * ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n * M ^ q) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

/-- If too many vectors were large, cotype would contradict the signed bound. -/
theorem HasRademacherCotype.exists_norm_lt_of_sign_bound
    (h : HasRademacherCotype X q C) {n : ℕ} (x : Fin n → X)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hsign : ∀ ε : Fin n → Bool, ‖∑ i, if ε i then x i else -x i‖ ≤ M)
    (hlarge : C ^ q * M ^ q < (n : ℝ) * δ ^ q) :
    ∃ i, ‖x i‖ < δ := by
  by_contra! hn
  have hq : 0 ≤ q := (by norm_num : (0 : ℝ) ≤ 2).trans h.1
  have hlower : (n : ℝ) * δ ^ q ≤ ∑ i, ‖x i‖ ^ q := by
    calc
      _ = ∑ _i : Fin n, δ ^ q := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => Real.rpow_le_rpow hδ (hn i) hq
  exact (not_lt_of_ge (hlower.trans (h.sum_rpow_le_of_sign_bound x hM hsign))) hlarge

/-- Raise the manuscript's threshold N^(1/q) ε > 2 C M to the qth power.
This is the numeric bridge for the test vectors of size ε/2. -/
theorem cotype_power_threshold {n : ℕ} {q C M ε : ℝ}
    (hq : 0 < q) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hlarge : 2 * C * M < (n : ℝ) ^ (1 / q) * ε) :
    C ^ q * M ^ q < (n : ℝ) * (ε / 2) ^ q := by
  have hprod : C * M < (n : ℝ) ^ (1 / q) * (ε / 2) := by linarith
  have hpow := Real.rpow_lt_rpow (mul_nonneg hC hM) hprod hq
  rw [Real.mul_rpow hC hM] at hpow
  have hε : 0 ≤ ε / 2 := by
    have hN : 0 ≤ (n : ℝ) ^ (1 / q) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    nlinarith [mul_nonneg hC hM]
  rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) hε,
    ← Real.rpow_mul (Nat.cast_nonneg n), one_div_mul_cancel hq.ne', Real.rpow_one] at hpow
  exact hpow

/-- Archimedean choice of the number of disjoint blocks. We choose it after
raising the paper's root inequality to the qth power. -/
theorem exists_cotype_power_threshold {q C M ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, C ^ q * M ^ q < (n : ℝ) * (ε / 2) ^ q := by
  have hpos : 0 < (ε / 2) ^ q := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ q * M ^ q / (ε / 2) ^ q)
  exact ⟨n, (div_lt_iff₀ hpos).mp hn⟩

end ThesisCommon
