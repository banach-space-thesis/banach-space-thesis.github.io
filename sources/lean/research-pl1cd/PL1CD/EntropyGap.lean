import PL1CD.EntropyScalar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section
open scoped BigOperators

namespace PL1CD.Entropy

def phi (a : ℝ) : ℝ := a * Real.log a

theorem hellinger_le_phi_gap (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤
      phi a - phi b - (Real.log b + 1) * (a - b) := by
  have h := hellinger_le_relativeEntropy a b ha hb
  by_cases hzero : a = 0
  · subst a
    dsimp [phi]
    nlinarith
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    rw [Real.log_div hap.ne' hb.ne'] at h
    dsimp [phi]
    nlinarith

theorem sum_hellinger_le_phi_gap {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (g : ℝ)
    (hmean : ∑ i, f i = (Fintype.card ι : ℝ) * g) :
    ∑ i, (Real.sqrt (f i) - Real.sqrt g) ^ 2 ≤
      (∑ i, phi (f i)) - (Fintype.card ι : ℝ) * phi g := by
  classical
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hg : 0 ≤ g := by
    have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hf i)
    rw [hmean] at hsum
    exact nonneg_of_mul_nonneg_right hsum hcard
  by_cases hzero : g = 0
  · have hall : ∀ i, f i = 0 := by
      have hsum : ∑ i, f i = 0 := by rw [hmean, hzero, mul_zero]
      exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hf j)).mp hsum i
        (Finset.mem_univ i)
    simp [hall, hzero, phi]
  · have hgp : 0 < g := lt_of_le_of_ne hg (Ne.symm hzero)
    calc
      _ ≤ ∑ i, (phi (f i) - phi g - (Real.log g + 1) * (f i - g)) :=
        Finset.sum_le_sum (fun i _ => hellinger_le_phi_gap (f i) g (hf i) hgp)
      _ = _ := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
        rw [hmean]
        ring

theorem average_hellinger_le_phi_gap {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (g : ℝ)
    (hmean : ∑ i, f i = (Fintype.card ι : ℝ) * g) :
    (Fintype.card ι : ℝ)⁻¹ * ∑ i, (Real.sqrt (f i) - Real.sqrt g) ^ 2 ≤
      (Fintype.card ι : ℝ)⁻¹ * (∑ i, phi (f i)) - phi g := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := mul_le_mul_of_nonneg_left (sum_hellinger_le_phi_gap f hf g hmean)
    (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card ι)))
  simpa only [mul_sub, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using h

end PL1CD.Entropy
