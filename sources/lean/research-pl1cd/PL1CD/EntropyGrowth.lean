import PL1CD.EntropyEnergy
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter
open scoped Topology

namespace PL1CD.EntropyEnergy

theorem entropy_growth_tendsto_zero
    (v entropy : ℕ → ℝ) (M N d : ℕ → ℕ) (a : ℕ → ℝ)
    (l : Filter ℕ) (ε c : ℝ) (hε : 0 ≤ ε) (ha : ∀ s, 0 ≤ a s)
    (hstep : ∀ n, v n ^ 2 ≤ 4 * (entropy (n + 1) - entropy n))
    (hN : ∀ᶠ s in l, 0 < N s)
    (hupper : ∀ᶠ s in l, entropy (N s) ≤
      (d s : ℝ) * Real.log 2 + Real.exp (-ε * a s) *
        ((M (N s) : ℝ) * Real.log 2 + c))
    (hd : Tendsto (fun s => (d s : ℝ) / N s) l (𝓝 0))
    (hM : Tendsto (fun s => ((M (N s) : ℝ) / N s) * Real.exp (-ε * a s)) l (𝓝 0))
    (hinv : Tendsto (fun s => (N s : ℝ)⁻¹) l (𝓝 0)) :
    Tendsto (fun s => (entropy (N s) - entropy 0) / (N s : ℝ)) l (𝓝 0) := by
  have ht := ((hd.mul_const (Real.log 2)).add (hM.mul_const (Real.log 2))).add
    (hinv.const_mul (|c| + |entropy 0|))
  apply squeeze_zero' _ _ (by simpa using ht)
  · filter_upwards [hN] with s hs
    have hn := Finset.sum_nonneg (s := Finset.range (N s))
      (fun n _ => sq_nonneg (v n))
    have he := energy_sum_le v entropy hstep (N s)
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  · filter_upwards [hupper] with s hs
    have hexp : Real.exp (-ε * a s) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [ha s])
    have hc : Real.exp (-ε * a s) * c ≤ |c| := by
      calc
        _ ≤ Real.exp (-ε * a s) * |c| :=
          mul_le_mul_of_nonneg_left (le_abs_self c) (Real.exp_pos _).le
        _ ≤ 1 * |c| := mul_le_mul_of_nonneg_right hexp (abs_nonneg c)
        _ = |c| := one_mul _
    have hup : entropy (N s) - entropy 0 ≤
        (d s : ℝ) * Real.log 2 +
          Real.exp (-ε * a s) * (M (N s) : ℝ) * Real.log 2 +
          (|c| + |entropy 0|) := by
      nlinarith [neg_le_abs (entropy 0)]
    have he := div_le_div_of_nonneg_right hup (Nat.cast_nonneg (N s) : (0 : ℝ) ≤ _)
    calc
      _ ≤ _ := he
      _ = (d s : ℝ) / N s * Real.log 2 +
          ((M (N s) : ℝ) / N s * Real.exp (-ε * a s)) * Real.log 2 +
          (|c| + |entropy 0|) * (N s : ℝ)⁻¹ := by
        simp only [div_eq_mul_inv]
        ring
    simpa only [neg_mul] using (le_refl
      ((d s : ℝ) / N s * Real.log 2 +
        ((M (N s) : ℝ) / N s * Real.exp (-ε * a s)) * Real.log 2 +
        (|c| + |entropy 0|) * (N s : ℝ)⁻¹))

end PL1CD.EntropyEnergy
