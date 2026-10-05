import ThesisCommon.Analysis.GowersMaureyBlockAverageUpper
import ThesisCommon.Analysis.GowersMaureyGeometricGrowth

/-! Every subspace containing a genuine infinite block sequence contains
normalized m-piece averages with arbitrarily small loss. The contradiction
compares recursive grouping with the actual lower logarithmic estimate. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem hasBlockAverage_of_normalized_block_sequence (D : ConstructionData 𝕜)
    (Y : Submodule ℝ (C00 𝕜)) (u : ℕ → C00 𝕜)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hY : ∀ i, u i ∈ Y) (hnorm : ∀ i, implicitNorm D (u i) = 1)
    {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC : 1 < C) : HasBlockAverage D Y m C := by
  classical
  by_contra hno
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  obtain ⟨k, hk, hsmall⟩ := exists_logarithmicWeight_pow_lt hmR hC 1
  have hmp : 0 < m := by omega
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hmle : m ≤ m ^ k := by
    simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ m by omega) hk
  have hN : 2 ≤ m ^ k := hm.trans hmle
  let x (i : Fin (m ^ k)) := u i.val
  have hx : Successive x := fun i j hij => hu i.val j.val hij
  have hupper := no_block_average_power_bound D Y hmp hCpos hno k x hx
    (fun i => hY i.val) (fun i => (hnorm i.val).le)
  have hlower := successive_sum_lower_logarithmic D hN hx
  have hsum : (∑ i, implicitNorm D (x i)) = (m ^ k : ℕ) := by
    simp only [x, hnorm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  rw [hsum] at hlower
  have hf : 0 ≤ logarithmicWeight (m ^ k : ℕ) :=
    zero_le_one.trans (one_le_logarithmicWeight (by omega))
  have hbound := hlower.trans (mul_le_mul_of_nonneg_left hupper hf)
  have hsmall' : logarithmicWeight (m ^ k : ℕ) < C ^ k := by
    simpa only [Nat.cast_pow] using hsmall
  have hpos : 0 < ((m : ℝ) / C) ^ k := pow_pos (div_pos (by exact_mod_cast hmp) hCpos) k
  have hstrict := mul_lt_mul_of_pos_right hsmall' hpos
  have heq : C ^ k * ((m : ℝ) / C) ^ k = (m : ℝ) ^ k := by
    rw [← mul_pow]
    congr 1
    exact mul_div_cancel₀ _ hCpos.ne'
  rw [heq] at hstrict
  rw [Nat.cast_pow] at hbound
  exact (not_lt_of_ge hbound) (by simpa only [Nat.cast_pow] using hstrict)

theorem hasBlockAverage_of_block_sequence (D : ConstructionData 𝕜)
    (Y : Submodule ℝ (C00 𝕜)) (u : ℕ → C00 𝕜)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hY : ∀ i, u i ∈ Y) (hne : ∀ i, u i ≠ 0)
    {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC : 1 < C) : HasBlockAverage D Y m C := by
  let p := implicitNorm D
  have hp (i : ℕ) : 0 < p (u i) := by
    apply lt_of_le_of_ne (apply_nonneg _ _)
    intro hz
    exact hne i (implicitNorm_eq_zero D hz.symm)
  let v (i : ℕ) := (p (u i))⁻¹ • u i
  apply hasBlockAverage_of_normalized_block_sequence D Y v ?_ ?_ ?_ hm hC
  · intro i j hij s hs t ht
    exact hu i j hij s (Finsupp.support_smul hs) t (Finsupp.support_smul ht)
  · intro i
    exact Y.smul_mem _ (hY i)
  · intro i
    have hh := map_smul_eq_mul (p.restrictScalars ℝ) (p (u i))⁻¹ (u i)
    change p ((p (u i))⁻¹ • u i) = ‖(p (u i))⁻¹‖ * p (u i) at hh
    change p (v i) = 1
    change p ((p (u i))⁻¹ • u i) = 1
    rw [hh, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hp i)), inv_mul_cancel₀ (hp i).ne']

end ThesisCommon.GowersMaurey
