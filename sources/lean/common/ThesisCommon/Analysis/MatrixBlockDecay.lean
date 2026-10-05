import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The quantitative decay behind the matrix block averaging argument.
The floor N/k supplies quadratically many blocks, while the energy grows
with an exponent strictly below two. -/
noncomputable section
open Filter Topology
namespace ThesisCommon

theorem exists_matrixBlock_budget (k L : ℕ) (hk : 0 < k)
    (b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      0 < N / k ∧ (L : ℝ) * (N : ℝ) ^ b ≤ ((N / k : ℕ) : ℝ) ^ 2 * δ ^ 2 := by
  let C : ℝ := (L : ℝ) * (2 * (k : ℝ)) ^ b
  have ht : Tendsto (fun m : ℕ => (m : ℝ) ^ (b - 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hb2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [neg_sub] using h
  have hCt : Tendsto (fun m : ℕ => C * (m : ℝ) ^ (b - 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ht
  have hev : ∀ᶠ m : ℕ in atTop, C * (m : ℝ) ^ (b - 2) < δ ^ 2 :=
    (tendsto_order.mp hCt).2 _ (sq_pos_of_pos hδ)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  let K := max M 1
  refine ⟨K * k, Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)) hk, ?_⟩
  intro N hN
  let m := N / k
  have hKm : K ≤ m := (Nat.le_div_iff_mul_le hk).mpr hN
  have hm1 : 1 ≤ m := (le_max_right M 1).trans hKm
  have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm1
  refine ⟨hm0, ?_⟩
  have hbudget := (hM m ((le_max_left M 1).trans hKm)).le
  have hNbound : N ≤ (2 * k) * m := by
    have hf : N < k * (m + 1) := Nat.lt_mul_div_succ N hk
    have hkm : k ≤ k * m := by simpa only [mul_one] using Nat.mul_le_mul_left k hm1
    nlinarith
  have hNreal : (N : ℝ) ≤ (2 * (k : ℝ)) * (m : ℝ) := by exact_mod_cast hNbound
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm0
  have hpowers : (m : ℝ) ^ b = (m : ℝ) ^ 2 * (m : ℝ) ^ (b - 2) := by
    calc
      _ = (m : ℝ) ^ (2 + (b - 2)) := by congr 1; ring
      _ = (m : ℝ) ^ (2 : ℝ) * (m : ℝ) ^ (b - 2) := Real.rpow_add hmpos _ _
      _ = _ := by rw [Real.rpow_two]
  calc
    (L : ℝ) * (N : ℝ) ^ b ≤ (L : ℝ) * ((2 * (k : ℝ)) * (m : ℝ)) ^ b :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg N) hNreal hb0) (Nat.cast_nonneg L)
    _ = C * (m : ℝ) ^ b := by
      rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg m)]
      dsimp only [C]
      ring
    _ = (m : ℝ) ^ 2 * (C * (m : ℝ) ^ (b - 2)) := by rw [hpowers]; ring
    _ ≤ (m : ℝ) ^ 2 * δ ^ 2 := mul_le_mul_of_nonneg_left hbudget (sq_nonneg _)

end ThesisCommon
