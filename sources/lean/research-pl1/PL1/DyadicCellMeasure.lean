import PL1.DyadicTrace

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PL1.DyadicTrace

theorem cell_inter_Ico (n i : ℕ) (hi : i < 2 ^ n) :
    cell n i ∩ Set.Ico (0 : ℝ) 1 =
      Set.Ico ((i : ℝ) / 2 ^ n) (((i : ℝ) + 1) / 2 ^ n) := by
  have hp : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hip : (i : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hi
  have hindex (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) : index n x = ⌊(2 : ℝ) ^ n * x⌋₊ := by
    apply min_eq_left
    have hf : ⌊(2 : ℝ) ^ n * x⌋₊ < 2 ^ n :=
      (Nat.floor_lt (mul_nonneg hp.le hx.1)).mpr (by
        simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_one] using mul_lt_mul_of_pos_left hx.2 hp)
    omega
  ext x
  constructor
  · rintro ⟨hc, hx⟩
    have hf : ⌊(2 : ℝ) ^ n * x⌋₊ = i := (hindex x hx).symm.trans hc
    obtain ⟨hl, hu⟩ := (Nat.floor_eq_iff (mul_nonneg hp.le hx.1)).mp hf
    exact ⟨(div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hl),
      (lt_div_iff₀ hp).mpr (by simpa only [mul_comm] using hu)⟩
  · intro hx
    have hx0 : 0 ≤ x := (div_nonneg (Nat.cast_nonneg i) hp.le).trans hx.1
    have hx1 : x < 1 := hx.2.trans_le ((div_le_one hp).mpr hip)
    refine ⟨?_, hx0, hx1⟩
    change index n x = i
    rw [hindex x ⟨hx0, hx1⟩]
    apply (Nat.floor_eq_iff (mul_nonneg hp.le hx0)).mpr
    exact ⟨by simpa only [mul_comm] using (div_le_iff₀ hp).mp hx.1,
      by simpa only [mul_comm] using (lt_div_iff₀ hp).mp hx.2⟩

/-- Every nonempty indexed dyadic trace cell has exactly its usual dyadic
Lebesgue mass, including the clamped first and last cells. -/
theorem intervalMeasure_cell (n i : ℕ) (hi : i < 2 ^ n) :
    intervalMeasure (cell n i) = ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) := by
  rw [intervalMeasure, ← MeasureTheory.restrict_Ico_eq_restrict_Icc,
    Measure.restrict_apply (measurableSet_cell n i), cell_inter_Ico n i hi,
    Real.volume_Ico]
  have hp : (2 : ℝ) ^ n ≠ 0 := ne_of_gt (pow_pos (by norm_num) n)
  have heq : ((i : ℝ) + 1) / (2 : ℝ) ^ n - (i : ℝ) / 2 ^ n = ((2 : ℝ) ^ n)⁻¹ := by
    field_simp
    ring
  rw [heq]

theorem intervalMeasure_cell_toReal (n i : ℕ) (hi : i < 2 ^ n) :
    (intervalMeasure (cell n i)).toReal = ((2 : ℝ) ^ n)⁻¹ := by
  rw [intervalMeasure_cell n i hi, ENNReal.toReal_ofReal]
  positivity

end PL1.DyadicTrace
