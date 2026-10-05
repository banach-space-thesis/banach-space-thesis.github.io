import ThesisCommon.Analysis.GowersMaureyMismatchSizes

/-! Positivity and strict increase of the genuine floor-square-root
construction sizes used in the outer RIS. -/
noncomputable section
namespace ThesisCommon.GowersMaurey.ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜] (D : ConstructionData 𝕜)

theorem floor_sqrt_size_pos (n : ℕ) :
    0 < ⌊Real.sqrt (D.j n : ℝ)⌋₊ := by
  have h : (1 : ℝ) ≤ Real.sqrt (D.j n : ℝ) := Real.one_le_sqrt.mpr (D.one_le_size n)
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one
    (Nat.le_floor (n := 1) (by simpa only [Nat.cast_one] using h))

theorem floor_sqrt_size_lt_size (n : ℕ) :
    ⌊Real.sqrt (D.j n : ℝ)⌋₊ < D.j n := by
  apply (Nat.floor_lt (Real.sqrt_nonneg _)).mpr
  apply (Real.sqrt_lt' (by exact_mod_cast D.j_positive n)).mpr
  have h := D.size_large n
  nlinarith

theorem floor_sqrt_size_strictMono :
    StrictMono (fun n => ⌊Real.sqrt (D.j n : ℝ)⌋₊) := by
  intro m n hmn
  exact (D.floor_sqrt_size_lt_size m).trans_le (Nat.le_floor (D.size_le_sqrt_size hmn))

end ThesisCommon.GowersMaurey.ConstructionData
