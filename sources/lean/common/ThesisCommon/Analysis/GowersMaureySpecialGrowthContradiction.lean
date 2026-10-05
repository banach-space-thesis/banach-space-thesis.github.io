import ThesisCommon.Analysis.GowersMaureyLowCodeBudget
import ThesisCommon.Analysis.GowersMaureyStandardProfiles

/-! The numerical contradiction at the end of the coded special-pair argument.
Along the actual even rapid sizes, the square-root lower estimate eventually
exceeds every fixed multiple of the logarithmic upper estimate. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem special_pair_lower_gt_upper {k F ε L r : ℝ}
    (hk : 0 < k) (hF : 0 < F) (hε : 0 < ε) (hr : 0 < r)
    (hroot : 96 * L / (r * ε) < Real.sqrt F) :
    L * (3 / r) * k / F < k * ε / (32 * Real.sqrt F) := by
  have hs : 0 < Real.sqrt F := Real.sqrt_pos.mpr hF
  have hh := (div_lt_iff₀ (mul_pos hr hε)).mp hroot
  have hmain : 96 * L / r < Real.sqrt F * ε := by
    apply (div_lt_iff₀ hr).mpr
    nlinarith [hh]
  apply (div_lt_div_iff₀ hF (mul_pos (by norm_num : (0 : ℝ) < 32) hs)).mpr
  calc
    L * (3 / r) * k * (32 * Real.sqrt F) =
        (96 * L / r) * (k * Real.sqrt F) := by ring
    _ < (Real.sqrt F * ε) * (k * Real.sqrt F) :=
      mul_lt_mul_of_pos_right hmain (mul_pos hk hs)
    _ = k * ε * (Real.sqrt F) ^ 2 := by ring
    _ = k * ε * F := by rw [Real.sq_sqrt hF.le]

theorem ConstructionData.eventually_special_pair_lower_gt_upper
    (D : ConstructionData 𝕜) {ε L r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∀ᶠ t : ℕ in atTop,
      L * (3 / r) * (D.j (2 * t) : ℝ) / logarithmicWeight (D.j (2 * t)) <
        (D.j (2 * t) : ℝ) * ε / (32 * Real.sqrt (logarithmicWeight (D.j (2 * t)))) := by
  have heven : StrictMono (fun t : ℕ => 2 * t) := by
    intro m n hmn
    change 2 * m < 2 * n
    omega
  have hseq : Tendsto (fun t : ℕ => (D.j (2 * t) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (D.j_strict.tendsto_atTop.comp heven.tendsto_atTop)
  have hroot := (tendsto_sqrt_logarithmicWeight_atTop.comp hseq).eventually
    (eventually_gt_atTop (96 * L / (r * ε)))
  filter_upwards [hroot] with t ht
  have hk : 0 < (D.j (2 * t) : ℝ) := lt_of_lt_of_le zero_lt_one (D.one_le_size _)
  have hF : 0 < logarithmicWeight (D.j (2 * t)) := by
    have h := D.specialSize_weight_large ⟨t, rfl⟩
    linarith
  exact special_pair_lower_gt_upper hk hF hε hr ht

theorem ConstructionData.exists_special_pair_lower_gt_upper
    (D : ConstructionData 𝕜) {ε L r : ℝ} (hε : 0 < ε) (hr : 0 < r) (N : ℕ) :
    ∃ t : ℕ, N ≤ t ∧
      L * (3 / r) * (D.j (2 * t) : ℝ) / logarithmicWeight (D.j (2 * t)) <
        (D.j (2 * t) : ℝ) * ε / (32 * Real.sqrt (logarithmicWeight (D.j (2 * t)))) := by
  exact ((eventually_ge_atTop N).and
    (D.eventually_special_pair_lower_gt_upper hε hr)).exists

end ThesisCommon.GowersMaurey
