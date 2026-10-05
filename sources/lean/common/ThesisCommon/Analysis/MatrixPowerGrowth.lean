import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A common finite cutoff for the two sublinear powers occurring in
the matrix row and column coefficient estimates. -/
noncomputable section
open Filter Topology
namespace ThesisCommon

theorem exists_nat_two_sublinear_powers (r s K : ℝ) (hr : r < 1) (hs : s < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, 0 < m ∧ K * (m : ℝ) ^ r < δ * m ∧ K * (m : ℝ) ^ s < δ * m := by
  have hev (t : ℝ) (ht : t < 1) :
      ∀ᶠ m : ℕ in atTop, K * (m : ℝ) ^ (t - 1) < δ := by
    have hlim : Tendsto (fun m : ℕ => (m : ℝ) ^ (t - 1)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (sub_pos.mpr ht)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa only [neg_sub] using h
    have hK : Tendsto (fun m : ℕ => K * (m : ℝ) ^ (t - 1)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hlim
    exact (tendsto_order.mp hK).2 _ hδ
  obtain ⟨m, hm, hmr, hms⟩ := ((eventually_gt_atTop 0).and ((hev r hr).and (hev s hs))).exists
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hpower (t : ℝ) : (m : ℝ) ^ (t - 1) * (m : ℝ) = (m : ℝ) ^ t := by
    calc
      _ = (m : ℝ) ^ (t - 1) * (m : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (m : ℝ) ^ ((t - 1) + 1) := (Real.rpow_add hmpos _ _).symm
      _ = _ := by congr 1; ring
  refine ⟨m, hm, ?_, ?_⟩
  · have h := mul_lt_mul_of_pos_right hmr hmpos
    simpa only [mul_assoc, hpower] using h
  · have h := mul_lt_mul_of_pos_right hms hmpos
    simpa only [mul_assoc, hpower] using h

theorem exists_matrix_row_column_power_cutoff (p : BanachExponent)
    (hp : 1 < p.val.toReal) (K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, 0 < m ∧ K * (m : ℝ) ^ (1 / p.val.toReal) < δ * m ∧
      K * (m : ℝ) ^ (1 / (p.val.toReal / (p.val.toReal - 1))) < δ * m := by
  have hp0 : 0 < p.val.toReal := lt_trans zero_lt_one hp
  have hq : 1 < p.val.toReal / (p.val.toReal - 1) := by
    apply (lt_div_iff₀ (sub_pos.mpr hp)).mpr
    linarith
  exact exists_nat_two_sublinear_powers _ _ K
    ((div_lt_one hp0).mpr hp) ((div_lt_one (lt_trans zero_lt_one hq)).mpr hq) hδ

end ThesisCommon
