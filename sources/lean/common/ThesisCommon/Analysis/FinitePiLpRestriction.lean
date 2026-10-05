import ThesisCommon.Analysis.JamesTreePartialTests

/-! Contractivity of genuine finite-coordinate restrictions, including empty
index sets and the infinite exponent. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem piLp_norm_restrict_embedding_le (p : BanachExponent)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ↪ κ)
    (a : PiLp p.val (fun _ : κ => 𝕜)) :
    ‖WithLp.toLp p.val (fun i => a (e i))‖ ≤ ‖a‖ := by
  classical
  rcases p with ⟨p, hp1⟩
  letI : Fact (1 ≤ p) := ⟨hp1⟩
  by_cases hp : p = ∞
  · subst p
    rw [← PiLp.norm_ofLp, ← PiLp.norm_ofLp]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      (fun i => norm_le_pi_norm (WithLp.ofLp a) (e i))
  · have hpr : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le hp1)) hp
    rw [PiLp.norm_eq_sum hpr, PiLp.norm_eq_sum hpr]
    apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _) _ (by positivity)
    change (∑ i, ‖a (e i)‖ ^ p.toReal) ≤ _
    rw [← Finset.sum_map Finset.univ e (fun i => ‖a i‖ ^ p.toReal)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Real.rpow_nonneg (norm_nonneg _) _)

end ThesisCommon
