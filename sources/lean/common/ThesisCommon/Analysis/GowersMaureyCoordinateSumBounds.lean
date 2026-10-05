import ThesisCommon.Analysis.GowersMaureyFixedRIS
import ThesisCommon.Analysis.GowersMaureyRISLemmaSeven

/-! Sharp bounds for fixed successive vectors having all interval norms
at most one, in particular coordinate unit vectors. Letting the RIS
parameter tend to zero removes the auxiliary error; this is the first
coordinate-vector estimate used in the source's Laurent-operator lemma. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem normalized_norm_le_one_of_all_intervalNorm_le_one
    (D : ConstructionData 𝕜) {N : ℕ} {x : Fin N → C00 𝕜}
    (hx : Successive x) (hbound : ∀ i n, 0 < n → intervalNorm D n (x i) ≤ 1)
    (m : ℕ) (hN : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2 * m + 1) : ℝ))
      (Real.exp (D.j (2 * m + 1) : ℝ))) :
    implicitNorm D ((logarithmicWeight N / N) • (∑ i, x i)) ≤ 1 := by
  apply le_of_forall_pos_le_add
  intro t ht
  let ε := min 1 (t / 3)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  obtain ⟨h⟩ := isRIS_of_all_intervalNorm_le_one D hx hbound hε hε1
  have hh := h.normalized_norm_le_lemma7 m hN
  have heps : ε ≤ t / 3 := min_le_right _ _
  exact hh.trans (by linarith)

theorem normalized_single_sum_norm_le_one (D : ConstructionData 𝕜)
    {N : ℕ} {a : Fin N → ℕ} (ha : StrictMono a) (m : ℕ)
    (hN : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2 * m + 1) : ℝ))
      (Real.exp (D.j (2 * m + 1) : ℝ))) :
    implicitNorm D ((logarithmicWeight N / N) •
      (∑ i, Finsupp.single (a i) (1 : 𝕜))) ≤ 1 := by
  apply le_of_forall_pos_le_add
  intro t ht
  let ε := min 1 (t / 3)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨h⟩ := isRIS_single D ha hε (min_le_left _ _)
  have hh := h.normalized_norm_le_lemma7 m hN
  have heps : ε ≤ t / 3 := min_le_right _ _
  exact hh.trans (by linarith)

theorem single_sum_norm_le_div_weight (D : ConstructionData 𝕜)
    {N : ℕ} {a : Fin N → ℕ} (ha : StrictMono a) (m : ℕ)
    (hN : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2 * m + 1) : ℝ))
      (Real.exp (D.j (2 * m + 1) : ℝ))) :
    implicitNorm D (∑ i, Finsupp.single (a i) (1 : 𝕜)) ≤
      (N : ℝ) / logarithmicWeight N := by
  have hlog := D.log_size_large (2 * m + 1)
  have hNr : 0 < (N : ℝ) := by linarith [hN.1]
  have hN1 : 1 ≤ (N : ℝ) := by linarith [hN.1]
  have hfp := zero_lt_one.trans_le (one_le_logarithmicWeight_real hN1)
  have hh := normalized_single_sum_norm_le_one D ha m hN
  rw [seminorm_real_smul, abs_of_nonneg (div_nonneg hfp.le hNr.le)] at hh
  apply (le_div_iff₀ hfp).mpr
  have heq : logarithmicWeight N / N * implicitNorm D (∑ i, Finsupp.single (a i) (1 : 𝕜)) =
      (implicitNorm D (∑ i, Finsupp.single (a i) (1 : 𝕜)) * logarithmicWeight N) / N := by ring
  rw [heq] at hh
  exact (div_le_one hNr).mp hh

end ThesisCommon.GowersMaurey
