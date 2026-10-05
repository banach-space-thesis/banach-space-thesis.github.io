import ThesisCommon.Analysis.GowersMaureyCoordinateSumBounds

/-! Sharp interval-norm estimates for fixed coordinate sums, obtained
from actual RIS estimates by letting their auxiliary epsilon decrease
to zero. The interval order and the logarithmic scaling error are fixed. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem normalized_intervalNorm_le_one_add_of_all_intervalNorm_le_one
    (D : ConstructionData 𝕜) {N : ℕ} {x : Fin N → C00 𝕜}
    (hx : Successive x) (hbound : ∀ i n, 0 < n → intervalNorm D n (x i) ≤ 1)
    (m n : ℕ)
    (hratio : (N : ℝ) / n ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
      (Real.exp (D.j (2*m+1) : ℝ))) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : logarithmicWeight N ≤ (1+δ) * logarithmicWeight ((N : ℝ)/n)) :
    intervalNorm D n ((logarithmicWeight N / N) • (∑ i, x i)) ≤ 1+δ := by
  apply le_of_forall_pos_le_add
  intro t ht
  let ε := min 1 (t / (3*(1+δ)))
  have hc : 0 < 3*(1+δ) := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (div_pos ht hc)
  obtain ⟨h⟩ := isRIS_of_all_intervalNorm_le_one D hx hbound hε (min_le_left _ _)
  have hh := h.normalized_intervalNorm_le_lemma7 m n hratio hδ hf
  have heps : ε * (3*(1+δ)) ≤ t := (le_div_iff₀ hc).mp (min_le_right _ _)
  exact hh.trans (by nlinarith)

theorem normalized_single_sum_intervalNorm_le_one_add (D : ConstructionData 𝕜)
    {N : ℕ} {a : Fin N → ℕ} (ha : StrictMono a) (m n : ℕ)
    (hratio : (N : ℝ) / n ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
      (Real.exp (D.j (2*m+1) : ℝ))) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : logarithmicWeight N ≤ (1+δ) * logarithmicWeight ((N : ℝ)/n)) :
    intervalNorm D n ((logarithmicWeight N / N) •
      (∑ i, Finsupp.single (a i) (1 : 𝕜))) ≤ 1+δ := by
  apply normalized_intervalNorm_le_one_add_of_all_intervalNorm_le_one D ?_ ?_ m n hratio hδ hf
  · intro i j hij s hs t ht
    simp only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hs ht
    simpa only [hs, ht] using ha hij
  · intro i k _
    simpa only [norm_one] using intervalNorm_single_le D k (a i) (1 : 𝕜)

end ThesisCommon.GowersMaurey
