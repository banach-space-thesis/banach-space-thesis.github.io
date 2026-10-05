import ThesisCommon.Analysis.GowersMaureyActualRISProfile
import ThesisCommon.Analysis.GowersMaureyConstructionProfileGap

/-! The actual Lemma 7 estimate from Gowers--Maurey,
arXiv:math/9407209, printed p.9. The source's M in L is j_(2m+1)
with zero-based indexing. All profile and norming-form premises have
been proved for the concrete norm; the conclusion concerns every RIS.
The proof in fact needs only delta >= 0, not the printed delta < 1. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem RISData.normalized_intervalNorm_le_lemma7
    {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ} {x : Fin N → C00 𝕜}
    (h : RISData D ε x) (m n : ℕ)
    (hratio : (N : ℝ) / n ∈ Set.Icc (Real.log (D.j (2 * m + 1) : ℝ))
      (Real.exp (D.j (2 * m + 1) : ℝ)))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : logarithmicWeight N ≤ (1 + δ) * logarithmicWeight ((N : ℝ) / n)) :
    intervalNorm D n ((logarithmicWeight N / N) • (∑ i, x i)) ≤
      (1 + δ) * (1 + 3 * ε) := by
  have hlog := D.log_size_large (2 * m + 1)
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    simp only [hn0, Nat.cast_zero, div_zero] at hratio
    linarith [hratio.1]
  have hratio1 : 1 ≤ (N : ℝ) / n := by linarith [hratio.1]
  have hnN : n ≤ N := by
    have hh := (le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mp hratio1
    simpa only [one_mul, Nat.cast_le] using hh
  exact h.normalized_intervalNorm_le_of_interpolation_value hn hnN
    (D.interpolationProfile_eq_on_odd_gap m hratio) hδ hf

theorem IsRIS.normalized_intervalNorm_le_lemma7
    {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ} {x : Fin N → C00 𝕜}
    (h : IsRIS D ε x) (m n : ℕ)
    (hratio : (N : ℝ) / n ∈ Set.Icc (Real.log (D.j (2 * m + 1) : ℝ))
      (Real.exp (D.j (2 * m + 1) : ℝ)))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : logarithmicWeight N ≤ (1 + δ) * logarithmicWeight ((N : ℝ) / n)) :
    intervalNorm D n ((logarithmicWeight N / N) • (∑ i, x i)) ≤
      (1 + δ) * (1 + 3 * ε) := by
  obtain ⟨h⟩ := h
  exact h.normalized_intervalNorm_le_lemma7 m n hratio hδ hf

theorem RISData.normalized_norm_le_lemma7
    {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ} {x : Fin N → C00 𝕜}
    (h : RISData D ε x) (m : ℕ)
    (hN : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2 * m + 1) : ℝ))
      (Real.exp (D.j (2 * m + 1) : ℝ))) :
    implicitNorm D ((logarithmicWeight N / N) • (∑ i, x i)) ≤ 1 + 3 * ε := by
  have hh := h.normalized_intervalNorm_le_lemma7 m 1
    (by simpa only [Nat.cast_one, div_one] using hN) (δ := 0) (le_refl 0)
    (by simp)
  simpa only [intervalNorm_one, zero_add, one_mul, add_zero] using hh

end ThesisCommon.GowersMaurey
