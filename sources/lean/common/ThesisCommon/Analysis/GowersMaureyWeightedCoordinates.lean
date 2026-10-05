import ThesisCommon.Analysis.GowersMaureyCoordinateLowerBounds

/-! The sharp coordinate-sum estimate also holds for arbitrary scalar
coefficients in the unit disk. Phase alignment therefore bounds the sum
of the absolute values of a genuine bounded functional on these vectors. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem successive_weighted_single {N : ℕ} {a : Fin N → ℕ} (ha : StrictMono a)
    (c : Fin N → 𝕜) : Successive (fun i => Finsupp.single (a i) (c i)) := by
  intro i j hij s hs t ht
  have hs' : s = a i := Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
  have ht' : t = a j := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  simpa only [hs', ht'] using ha hij

theorem weighted_single_sum_norm_le_div_weight (D : ConstructionData 𝕜)
    {N : ℕ} {a : Fin N → ℕ} (ha : StrictMono a) (c : Fin N → 𝕜)
    (hc : ∀ i, ‖c i‖ ≤ 1) (m : ℕ)
    (hN : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
      (Real.exp (D.j (2*m+1) : ℝ))) :
    implicitNorm D (∑ i, Finsupp.single (a i) (c i)) ≤ (N : ℝ) / logarithmicWeight N := by
  have hh := normalized_norm_le_one_of_all_intervalNorm_le_one D
    (successive_weighted_single ha c)
    (fun i n _ => (intervalNorm_single_le D n (a i) (c i)).trans (hc i)) m hN
  have hlog := D.log_size_large (2*m+1)
  have hNr : 0 < (N : ℝ) := by linarith [hN.1]
  have hN1 : 1 ≤ (N : ℝ) := by linarith [hN.1]
  have hfp := zero_lt_one.trans_le (one_le_logarithmicWeight_real hN1)
  rw [seminorm_real_smul, abs_of_nonneg (div_nonneg hfp.le hNr.le)] at hh
  apply (le_div_iff₀ hfp).mpr
  have heq : logarithmicWeight N / N * implicitNorm D (∑ i, Finsupp.single (a i) (c i)) =
      (implicitNorm D (∑ i, Finsupp.single (a i) (c i)) * logarithmicWeight N) / N := by ring
  rw [heq] at hh
  exact (div_le_one hNr).mp hh

theorem weighted_basisVector_sum_norm_le_div_weight (D : ConstructionData 𝕜)
    {N : ℕ} {a : Fin N → ℕ} (ha : StrictMono a) (c : Fin N → 𝕜)
    (hc : ∀ i, ‖c i‖ ≤ 1) (m : ℕ)
    (hN : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
      (Real.exp (D.j (2*m+1) : ℝ))) :
    ‖∑ i, c i • basisVector D (a i)‖ ≤ (N : ℝ) / logarithmicWeight N := by
  have he : (∑ i, c i • basisVector D (a i)) =
      denseEmbedding D (∑ i, Finsupp.single (a i) (c i)) := by
    simp only [basisVector, ← map_smul, ← map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change c i • Finsupp.single (a i) (1 : 𝕜) = Finsupp.single (a i) (c i)
    simp
  rw [he, denseEmbedding_norm]
  exact weighted_single_sum_norm_le_div_weight D ha c hc m hN

theorem functional_basisVector_sum_norm_le (D : ConstructionData 𝕜)
    (φ : ShiftSpace D →L[𝕜] 𝕜) {N : ℕ} {a : Fin N → ℕ}
    (ha : StrictMono a) (m : ℕ)
    (hN : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
      (Real.exp (D.j (2*m+1) : ℝ))) :
    (∑ i, ‖φ (basisVector D (a i))‖) ≤ ‖φ‖ * ((N : ℝ) / logarithmicWeight N) := by
  choose c hc hp using fun i => RCLike.exists_norm_eq_mul_self (φ (basisVector D (a i)))
  have he : φ (∑ i, c i • basisVector D (a i)) =
      ((∑ i, ‖φ (basisVector D (a i))‖ : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => (hp i).symm)
  calc
    _ = ‖φ (∑ i, c i • basisVector D (a i))‖ := by
      rw [he, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    _ ≤ ‖φ‖ * ‖∑ i, c i • basisVector D (a i)‖ := φ.le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (weighted_basisVector_sum_norm_le_div_weight D ha c (fun i => (hc i).le) m hN)
      (norm_nonneg _)

end ThesisCommon.GowersMaurey
