import ThesisCommon.Analysis.GowersMaureyCoordinateSumBounds
import ThesisCommon.Analysis.GowersMaureyCoordinates

/-! Singleton interval tests give genuine finite coordinate lower bounds,
also on the Banach completion. Together with Lemma 7 they give the exact
norm of sums of separated coordinate unit vectors at the good sizes. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem restrict_singleton_interval (k : ℕ) (x : C00 𝕜) :
    restrict ⟨k, k⟩ x = Finsupp.single k (x k) := by
  ext n
  simp only [restrict_apply, Interval.set, Finset.Icc_self, Finset.mem_singleton,
    Finsupp.single_apply]
  split_ifs with h h <;> simp_all

theorem coordinate_sum_norm_le_weight (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 2 ≤ N) {a : Fin N → ℕ} (ha : StrictMono a) (x : C00 𝕜) :
    (∑ i, ‖x (a i)‖) ≤ logarithmicWeight N * implicitNorm D x := by
  let T : IntervalTest := {
    count := N
    count_ge_two := hN
    interval := fun i => ⟨a i, a i⟩
    successive := by
      intro i j hij s hs t ht
      simp only [Interval.set, Finset.Icc_self, Finset.mem_singleton] at hs ht
      simpa only [hs, ht] using ha hij
  }
  have hh := implicitNorm_intervalAverage_le D T x
  change (logarithmicWeight N)⁻¹ * (∑ i, implicitNorm D (restrict ⟨a i, a i⟩ x)) ≤ _ at hh
  simp only [restrict_singleton_interval, implicitNorm_single] at hh
  have hf : 0 < logarithmicWeight N := zero_lt_one.trans_le (one_le_logarithmicWeight (by omega))
  have hb := mul_le_mul_of_nonneg_left hh hf.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hf.ne', one_mul] using hb

theorem completedCoordinate_sum_norm_le_weight (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 2 ≤ N) {a : Fin N → ℕ} (ha : StrictMono a) (x : ShiftSpace D) :
    (∑ i, ‖completedCoordinate D (a i) x‖) ≤ logarithmicWeight N * ‖x‖ := by
  refine (denseEmbedding_denseRange D).induction_on x ?_ ?_
  · exact isClosed_le (continuous_finset_sum _ (fun i _ => (completedCoordinate D (a i)).continuous.norm))
      (continuous_const.mul continuous_norm)
  · intro y
    simp only [completedCoordinate_denseEmbedding, denseEmbedding_norm]
    exact coordinate_sum_norm_le_weight D hN ha y

theorem basisVector_sum_norm_le_div_weight (D : ConstructionData 𝕜)
    {N : ℕ} {a : Fin N → ℕ} (ha : StrictMono a) (m : ℕ)
    (hN : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2 * m + 1) : ℝ))
      (Real.exp (D.j (2 * m + 1) : ℝ))) :
    ‖∑ i, basisVector D (a i)‖ ≤ (N : ℝ) / logarithmicWeight N := by
  simp only [basisVector, ← map_sum, denseEmbedding_norm]
  exact single_sum_norm_le_div_weight D ha m hN

theorem single_sum_norm_eq_div_weight (D : ConstructionData 𝕜)
    {N : ℕ} {a : Fin N → ℕ} (ha : StrictMono a) (m : ℕ)
    (hN : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2 * m + 1) : ℝ))
      (Real.exp (D.j (2 * m + 1) : ℝ))) :
    implicitNorm D (∑ i, Finsupp.single (a i) (1 : 𝕜)) =
      (N : ℝ) / logarithmicWeight N := by
  apply le_antisymm (single_sum_norm_le_div_weight D ha m hN)
  have hnR : 2 ≤ (N : ℝ) := by have hh := D.log_size_large (2*m+1); linarith [hN.1]
  have hn : 2 ≤ N := by exact_mod_cast hnR
  have hf : 0 < logarithmicWeight N := zero_lt_one.trans_le (one_le_logarithmicWeight (by omega))
  have hh := coordinate_sum_norm_le_weight D hn ha (∑ i, Finsupp.single (a i) (1 : 𝕜))
  have hv : ∀ i : Fin N, (∑ j, Finsupp.single (a j) (1 : 𝕜)) (a i) = 1 := by
    intro i
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      exact Finsupp.single_eq_of_ne (Ne.symm (ha.injective.ne hji))
    · simp
  simp only [hv, norm_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hh
  exact (div_le_iff₀ hf).mpr (by simpa only [mul_comm] using hh)

end ThesisCommon.GowersMaurey
