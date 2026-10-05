import ThesisCommon.Analysis.MixedInfinityAtomicPart

/-! The almost-disjoint support restriction for the genuine mixed space.
All coordinate residuals on all source fibres form one countable family.
Their common support extends from finite outer sums by norm convergence. -/
noncomputable section
open Filter Topology
open scoped BigOperators ENNReal
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

theorem norm_infinityCoordinate_le (i j : ℕ) :
    ‖infinityCoordinate (b := b) (hb := hb) i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (x i) j).trans
    (by simpa only [one_mul] using norm_apply_le x i)

theorem infinity_weighted_entries_bound
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞))
    (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (i j : ℕ) :
    Summable (fun p : ℕ × ℕ => ‖x p.1 p.2 * infinityEntry T i j p.1 p.2‖) ∧
      (∑' p : ℕ × ℕ, ‖x p.1 p.2 * infinityEntry T i j p.1 p.2‖) ≤ ‖T‖ * ‖x‖ := by
  let φ := (infinityCoordinate (b := b) (hb := hb) i j).comp T
  have hφ : ‖φ‖ ≤ ‖T‖ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right (norm_infinityCoordinate_le i j) (norm_nonneg T)).trans_eq
      (one_mul _))
  exact ⟨infinity_weighted_norm_summable φ x,
    (infinity_weighted_tsum_norm_le φ x).trans
      (mul_le_mul_of_nonneg_right hφ (norm_nonneg x))⟩

theorem infinity_matrix_restriction
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞))
    {A : Set ℕ} (hA : A.Infinite) :
    ∃ M : Set ℕ, M ⊆ A ∧ M.Infinite ∧
      ∀ (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)),
        (∀ r s, s ∉ M → x r s = 0) → ∀ i j,
        HasSum (fun p : ℕ × ℕ => x p.1 p.2 * infinityEntry T i j p.1 p.2) (T x i j) := by
  let φ := fun k => (infinityCoordinate (b := b) (hb := hb)
    (Nat.unpair k).1 (Nat.unpair k).2).comp T
  let ψ := fun k => φ k - infinityMatrixFunctional (φ k)
  let χ := fun n => (ψ (Nat.unpair n).1).comp (singleL (Nat.unpair n).2)
  have hχ (n s : ℕ) : χ n (lp.single ∞ s (1 : 𝕜)) = 0 := by
    change φ (Nat.unpair n).1 (single (Nat.unpair n).2 (lp.single ∞ s (1 : 𝕜))) -
      infinityMatrixFunctional (φ (Nat.unpair n).1)
        (single (Nat.unpair n).2 (lp.single ∞ s (1 : 𝕜))) = 0
    rw [infinityMatrixFunctional_single, sub_self]
  obtain ⟨M, hMA, hM, hzero⟩ := ThesisCommon.infinity_common_annihilator χ hχ hA
  refine ⟨M, hMA, hM, ?_⟩
  intro x hx i j
  have hsingle (r : ℕ) : ψ (Nat.pair i j) (single r (x r)) = 0 := by
    have hh := hzero (Nat.pair (Nat.pair i j) r) (x r) (hx r)
    simpa only [χ, Nat.unpair_pair, ContinuousLinearMap.comp_apply, singleL_apply] using hh
  have hψ : ψ (Nat.pair i j) x = 0 := by
    have ht := ((ψ (Nat.pair i j)).continuous.tendsto x).comp (expansion x)
    apply tendsto_nhds_unique ht
    have heq : (fun N => ψ (Nat.pair i j)
        (∑ r ∈ Finset.range N, single r (x r))) = fun _ => (0 : 𝕜) := by
      funext N
      simp only [map_sum, hsingle, Finset.sum_const_zero]
    change Tendsto (fun N => ψ (Nat.pair i j)
      (∑ r ∈ Finset.range N, single r (x r))) atTop (𝓝 0)
    rw [heq]
    exact tendsto_const_nhds
  change φ (Nat.pair i j) x - infinityMatrixFunctional (φ (Nat.pair i j)) x = 0 at hψ
  rw [sub_eq_zero, infinityMatrixFunctional_apply] at hψ
  have heq : T x i j = ∑' p : ℕ × ℕ, x p.1 p.2 * infinityEntry T i j p.1 p.2 := by
    simpa only [φ, Nat.unpair_pair] using hψ
  rw [heq]
  exact (infinity_weighted_entries_bound T x i j).1.of_norm.hasSum

end SchauderSum
end ThesisCommon
