import ThesisCommon.Analysis.JamesTreeAntichainCopies
import ThesisCommon.Analysis.JamesTreeFiniteLevels
import ThesisCommon.Analysis.SchurFamilySupport
import ThesisCommon.Analysis.MatrixPowerGrowth

/-! For 1 < p < infinity, an actual antichain of canonical tree vectors is
weakly null. Every fixed finite-level part of an operator image consequently
converges to zero in norm. Both concrete segment conventions are covered. -/
noncomputable section
open Filter Topology
open scoped BigOperators ENNReal
namespace ThesisCommon
variable {𝕜 Γ : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTree_antichain_unit_sum_bound {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S)
    (hp : 0 < p.val.toReal) (a : Fin n → 𝕜) (ha : ∀ i, ‖a i‖ ≤ 1) :
    ‖∑ i, a i • jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S) (e i)‖ ≤
      (n : ℝ) ^ (1 / p.val.toReal) := by
  have hfin : p.val ≠ ∞ := by
    intro h
    rw [h, ENNReal.toReal_top] at hp
    exact lt_irrefl _ hp
  rw [jamesTree_antichain_norm_finite e he hS hfin a]
  apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (norm_nonneg _) _) _ (by positivity)
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) ^ p.val.toReal :=
      Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (norm_nonneg _) (ha i) hp.le)
    _ = n := by simp

theorem jamesTree_antichain_functional_tendsto (e : Γ ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S)
    (hp : 1 < p.val.toReal) (φ : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] 𝕜) :
    Tendsto (fun γ => φ (jamesTreeUnit (e γ))) cofinite (𝓝 0) := by
  apply functional_tendsto_zero_of_sublinear_sums
    (fun γ => jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S) (e γ))
    (fun n => (n : ℝ) ^ (1 / p.val.toReal))
  · intro n f a ha
    exact jamesTree_antichain_unit_sum_bound (f.trans e)
      (fun i j hij => he (f i) (f j) (f.injective.ne hij)) hS
      (zero_lt_one.trans hp) a ha
  · intro M _ ε hε
    have hr : 1 / p.val.toReal < 1 := (div_lt_one (zero_lt_one.trans hp)).mpr hp
    obtain ⟨n, _, hn, _⟩ := exists_nat_two_sublinear_powers
      (1 / p.val.toReal) (1 / p.val.toReal) M hr hr hε
    exact ⟨n, by simpa only [mul_comm ε] using hn⟩

theorem jamesTree_antichain_level_image_tendsto (e : Γ ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S)
    (hp : 1 < p.val.toReal)
    (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (N : ℕ) (hN : JamesTreeMaskClosed S (dyadicInitialLevels N)) :
    Tendsto (fun γ => jamesTreeMask (dyadicInitialLevels N) hN (T (jamesTreeUnit (e γ))))
      cofinite (𝓝 0) := by
  have hc (t : DyadicTreeNode) :
      Tendsto (fun γ => jamesTreeCoordinate t (T (jamesTreeUnit (e γ)))) cofinite (𝓝 0) :=
    jamesTree_antichain_functional_tendsto e he hS hp ((jamesTreeCoordinate t).comp T)
  have h := tendsto_finset_sum (dyadicInitialFinset N) (fun t _ =>
    (hc t).smul_const (jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S) t))
  simpa only [zero_smul, Finset.sum_const_zero, ← jamesTreeLevelProjection_finite_sum N hN] using h

theorem literalJamesTree_antichain_level_image_tendsto (e : Γ ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hp : 1 < p.val.toReal)
    (T : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p) (N : ℕ) :
    Tendsto (fun γ => literalJamesTreeLevelProjection p N (T (jamesTreeUnit (e γ))))
      cofinite (𝓝 0) :=
  jamesTree_antichain_level_image_tendsto e he literalJamesTreeSegmentsAreChains hp T N
    (literalJamesTreeMaskClosed_levels N)

theorem consecutiveJamesTree_antichain_level_image_tendsto (e : Γ ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hp : 1 < p.val.toReal)
    (T : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p) (N : ℕ) :
    Tendsto (fun γ => consecutiveJamesTreeLevelProjection p N (T (jamesTreeUnit (e γ))))
      cofinite (𝓝 0) :=
  jamesTree_antichain_level_image_tendsto e he consecutiveJamesTreeSegmentsAreChains hp T N
    (consecutiveJamesTreeMaskClosed_levels N)

end ThesisCommon
