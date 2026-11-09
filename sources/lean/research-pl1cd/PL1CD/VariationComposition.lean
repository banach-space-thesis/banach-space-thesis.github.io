import PL1CD.Variation
import PL1.Definitions

noncomputable section
open Filter
open scoped BigOperators Topology NNReal ENNReal

namespace PL1CD.Variation

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem averageSeminorm_compare (p : ℕ → Seminorm 𝕜 E) (q : ℕ → Seminorm 𝕜 F)
    (N : ℕ) (x : E) (y : F) (c : ℝ) (h : ∀ n, p n x ≤ c * q n y) :
    averageSeminorm p N x ≤ c * averageSeminorm q N y := by
  rw [averageSeminorm_apply, averageSeminorm_apply]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, c * q n y :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => h n))
        (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem averageSeminorm_compare_lower (p : ℕ → Seminorm 𝕜 E) (q : ℕ → Seminorm 𝕜 F)
    (N : ℕ) (x : E) (y : F) (c : ℝ) (h : ∀ n, c * p n x ≤ q n y) :
    c * averageSeminorm p N x ≤ averageSeminorm q N y := by
  rw [averageSeminorm_apply, averageSeminorm_apply]
  calc
    _ = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, c * p n x := by
      rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => h n))
      (inv_nonneg.mpr (Nat.cast_nonneg N))

theorem levelSeminorm_comp_le (M : ℕ → ℕ) (n : ℕ)
    (T : HaarL1 𝕜 →L[𝕜] E) (W : E →L[𝕜] F) :
    levelSeminorm 𝕜 F M n (W.comp T) ≤ ‖W‖ * levelSeminorm 𝕜 E M n T :=
  finiteVariation_comp_le _ _ T W

theorem levelSeminorm_comp_ge (M : ℕ → ℕ) (n : ℕ)
    (T : HaarL1 𝕜 →L[𝕜] E) (W : E →L[𝕜] F) (c : ℝ)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖W x‖) :
    c * levelSeminorm 𝕜 E M n T ≤ levelSeminorm 𝕜 F M n (W.comp T) :=
  finiteVariation_comp_ge _ _ T W c hlower

theorem endpointSeminorm_comp_le (M N : ℕ → ℕ) (s : ℕ)
    (T : HaarL1 𝕜 →L[𝕜] E) (W : E →L[𝕜] F) :
    endpointSeminorm 𝕜 F M N s (W.comp T) ≤ ‖W‖ * endpointSeminorm 𝕜 E M N s T :=
  averageSeminorm_compare _ _ (N s) _ _ _ (fun n => levelSeminorm_comp_le M n T W)

theorem endpointSeminorm_comp_ge (M N : ℕ → ℕ) (s : ℕ)
    (T : HaarL1 𝕜 →L[𝕜] E) (W : E →L[𝕜] F) (c : ℝ)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖W x‖) :
    c * endpointSeminorm 𝕜 E M N s T ≤ endpointSeminorm 𝕜 F M N s (W.comp T) :=
  averageSeminorm_compare_lower _ _ (N s) _ _ _
    (fun n => levelSeminorm_comp_ge M n T W c hlower)

theorem averagedVariation_comp_le (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (T : HaarL1 𝕜 →L[𝕜] E) (W : E →L[𝕜] F) :
    averagedVariation 𝕜 F M N H hH (W.comp T) ≤
      ‖W‖ * averagedVariation 𝕜 E M N H hH T := by
  let := alongInfinite_neBot hH
  exact PL1CD.limsupSeminorm_compare (endpointSeminorm 𝕜 F M N) 2
    (endpointSeminorm_le 𝕜 F M N) (atTop ⊓ 𝓟 H)
    (endpointSeminorm 𝕜 E M N) 2 (endpointSeminorm_le 𝕜 E M N)
    (W.comp T) T (norm_nonneg W) (fun s => endpointSeminorm_comp_le M N s T W)

theorem averagedVariation_comp_ge (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (T : HaarL1 𝕜 →L[𝕜] E) (W : E →L[𝕜] F) (c : ℝ) (hc : 0 ≤ c)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖W x‖) :
    c * averagedVariation 𝕜 E M N H hH T ≤
      averagedVariation 𝕜 F M N H hH (W.comp T) := by
  let := alongInfinite_neBot hH
  exact PL1CD.limsupSeminorm_compare_lower (endpointSeminorm 𝕜 E M N) 2
    (endpointSeminorm_le 𝕜 E M N) (atTop ⊓ 𝓟 H)
    (endpointSeminorm 𝕜 F M N) 2 (endpointSeminorm_le 𝕜 F M N)
    T (W.comp T) hc (fun s => endpointSeminorm_comp_ge M N s T W c hlower)

theorem not_containsIsomorphicCopy_of_variation (M N : ℕ → ℕ)
    (H : Set ℕ) (hH : H.Infinite) (T : HaarL1 𝕜 →L[𝕜] E)
    (hpositive : 0 < averagedVariation 𝕜 E M N H hH T)
    (hvanish : ∀ U : HaarL1 𝕜 →L[𝕜] F, averagedVariation 𝕜 F M N H hH U = 0) :
    ¬ PL1.ContainsIsomorphicCopy 𝕜 E F := by
  rintro ⟨V, _hclosed, ⟨e⟩⟩
  let S : E →L[𝕜] F := V.subtypeL.comp e.toContinuousLinearMap
  let A : ℝ := ‖e.symm.toContinuousLinearMap‖
  let c : ℝ := (A + 1)⁻¹
  have hA : 0 < A + 1 := by dsimp [A]; positivity
  have hc : 0 < c := inv_pos.mpr hA
  have hinverse (x : E) : ‖x‖ ≤ A * ‖S x‖ := by
    have h := e.symm.toContinuousLinearMap.le_opNorm (e x)
    simpa [A, S] using h
  have hlower (x : E) : c * ‖x‖ ≤ ‖S x‖ := by
    dsimp [c]
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ hA).mpr
    nlinarith [hinverse x, norm_nonneg (S x)]
  have h := averagedVariation_comp_ge M N H hH T S c hc.le hlower
  rw [hvanish] at h
  have hstrict := mul_pos hc hpositive
  linarith

end PL1CD.Variation
