import JLMS.BlockStabilization

/-! # Scalar normalization of the stabilized dual radius -/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem dualEventualBound_smul (f : ℕ → (X →L[𝕜] 𝕜)) {r : ℝ}
    (hf : DualEventualBound f r) (a : 𝕜) :
    DualEventualBound (fun n => a • f n) (‖a‖ * r) := by
  intro x ε hε
  let η := ε / (‖a‖ + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  filter_upwards [hf x η hη] with n hn
  simp only [ContinuousLinearMap.smul_apply, norm_smul]
  calc
    ‖a‖ * ‖f n x‖ ≤ ‖a‖ * ((r + η) * ‖x‖) :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg a)
    _ ≤ (‖a‖ * r + ε) * ‖x‖ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      have hη' : ‖a‖ * η ≤ ε := by
        calc
          _ ≤ (‖a‖ + 1) * η := mul_le_mul_of_nonneg_right (by linarith) hη.le
          _ = ε := by dsimp [η]; field_simp
      nlinarith

theorem NormalizedBlockSystem.applyDual_smul (b : NormalizedBlockSystem 𝕜)
    (f : ℕ → (X →L[𝕜] 𝕜)) (a : 𝕜) (n : ℕ) :
    b.applyDual (fun k => a • f k) n = a • b.applyDual f n := by
  change (∑ k ∈ b.support n, b.coefficient n k • (a • f k)) =
    a • (∑ k ∈ b.support n, b.coefficient n k • f k)
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun k _ => smul_comm _ _ _)

theorem dualAsymptoticRadius_smul (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (a : 𝕜) :
    dualAsymptoticRadius (fun n => a • f n) = ‖a‖ * dualAsymptoticRadius f := by
  have hbound (a : 𝕜) (n : ℕ) : ‖a • f n‖ ≤ ‖a‖ * C := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hf n) (norm_nonneg a)
  have hup := dualAsymptoticRadius_le _
    (mul_nonneg (norm_nonneg a) (dualAsymptoticRadius_nonneg f hC hf))
    (dualEventualBound_smul f (dualAsymptoticRadius_eventualBound f hC hf) a)
  apply le_antisymm hup
  by_cases ha : a = 0
  · subst a
    simpa using dualAsymptoticRadius_nonneg (fun n => (0 : 𝕜) • f n)
      (mul_nonneg (norm_nonneg (0 : 𝕜)) hC) (hbound 0)
  · have hinv := dualAsymptoticRadius_le _
      (mul_nonneg (norm_nonneg a⁻¹)
        (dualAsymptoticRadius_nonneg _ (mul_nonneg (norm_nonneg a) hC) (hbound a)))
      (dualEventualBound_smul (fun n => a • f n)
        (dualAsymptoticRadius_eventualBound _ (mul_nonneg (norm_nonneg a) hC) (hbound a)) a⁻¹)
    simp only [smul_smul, inv_mul_cancel₀ ha, one_smul, norm_inv] at hinv
    have hh := mul_le_mul_of_nonneg_left hinv (norm_nonneg a)
    simpa only [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_mul] using hh

end JLMS
