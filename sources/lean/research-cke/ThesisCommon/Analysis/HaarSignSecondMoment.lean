import ThesisCommon.Analysis.GrothendieckMoments

/-! Exact finite-sign second moments and simultaneous small-value selection.
These are the random-sign estimates in the Haar block construction. The
statements include complex scalars; expectations are explicit finite sums. -/

noncomputable section
open scoped BigOperators
namespace ThesisCommon
open Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem haar_sign_second_moment {n : ℕ} (a : Fin n → 𝕜) :
    mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (a i)‖ ^ 2) =
      ∑ i, ‖a i‖ ^ 2 := by
  have hparts (θ : Fin n → Bool) :
      ‖∑ i, signedValue (θ i) (a i)‖ ^ 2 =
        rademacher (fun i => RCLike.re (a i)) θ ^ 2 +
        rademacher (fun i => RCLike.im (a i)) θ ^ 2 := by
    rw [RCLike.norm_sq_eq_def]
    have hre : RCLike.re (∑ i, signedValue (θ i) (a i)) =
        rademacher (fun i => RCLike.re (a i)) θ := by
      simp only [map_sum, rademacher]
      apply Finset.sum_congr rfl
      intro i _
      cases θ i <;> simp [signedValue]
    have him : RCLike.im (∑ i, signedValue (θ i) (a i)) =
        rademacher (fun i => RCLike.im (a i)) θ := by
      simp only [map_sum, rademacher]
      apply Finset.sum_congr rfl
      intro i _
      cases θ i <;> simp [signedValue]
    rw [hre, him]
    ring
  simp_rw [hparts]
  rw [mean_add, rademacher_second, rademacher_second, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.norm_sq_eq_def]
  ring

/-- The variance estimate uses both the largest atom and the total variation.
In the Haar application the largest atom tends to zero with the dyadic mesh. -/
theorem haar_sign_variance_le {n : ℕ} (a : Fin n → 𝕜) {d C : ℝ}
    (hd : 0 ≤ d) (ha : ∀ i, ‖a i‖ ≤ d) (hC : ∑ i, ‖a i‖ ≤ C) :
    (∑ i, ‖a i‖ ^ 2) ≤ d * C := by
  calc
    _ ≤ ∑ i, d * ‖a i‖ := Finset.sum_le_sum fun i _ => by
      nlinarith [norm_nonneg (a i), ha i]
    _ = d * ∑ i, ‖a i‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ d * C := mul_le_mul_of_nonneg_left hC hd

/-- One sign choice meets finitely many complex-valued constraints whenever
the sum of their exact variances is small enough. -/
theorem haar_sign_simultaneous_small {m n : ℕ} (a : Fin m → Fin n → 𝕜)
    {ε : ℝ} (hε : 0 < ε) (hsmall : (∑ r, ∑ i, ‖a r i‖ ^ 2) < ε ^ 2) :
    ∃ θ : Fin n → Bool, ∀ r, ‖∑ i, signedValue (θ i) (a r i)‖ < ε := by
  have hex : ∃ θ : Fin n → Bool,
      (∑ r, ‖∑ i, signedValue (θ i) (a r i)‖ ^ 2) < ε ^ 2 := by
    by_contra h
    push_neg at h
    have havg := mean_mono h
    rw [mean_const, mean_sum] at havg
    simp_rw [haar_sign_second_moment] at havg
    linarith
  obtain ⟨θ, hθ⟩ := hex
  refine ⟨θ, fun r => ?_⟩
  have hr : ‖∑ i, signedValue (θ i) (a r i)‖ ^ 2 ≤
      ∑ s, ‖∑ i, signedValue (θ i) (a s i)‖ ^ 2 :=
    Finset.single_le_sum
      (f := fun s : Fin m => ‖∑ i, signedValue (θ i) (a s i)‖ ^ 2)
      (fun s _ => sq_nonneg _) (Finset.mem_univ r)
  nlinarith [norm_nonneg (∑ i, signedValue (θ i) (a r i))]

end ThesisCommon
