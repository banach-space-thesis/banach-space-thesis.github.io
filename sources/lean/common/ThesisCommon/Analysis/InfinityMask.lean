import ThesisCommon.Analysis.InfinityScalarRows

/-! Coordinate masks on the actual sup-norm space, and invariance under
finite-coordinate removal for functionals annihilating the unit vectors.
-/
noncomputable section
open scoped Classical BigOperators ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def infinityMask (M : Set ℕ) : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞ :=
  LinearMap.mkContinuous {
    toFun := fun x => ⟨fun n => if n ∈ M then x n else 0,
      memℓp_infty ⟨‖x‖, by
        rintro _ ⟨n, rfl⟩
        dsimp only
        split_ifs
        · exact lp.norm_apply_le_norm ENNReal.top_ne_zero x n
        · simpa only [norm_zero] using norm_nonneg x⟩⟩
    map_add' := by
      intro x y
      ext n
      change (if n ∈ M then x n + y n else 0) =
        (if n ∈ M then x n else 0) + (if n ∈ M then y n else 0)
      split_ifs <;> simp
    map_smul' := by
      intro a x
      ext n
      change (if n ∈ M then a * x n else 0) = a * (if n ∈ M then x n else 0)
      split_ifs <;> simp }
    1 (fun x => by
      rw [one_mul]
      apply lp.norm_le_of_forall_le (norm_nonneg _)
      intro n
      change ‖if n ∈ M then x n else 0‖ ≤ ‖x‖
      split_ifs
      · exact lp.norm_apply_le_norm ENNReal.top_ne_zero x n
      · simpa only [norm_zero] using norm_nonneg x)

@[simp] theorem infinityMask_apply (M : Set ℕ) (x : lp (fun _ : ℕ => 𝕜) ∞) (n : ℕ) :
    infinityMask M x n = if n ∈ M then x n else 0 := rfl

theorem norm_infinityMask_apply_le (M : Set ℕ) (x : lp (fun _ : ℕ => 𝕜) ∞) :
    ‖infinityMask M x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg x)
  intro n
  rw [infinityMask_apply]
  split_ifs
  · exact lp.norm_apply_le_norm ENNReal.top_ne_zero x n
  · simpa only [norm_zero] using norm_nonneg x

theorem infinityMask_compl_finset (F : Finset ℕ) (x : lp (fun _ : ℕ => 𝕜) ∞) :
    infinityMask (F : Set ℕ)ᶜ x = x - ∑ n ∈ F, x n • lp.single ∞ n (1 : 𝕜) := by
  ext m
  have hsum : (∑ n ∈ F, x n • (lp.single ∞ n (1 : 𝕜) : lp (fun _ : ℕ => 𝕜) ∞)) m =
      if m ∈ F then x m else 0 := by
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      lp.single_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  rw [infinityMask_apply, lp.coeFn_sub, Pi.sub_apply, hsum]
  by_cases hm : m ∈ F <;> simp [hm]

theorem infinity_functional_remove_finite
    (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜)
    (hφ : ∀ n, φ (lp.single ∞ n (1 : 𝕜)) = 0)
    (F : Finset ℕ) (x : lp (fun _ : ℕ => 𝕜) ∞) :
    φ (infinityMask (F : Set ℕ)ᶜ x) = φ x := by
  rw [infinityMask_compl_finset]
  simp only [map_sub, map_sum, map_smul, hφ, smul_zero, Finset.sum_const_zero, sub_zero]

end ThesisCommon

