import ThesisCommon.Analysis.BoundedProductRetractions

/-! Uniform bounded coordinate readings and actual factor maps on the full
bounded product. These maps do not rely on density of finite support. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {E F : ℕ → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

def boundedProductReadBound (n : ℕ → ℕ)
    (s : ∀ i, F (n i) →L[𝕜] E i) (C : ℝ) (hC : 0 ≤ C)
    (hs : ∀ i, ‖s i‖ ≤ C) : lp F ∞ →L[𝕜] lp E ∞ :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => s i (x (n i)), memℓp_infty ⟨C * ‖x‖, by
        rintro _ ⟨i, rfl⟩
        exact ((s i).le_opNorm _).trans (mul_le_mul (hs i)
          (lp.norm_apply_le_norm ENNReal.top_ne_zero x (n i)) (norm_nonneg _) hC)⟩⟩
      map_add' := by intros; apply lp.ext; funext i; exact map_add _ _ _
      map_smul' := by intros; apply lp.ext; funext i; exact map_smul _ _ _ }
    C (fun x => by
      apply lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg _))
      intro i
      exact ((s i).le_opNorm _).trans (mul_le_mul (hs i)
        (lp.norm_apply_le_norm ENNReal.top_ne_zero x (n i)) (norm_nonneg _) hC))

@[simp] theorem boundedProductReadBound_apply (n : ℕ → ℕ)
    (s : ∀ i, F (n i) →L[𝕜] E i) (C : ℝ) (hC : 0 ≤ C) (hs : ∀ i, ‖s i‖ ≤ C)
    (x : lp F ∞) (i : ℕ) : boundedProductReadBound n s C hC hs x i = s i (x (n i)) := rfl

theorem norm_boundedProductReadBound_le (n : ℕ → ℕ)
    (s : ∀ i, F (n i) →L[𝕜] E i) (C : ℝ) (hC : 0 ≤ C) (hs : ∀ i, ‖s i‖ ≤ C) :
    ‖boundedProductReadBound n s C hC hs‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

theorem boundedProduct_factorization_of_coordinate_factors
    (T : lp F ∞ →L[𝕜] lp F ∞) (n : ℕ → ℕ) (hn : Function.Injective n)
    (D : ∀ i, F (n i) →L[𝕜] F (n i))
    (hD : ∀ (x : lp F ∞) i, T x (n i) = D i (x (n i)))
    (r : ∀ i, E i →L[𝕜] F (n i)) (hr : ∀ i, ‖r i‖ ≤ 1)
    (s : ∀ i, F (n i) →L[𝕜] E i) (C : ℝ) (hC : 0 ≤ C) (hs : ∀ i, ‖s i‖ ≤ C)
    (h : ∀ i, ((s i).comp (D i)).comp (r i) = ContinuousLinearMap.id 𝕜 (E i)) :
    ∃ (U : lp F ∞ →L[𝕜] lp E ∞) (V : lp E ∞ →L[𝕜] lp F ∞),
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (lp E ∞) ∧ ‖U‖ * ‖V‖ ≤ C := by
  let U := boundedProductReadBound n s C hC hs
  let V := boundedProductInsert n r hr
  refine ⟨U, V, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    change s i (T (V x) (n i)) = x i
    rw [hD]
    change s i (D i (boundedProductInsert n r hr x (n i))) = x i
    rw [boundedProductInsert_apply_image n hn]
    exact DFunLike.congr_fun (h i) (x i)
  · exact (mul_le_mul_of_nonneg_right (norm_boundedProductReadBound_le n s C hC hs)
      (norm_nonneg V)).trans ((mul_le_mul_of_nonneg_left
        (norm_boundedProductInsert_le n r hr) hC).trans_eq (mul_one C))

end ThesisCommon
