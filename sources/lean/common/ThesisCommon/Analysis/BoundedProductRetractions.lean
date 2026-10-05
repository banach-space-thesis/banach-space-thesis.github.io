import ThesisCommon.Analysis.BoundedProductMasks

/-! Coordinatewise contractions and retractions on bounded products with
varying coefficient spaces. Every map acts on all bounded vectors. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {E F : ℕ → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

private theorem boundedProduct_norm_cast {i j : ℕ} (h : i = j) (y : F i) :
    ‖h ▸ y‖ = ‖y‖ := by cases h; rfl

private theorem boundedProduct_cast_add {i j : ℕ} (h : i = j) (x y : F i) :
    h ▸ (x + y) = (h ▸ x) + (h ▸ y) := by cases h; rfl

private theorem boundedProduct_cast_smul {i j : ℕ} (h : i = j) (a : 𝕜) (x : F i) :
    h ▸ (a • x) = a • (h ▸ x) := by cases h; rfl

private def boundedProductInsertValue (n : ℕ → ℕ)
    (r : ∀ i, E i →L[𝕜] F (n i)) (x : lp E ∞) (j : ℕ) : F j := by
  classical
  exact if h : j ∈ Set.range n then h.choose_spec ▸ r h.choose (x h.choose) else 0

private theorem boundedProductInsertValue_norm_le (n : ℕ → ℕ)
    (r : ∀ i, E i →L[𝕜] F (n i)) (hr : ∀ i, ‖r i‖ ≤ 1)
    (x : lp E ∞) (j : ℕ) : ‖boundedProductInsertValue n r x j‖ ≤ ‖x‖ := by
  classical
  unfold boundedProductInsertValue
  split_ifs with h
  · rw [boundedProduct_norm_cast]
    exact ((r h.choose).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (hr h.choose) (norm_nonneg _)).trans
        (by simpa only [one_mul] using lp.norm_apply_le_norm ENNReal.top_ne_zero x h.choose))
  · simpa only [norm_zero] using norm_nonneg x

def boundedProductInsert (n : ℕ → ℕ)
    (r : ∀ i, E i →L[𝕜] F (n i)) (hr : ∀ i, ‖r i‖ ≤ 1) : lp E ∞ →L[𝕜] lp F ∞ := by
  classical
  refine LinearMap.mkContinuous
    { toFun := fun x => ⟨boundedProductInsertValue n r x, memℓp_infty ⟨‖x‖, ?_⟩⟩
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · rintro _ ⟨j, rfl⟩
    exact boundedProductInsertValue_norm_le n r hr x j
  · intro x y
    apply lp.ext
    funext j
    change boundedProductInsertValue n r (x + y) j =
      boundedProductInsertValue n r x j + boundedProductInsertValue n r y j
    unfold boundedProductInsertValue
    split_ifs with h
    · simp only [lp.coeFn_add, Pi.add_apply, map_add, boundedProduct_cast_add]
    · exact (add_zero _).symm
  · intro a x
    apply lp.ext
    funext j
    change boundedProductInsertValue n r (a • x) j = a • boundedProductInsertValue n r x j
    unfold boundedProductInsertValue
    split_ifs with h
    · simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, boundedProduct_cast_smul]
    · exact (smul_zero a).symm
  · intro x
    rw [one_mul]
    exact lp.norm_le_of_forall_le (norm_nonneg x) (boundedProductInsertValue_norm_le n r hr x)

theorem norm_boundedProductInsert_le (n : ℕ → ℕ)
    (r : ∀ i, E i →L[𝕜] F (n i)) (hr : ∀ i, ‖r i‖ ≤ 1) :
    ‖boundedProductInsert n r hr‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem boundedProductInsert_apply_image (n : ℕ → ℕ) (hn : Function.Injective n)
    (r : ∀ i, E i →L[𝕜] F (n i)) (hr : ∀ i, ‖r i‖ ≤ 1)
    (x : lp E ∞) (i : ℕ) : boundedProductInsert n r hr x (n i) = r i (x i) := by
  classical
  change boundedProductInsertValue n r x (n i) = _
  unfold boundedProductInsertValue
  have hi : n i ∈ Set.range n := ⟨i, rfl⟩
  rw [dif_pos hi]
  have heq : hi.choose = i := hn hi.choose_spec
  have transport (a b : ℕ) (h : n a = n b) (hab : a = b) :
      h ▸ r a (x a) = r b (x b) := by subst b; rfl
  exact transport hi.choose i hi.choose_spec heq

theorem boundedProductInsert_apply_of_not_mem (n : ℕ → ℕ)
    (r : ∀ i, E i →L[𝕜] F (n i)) (hr : ∀ i, ‖r i‖ ≤ 1)
    (x : lp E ∞) (j : ℕ) (hj : j ∉ Set.range n) : boundedProductInsert n r hr x j = 0 := by
  classical
  exact dif_neg hj

def boundedProductRead (n : ℕ → ℕ)
    (s : ∀ i, F (n i) →L[𝕜] E i) (hs : ∀ i, ‖s i‖ ≤ 1) : lp F ∞ →L[𝕜] lp E ∞ :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => s i (x (n i)), memℓp_infty ⟨‖x‖, by
        rintro _ ⟨i, rfl⟩
        exact ((s i).le_opNorm _).trans
          ((mul_le_mul_of_nonneg_right (hs i) (norm_nonneg _)).trans
            (by simpa only [one_mul] using lp.norm_apply_le_norm ENNReal.top_ne_zero x (n i)))⟩⟩
      map_add' := by intros; apply lp.ext; funext i; exact map_add _ _ _
      map_smul' := by intros; apply lp.ext; funext i; exact map_smul _ _ _ }
    1 (fun x => by
      rw [one_mul]
      apply lp.norm_le_of_forall_le (norm_nonneg x)
      intro i
      exact ((s i).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (hs i) (norm_nonneg _)).trans
          (by simpa only [one_mul] using lp.norm_apply_le_norm ENNReal.top_ne_zero x (n i))))

@[simp] theorem boundedProductRead_apply (n : ℕ → ℕ)
    (s : ∀ i, F (n i) →L[𝕜] E i) (hs : ∀ i, ‖s i‖ ≤ 1)
    (x : lp F ∞) (i : ℕ) : boundedProductRead n s hs x i = s i (x (n i)) := rfl

theorem norm_boundedProductRead_le (n : ℕ → ℕ)
    (s : ∀ i, F (n i) →L[𝕜] E i) (hs : ∀ i, ‖s i‖ ≤ 1) :
    ‖boundedProductRead n s hs‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem boundedProductRead_comp_insert (n : ℕ → ℕ) (hn : Function.Injective n)
    (r : ∀ i, E i →L[𝕜] F (n i)) (hr : ∀ i, ‖r i‖ ≤ 1)
    (s : ∀ i, F (n i) →L[𝕜] E i) (hs : ∀ i, ‖s i‖ ≤ 1)
    (h : ∀ i, (s i).comp (r i) = ContinuousLinearMap.id 𝕜 (E i)) :
    (boundedProductRead n s hs).comp (boundedProductInsert n r hr) =
      ContinuousLinearMap.id 𝕜 (lp E ∞) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  change s i (boundedProductInsert n r hr x (n i)) = x i
  rw [boundedProductInsert_apply_image n hn]
  exact DFunLike.congr_fun (h i) (x i)

def boundedProductDiagonal (D : ∀ i, E i →L[𝕜] F i)
    (C : ℝ) (hC : 0 ≤ C) (hD : ∀ i, ‖D i‖ ≤ C) : lp E ∞ →L[𝕜] lp F ∞ :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => D i (x i), memℓp_infty ⟨C * ‖x‖, by
        rintro _ ⟨i, rfl⟩
        exact ((D i).le_opNorm _).trans (mul_le_mul (hD i)
          (lp.norm_apply_le_norm ENNReal.top_ne_zero x i) (norm_nonneg _) hC)⟩⟩
      map_add' := by intros; apply lp.ext; funext i; exact map_add _ _ _
      map_smul' := by intros; apply lp.ext; funext i; exact map_smul _ _ _ }
    C (fun x => by
      apply lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg x))
      intro i
      exact ((D i).le_opNorm _).trans (mul_le_mul (hD i)
        (lp.norm_apply_le_norm ENNReal.top_ne_zero x i) (norm_nonneg _) hC))

@[simp] theorem boundedProductDiagonal_apply (D : ∀ i, E i →L[𝕜] F i)
    (C : ℝ) (hC : 0 ≤ C) (hD : ∀ i, ‖D i‖ ≤ C) (x : lp E ∞) (i : ℕ) :
    boundedProductDiagonal D C hC hD x i = D i (x i) := rfl

theorem norm_boundedProductDiagonal_le (D : ∀ i, E i →L[𝕜] F i)
    (C : ℝ) (hC : 0 ≤ C) (hD : ∀ i, ‖D i‖ ≤ C) :
    ‖boundedProductDiagonal D C hC hD‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

end ThesisCommon
