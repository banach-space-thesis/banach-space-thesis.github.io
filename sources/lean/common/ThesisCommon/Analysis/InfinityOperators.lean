import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.Tactic.FunProp

/-! Actual diagonal, restriction and zero-extension operators on ℓ∞(X).
No matrix representation assumption is made for a general operator.
-/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A uniformly bounded family of coordinate maps induces a bounded diagonal map. -/
def infinityDiagonal (F : ℕ → X →L[𝕜] Y) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n, ‖F n‖ ≤ C) : EllInfinitySum X →L[𝕜] EllInfinitySum Y :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => F n (x n), memℓp_infty ⟨C * ‖x‖, by
        rintro _ ⟨n, rfl⟩
        exact ((F n).le_opNorm _).trans (mul_le_mul (hF n)
          (lp.norm_apply_le_norm ENNReal.top_ne_zero x n) (norm_nonneg _) hC)⟩⟩
      map_add' := by intros; ext n; exact map_add _ _ _
      map_smul' := by intros; ext n; exact map_smul _ _ _ }
    C (fun x => lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg _)) (fun n =>
      ((F n).le_opNorm _).trans (mul_le_mul (hF n)
        (lp.norm_apply_le_norm ENNReal.top_ne_zero x n) (norm_nonneg _) hC)))

@[simp] theorem infinityDiagonal_apply (F : ℕ → X →L[𝕜] Y) (C : ℝ) (hC hF)
    (x : EllInfinitySum X) (n : ℕ) : infinityDiagonal F C hC hF x n = F n (x n) := rfl

theorem norm_infinityDiagonal_le (F : ℕ → X →L[𝕜] Y) (C : ℝ) (hC hF) :
    ‖infinityDiagonal F C hC hF‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

/-- Restrict to a reindexed set of coordinates; works for every injection. -/
def infinityRestrict (e : ℕ ↪ ℕ) : EllInfinitySum X →L[𝕜] EllInfinitySum X :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => x (e n), memℓp_infty ⟨‖x‖, by
        rintro _ ⟨n, rfl⟩
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero x (e n)⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun x => by
      simp only [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg _) fun n =>
        lp.norm_apply_le_norm ENNReal.top_ne_zero x (e n))

@[simp] theorem infinityRestrict_apply (e : ℕ ↪ ℕ) (x : EllInfinitySum X) (n : ℕ) :
    infinityRestrict (𝕜 := 𝕜) e x n = x (e n) := rfl

theorem norm_infinityRestrict_le (e : ℕ ↪ ℕ) :
    ‖infinityRestrict (𝕜 := 𝕜) (X := X) e‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

private theorem extend_norm_le (e : ℕ ↪ ℕ) (x : EllInfinitySum X) (n : ℕ) :
    ‖Function.extend e x (fun _ => 0) n‖ ≤ ‖x‖ := by
  classical
  by_cases h : ∃ i, e i = n
  · obtain ⟨i, rfl⟩ := h
    rw [e.injective.extend_apply]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero x i
  · rw [Function.extend_apply' _ _ _ h, norm_zero]
    exact norm_nonneg _

/-- Insert a bounded sequence on the image of e and use zero elsewhere. -/
def infinityExtend (e : ℕ ↪ ℕ) : EllInfinitySum X →L[𝕜] EllInfinitySum X := by
  classical
  refine LinearMap.mkContinuous
    { toFun := fun x => ⟨Function.extend e x (fun _ => 0),
        memℓp_infty ⟨‖x‖, by rintro _ ⟨n, rfl⟩; exact extend_norm_le e x n⟩⟩
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · intro x y
    ext n
    by_cases h : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := h
      simp [e.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  · intro a x
    ext n
    by_cases h : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := h
      simp [e.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  · intro x
    simp only [one_mul]
    exact lp.norm_le_of_forall_le (norm_nonneg _) (extend_norm_le e x)

@[simp] theorem infinityExtend_apply_image (e : ℕ ↪ ℕ) (x : EllInfinitySum X) (n : ℕ) :
    infinityExtend (𝕜 := 𝕜) e x (e n) = x n := by
  simp [infinityExtend, e.injective.extend_apply]

theorem norm_infinityExtend_le (e : ℕ ↪ ℕ) :
    ‖infinityExtend (𝕜 := 𝕜) (X := X) e‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem infinityRestrict_comp_extend (e : ℕ ↪ ℕ) :
    (infinityRestrict (𝕜 := 𝕜) (X := X) e).comp (infinityExtend e) =
      ContinuousLinearMap.id 𝕜 (EllInfinitySum X) := by
  ext x n
  simp

end ThesisCommon
