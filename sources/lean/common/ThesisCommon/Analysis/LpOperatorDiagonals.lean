import ThesisCommon.Analysis.SequenceEntryOperators

/-! The bounded product of coefficient operators embeds as genuine
diagonal operators on an lp sum. Reading their diagonal is a left inverse. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

def lpOperatorDiagonalMap :
    lp (fun _ : ℕ => X →L[𝕜] X) ∞ →L[𝕜]
      (lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p) :=
  LinearMap.mkContinuous
    { toFun := fun a => lpDiagonal p a ‖a‖ (norm_nonneg a)
        (fun i => lp.norm_apply_le_norm ENNReal.top_ne_zero a i)
      map_add' := by
        intro a b
        apply ContinuousLinearMap.ext
        intro x
        apply lp.ext
        funext i
        rfl
      map_smul' := by
        intro c a
        apply ContinuousLinearMap.ext
        intro x
        apply lp.ext
        funext i
        rfl }
    1 (fun a => by
      rw [one_mul]
      exact norm_lpDiagonal_le a ‖a‖ (norm_nonneg a)
        (fun i => lp.norm_apply_le_norm ENNReal.top_ne_zero a i))

theorem lpOperatorDiagonalMap_apply (a : lp (fun _ : ℕ => X →L[𝕜] X) ∞)
    (x : lp (fun _ : ℕ => X) p) (i : ℕ) : lpOperatorDiagonalMap p a x i = a i (x i) := rfl

theorem norm_lpOperatorDiagonalMap_le : ‖lpOperatorDiagonalMap (𝕜 := 𝕜) (X := X) p‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def lpOperatorDiagonalRead :
    (lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p) →L[𝕜]
      lp (fun _ : ℕ => X →L[𝕜] X) ∞ :=
  LinearMap.mkContinuous
    { toFun := fun T => ⟨fun i => lpEntry T i i,
        memℓp_infty ⟨‖T‖, by rintro _ ⟨i, rfl⟩; exact norm_lpEntry_le T i i⟩⟩
      map_add' := by
        intro T S
        apply lp.ext
        funext i
        apply ContinuousLinearMap.ext
        intro x
        rfl
      map_smul' := by
        intro c T
        apply lp.ext
        funext i
        apply ContinuousLinearMap.ext
        intro x
        rfl }
    1 (fun T => by
      rw [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg T) (fun i => norm_lpEntry_le T i i))

theorem lpOperatorDiagonalRead_apply
    (T : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p) (i : ℕ) :
    lpOperatorDiagonalRead p T i = lpEntry T i i := rfl

theorem norm_lpOperatorDiagonalRead_le : ‖lpOperatorDiagonalRead (𝕜 := 𝕜) (X := X) p‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem lpOperatorDiagonalRead_comp_map :
    (lpOperatorDiagonalRead (𝕜 := 𝕜) (X := X) p).comp (lpOperatorDiagonalMap p) =
      ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => X →L[𝕜] X) ∞) := by
  apply ContinuousLinearMap.ext
  intro a
  apply lp.ext
  funext i
  apply ContinuousLinearMap.ext
  intro x
  change a i ((lp.single p i x : lp (fun _ : ℕ => X) p) i) = a i x
  rw [lp.single_apply_self]

end ThesisCommon
