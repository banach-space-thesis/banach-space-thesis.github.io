import ThesisCommon.Analysis.UncountableSchauderSumSeries

/-! Coordinate insertions and uniformly bounded coordinate operators on the
actual vector-valued basis sums, with their exact norm estimates.
-/
noncomputable section
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
namespace UncountableSchauderSum
variable {𝕜 Γ X Y Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable {b : NormalizedSchauderFamily 𝕜 Γ X} {hb : b.IsOneUnconditional}

/-- Pointwise norm domination controls the actual sum norm, even with
different coefficient spaces. -/
theorem norm_le_of_apply_le (y : UncountableSchauderSum b hb Y) (z : UncountableSchauderSum b hb Z)
    (h : ∀ n, ‖y n‖ ≤ ‖z n‖) : ‖y‖ ≤ ‖z‖ := by
  apply b.norm_le_of_coord_le hb
  intro n
  simpa only [coord_normVector, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] using h n

/-- Domination by a multiple of an existing sum supplies genuine membership. -/
def ofDominated (y : UncountableSchauderSum b hb Y) (f : Γ → Z) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C * ‖y n‖) : UncountableSchauderSum b hb Z := ⟨f, by
  obtain ⟨x, hx, _⟩ := b.exists_of_coord_domination hb ((C : 𝕜) • normVector y)
    (fun n => (‖f n‖ : 𝕜)) (by
      intro n
      rw [map_smul, coord_normVector, smul_eq_mul, ← RCLike.ofReal_mul]
      simpa only [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (mul_nonneg hC (norm_nonneg _))] using hf n)
  exact ⟨x, hx⟩⟩

@[simp] theorem ofDominated_apply (y : UncountableSchauderSum b hb Y) (f : Γ → Z)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C * ‖y n‖) (n : Γ) :
    ofDominated y f hC hf n = f n := rfl

theorem norm_ofDominated_le (y : UncountableSchauderSum b hb Y) (f : Γ → Z)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C * ‖y n‖) :
    ‖ofDominated y f hC hf‖ ≤ C * ‖y‖ := by
  have h : ‖normVector (ofDominated y f hC hf)‖ ≤ ‖(C : 𝕜) • normVector y‖ := by
    apply b.norm_le_of_coord_le hb
    intro n
    rw [map_smul, coord_normVector, coord_normVector, smul_eq_mul, ← RCLike.ofReal_mul]
    simpa only [ofDominated_apply, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (mul_nonneg hC (norm_nonneg _))] using hf n
  simpa only [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hC] using h

/-- Bounded insertion into a single coordinate; it is isometric. -/
def singleL (n : Γ) : Y →L[𝕜] UncountableSchauderSum b hb Y :=
  LinearMap.mkContinuous
    { toFun := single n
      map_add' := by intro y z; ext i; by_cases hi : i = n <;> simp [single_apply, hi]
      map_smul' := by intro c y; ext i; by_cases hi : i = n <;> simp [single_apply, hi] }
    1 (fun y => by simp)

@[simp] theorem singleL_apply (n : Γ) (y : Y) :
    singleL (b := b) (hb := hb) (Y := Y) n y = single n y := rfl

/-- Uniformly bounded families of actual coordinate operators act on X(Y). -/
def diagonal (F : Γ → Y →L[𝕜] Z) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n, ‖F n‖ ≤ C) : UncountableSchauderSum b hb Y →L[𝕜] UncountableSchauderSum b hb Z :=
  LinearMap.mkContinuous
    { toFun := fun y => ofDominated y (fun n => F n (y n)) hC
        (fun n => ((F n).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hF n) (norm_nonneg _)))
      map_add' := by intro y z; ext n; exact map_add (F n) _ _
      map_smul' := by intro c y; ext n; exact map_smul (F n) _ _ }
    C (fun y => norm_ofDominated_le y _ hC (fun n => ((F n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hF n) (norm_nonneg _))))

@[simp] theorem diagonal_apply (F : Γ → Y →L[𝕜] Z) (C : ℝ) (hC hF)
    (y : UncountableSchauderSum b hb Y) (n : Γ) : diagonal F C hC hF y n = F n (y n) := rfl

theorem norm_diagonal_le (F : Γ → Y →L[𝕜] Z) (C : ℝ) (hC hF) :
    ‖diagonal (b := b) (hb := hb) F C hC hF‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

end UncountableSchauderSum
end ThesisCommon

