import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Tactic

/-! The dual of the supremum-norm product has the sum norm on its two real
coordinate functionals. The lower estimate uses approximate norm attainment. -/
noncomputable section
namespace ThesisCommon
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def dualProdLeft (φ : (E × F) →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  φ.comp (ContinuousLinearMap.inl ℝ E F)

def dualProdRight (φ : (E × F) →L[ℝ] ℝ) : F →L[ℝ] ℝ :=
  φ.comp (ContinuousLinearMap.inr ℝ E F)

theorem dualProd_apply (φ : (E × F) →L[ℝ] ℝ) (x : E) (y : F) :
    φ (x,y) = dualProdLeft φ x + dualProdRight φ y := by
  have h := φ.map_add (x,0) (0,y)
  simpa [dualProdLeft,dualProdRight] using h

theorem exists_near_norm_positive (φ : E →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ ‖φ‖ - ε < φ x := by
  obtain ⟨x,hx,hφ⟩ := φ.exists_lt_apply_of_lt_opNorm (r := ‖φ‖ - ε) (by linarith)
  by_cases h : 0 ≤ φ x
  · exact ⟨x,hx.le,by simpa only [Real.norm_eq_abs,abs_of_nonneg h] using hφ⟩
  · refine ⟨-x,by simpa only [norm_neg] using hx.le,?_⟩
    rw [map_neg]
    simpa only [Real.norm_eq_abs,abs_of_neg (lt_of_not_ge h)] using hφ

theorem dualProd_norm (φ : (E × F) →L[ℝ] ℝ) :
    ‖φ‖ = ‖dualProdLeft φ‖ + ‖dualProdRight φ‖ := by
  apply le_antisymm
  · apply φ.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
    rintro ⟨x,y⟩
    rw [dualProd_apply,add_mul]
    apply (norm_add_le _ _).trans
    exact add_le_add
      (((dualProdLeft φ).le_opNorm x).trans
        (mul_le_mul_of_nonneg_left (norm_fst_le (x,y)) (norm_nonneg _)))
      (((dualProdRight φ).le_opNorm y).trans
        (mul_le_mul_of_nonneg_left (norm_snd_le (x,y)) (norm_nonneg _)))
  · by_contra h
    have hlt : ‖φ‖ < ‖dualProdLeft φ‖ + ‖dualProdRight φ‖ := lt_of_not_ge h
    let ε := (‖dualProdLeft φ‖ + ‖dualProdRight φ‖ - ‖φ‖) / 4
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨x,hx,hpx⟩ := exists_near_norm_positive (dualProdLeft φ) hε
    obtain ⟨y,hy,hpy⟩ := exists_near_norm_positive (dualProdRight φ) hε
    have hxy : ‖(x,y)‖ ≤ 1 := by rw [Prod.norm_def]; exact max_le hx hy
    have hb : φ (x,y) ≤ ‖φ‖ := calc
      _ ≤ ‖φ (x,y)‖ := le_abs_self _
      _ ≤ ‖φ‖ * ‖(x,y)‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ := (mul_le_mul_of_nonneg_left hxy (norm_nonneg _)).trans_eq (mul_one _)
    rw [dualProd_apply] at hb
    dsimp [ε] at hpx hpy
    linarith

end ThesisCommon
