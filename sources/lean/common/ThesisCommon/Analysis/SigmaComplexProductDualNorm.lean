import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The dual of the supremum-norm product has the sum norm on its two real
coordinate functionals. The lower estimate uses approximate norm attainment. -/
noncomputable section
namespace ThesisCommon
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def complexDualProdLeft (φ : (E × F) →L[ℂ] ℂ) : E →L[ℂ] ℂ :=
  φ.comp (ContinuousLinearMap.inl ℂ E F)

def complexDualProdRight (φ : (E × F) →L[ℂ] ℂ) : F →L[ℂ] ℂ :=
  φ.comp (ContinuousLinearMap.inr ℂ E F)

theorem complexDualProd_apply (φ : (E × F) →L[ℂ] ℂ) (x : E) (y : F) :
    φ (x,y) = complexDualProdLeft φ x + complexDualProdRight φ y := by
  have h := φ.map_add (x,0) (0,y)
  simpa [complexDualProdLeft,complexDualProdRight] using h

theorem complex_exists_near_norm_positive (φ : E →L[ℂ] ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ ‖φ‖ - ε < (φ x).re := by
  obtain ⟨x,hx,hφ⟩ := φ.exists_lt_apply_of_lt_opNorm (r := ‖φ‖ - ε) (by linarith)
  obtain ⟨c,hc,hcz⟩ := Complex.exists_norm_eq_mul_self (φ x)
  refine ⟨c • x,by simpa [norm_smul,hc] using hx.le,?_⟩
  have heq : φ (c • x) = (‖φ x‖ : ℂ) := by
    rw [map_smul,smul_eq_mul]
    exact hcz.symm
  simpa [heq] using hφ

theorem complexDualProd_norm (φ : (E × F) →L[ℂ] ℂ) :
    ‖φ‖ = ‖complexDualProdLeft φ‖ + ‖complexDualProdRight φ‖ := by
  apply le_antisymm
  · apply φ.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
    rintro ⟨x,y⟩
    rw [complexDualProd_apply,add_mul]
    apply (norm_add_le _ _).trans
    exact add_le_add
      (((complexDualProdLeft φ).le_opNorm x).trans
        (mul_le_mul_of_nonneg_left (norm_fst_le (x,y)) (norm_nonneg _)))
      (((complexDualProdRight φ).le_opNorm y).trans
        (mul_le_mul_of_nonneg_left (norm_snd_le (x,y)) (norm_nonneg _)))
  · by_contra h
    have hlt : ‖φ‖ < ‖complexDualProdLeft φ‖ + ‖complexDualProdRight φ‖ := lt_of_not_ge h
    let ε := (‖complexDualProdLeft φ‖ + ‖complexDualProdRight φ‖ - ‖φ‖) / 4
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨x,hx,hpx⟩ := complex_exists_near_norm_positive (complexDualProdLeft φ) hε
    obtain ⟨y,hy,hpy⟩ := complex_exists_near_norm_positive (complexDualProdRight φ) hε
    have hxy : ‖(x,y)‖ ≤ 1 := by rw [Prod.norm_def]; exact max_le hx hy
    have hb : (φ (x,y)).re ≤ ‖φ‖ := calc
      _ ≤ ‖φ (x,y)‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ ≤ ‖φ‖ * ‖(x,y)‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ := (mul_le_mul_of_nonneg_left hxy (norm_nonneg _)).trans_eq (mul_one _)
    rw [complexDualProd_apply,Complex.add_re] at hb
    dsimp [ε] at hpx hpy
    linarith

end ThesisCommon


