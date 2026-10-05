import ThesisCommon.Analysis.LpOneRestriction
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Evaluation series for an arbitrary continuous ell-one representation of
a real Banach-space dual. No compatibility with a lattice order is assumed. -/
noncomputable section
namespace ThesisCommon
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] Classical.propDecidable

def dualAtom (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1) (i : I) : E →L[ℝ] ℝ :=
  d.symm (lp.single 1 i 1)

theorem dualAtom_norm_le (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1) (i : I) :
    ‖dualAtom d i‖ ≤ ‖d.symm.toContinuousLinearMap‖ := by
  have h := d.symm.toContinuousLinearMap.le_opNorm (lp.single 1 i (1 : ℝ))
  simpa only [lp.norm_single (by norm_num : (0 : ENNReal) < 1),norm_one,mul_one] using h

theorem dualAtom_evaluation_hasSum (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (φ : E →L[ℝ] ℝ) (x : E) : HasSum (fun i => d φ i * dualAtom d i x) (φ x) := by
  let T := (ContinuousLinearMap.apply ℝ ℝ x).comp d.symm.toContinuousLinearMap
  have hs := (lp.hasSum_single (by norm_num : (1 : ENNReal) ≠ ⊤) (d φ)).map T T.continuous
  have hi (i : I) : T (lp.single 1 i (d φ i)) = d φ i * dualAtom d i x := by
    have hsingle : lp.single (E := fun _ : I => ℝ) 1 i (d φ i) =
        (d φ i) • lp.single (E := fun _ : I => ℝ) 1 i (1 : ℝ) := by
      rw [← lp.single_smul]
      simp only [smul_eq_mul,mul_one]
    rw [hsingle,map_smul]
    rfl
  have ht : T (d φ) = φ x := by simp [T]
  simpa only [Function.comp_def,hi,ht] using hs

theorem dualAtom_evaluation_bound (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (φ : E →L[ℝ] ℝ) (x : E) (B : ℝ)
    (hB : ∀ i, d φ i ≠ 0 → |dualAtom d i x| ≤ B) :
    |φ x| ≤ ‖d φ‖ * B := by
  have h := (dualAtom_evaluation_hasSum d φ x).norm_le_of_bounded
    ((lp_one_hasSum_norm (d φ)).mul_right B) (fun i => ?_)
  · simpa only [Real.norm_eq_abs] using h
  · by_cases hi : d φ i = 0
    · simp only [hi,zero_mul,norm_zero,le_refl]
    · rw [norm_mul,Real.norm_eq_abs (dualAtom d i x)]
      exact mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _)

end ThesisCommon
