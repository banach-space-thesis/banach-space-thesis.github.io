import JLMS.AlgebraNormCompletion
import JLMS.OperatorNormComparison
import JLMS.MainStatements

/-!
# Automatic continuity implies uniqueness of every operator algebra norm

Both comparisons are obtained for each competing norm, without completeness.
Comparisons with the operator norm then compare any pair of algebra norms.
-/

noncomputable section
namespace JLMS
universe u w
variable {𝕜 : Type w} [RCLike 𝕜]

theorem equivalentNorms_of_reference_bounds {B : Type*} (p n m : B → ℝ)
    {cn Cn cm Cm : ℝ} (hcn : 0 < cn) (hCn : 0 < Cn) (hcm : 0 < cm) (hCm : 0 < Cm)
    (hn : ∀ x, cn * p x ≤ n x ∧ n x ≤ Cn * p x)
    (hm : ∀ x, cm * p x ≤ m x ∧ m x ≤ Cm * p x) : EquivalentNorms n m := by
  refine ⟨cm / Cn, div_pos hcm hCn, Cm / cn, div_pos hCm hcn, fun x => ?_⟩
  constructor
  · calc
      (cm / Cn) * n x = cm * (n x / Cn) := by ring
      _ ≤ cm * p x := mul_le_mul_of_nonneg_left ((div_le_iff₀ hCn).mpr
        (by simpa only [mul_comm] using (hn x).2)) hcm.le
      _ ≤ m x := (hm x).1
  · calc
      m x ≤ Cm * p x := (hm x).2
      _ ≤ Cm * (n x / cn) := mul_le_mul_of_nonneg_left ((le_div_iff₀ hcn).mpr
        (by simpa only [mul_comm] using (hn x).1)) hCm.le
      _ = (Cm / cn) * n x := by ring

theorem operatorAlgebra_hasUniqueNorm_of_automaticContinuity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hE : ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
      [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A],
      ∀ φ : (E →L[𝕜] E) →ₙₐ[𝕜] A, Continuous φ) :
    HasUniqueAlgebraNorm 𝕜 (B := E →L[𝕜] E) := by
  intro n m hn hm
  obtain ⟨Cn, hCn, hnupper⟩ := algebraNorm_upper_bound_of_automaticContinuity hE n hn
  obtain ⟨cn, hcn, hnlower⟩ := operatorNorm_lower_bound_of_upper n hn hCn hnupper
  obtain ⟨Cm, hCm, hmupper⟩ := algebraNorm_upper_bound_of_automaticContinuity hE m hm
  obtain ⟨cm, hcm, hmlower⟩ := operatorNorm_lower_bound_of_upper m hm hCm hmupper
  exact equivalentNorms_of_reference_bounds (fun T => ‖T‖) n m hcn hCn hcm hCm
    (fun T => ⟨hnlower T, hnupper T⟩) (fun T => ⟨hmlower T, hmupper T⟩)

theorem ordinal_operatorNorm_unique_of_theorem_1_3 (α : Ordinal.{u})
    (hα : Theorem_1_3.{u, max (u + 1) w, w} (𝕜 := 𝕜) α) :
    HasUniqueAlgebraNorm 𝕜 (B := OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) :=
  operatorAlgebra_hasUniqueNorm_of_automaticContinuity hα

end JLMS
