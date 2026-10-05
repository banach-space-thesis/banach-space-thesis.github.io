import ThesisCommon.Analysis.LpOneFamilyOperators
import ThesisCommon.Analysis.EllOneColumns

/-! Every bounded family in a Banach space is the family of columns of
an actual bounded operator on its scalar ell-one space. -/
noncomputable section
open scoped ENNReal Classical
namespace ThesisCommon
variable {𝕜 I F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

def lpOneColumnsOperator (f : I → F) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) :
    lp (fun _ : I => 𝕜) 1 →L[𝕜] F :=
  lpOneFamilyOperator (fun i => ContinuousLinearMap.toSpanSingleton 𝕜 (f i)) C hC
    (fun i => by simpa only [ContinuousLinearMap.norm_toSpanSingleton] using hf i)

theorem lpOneColumnsOperator_single (f : I → F) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C) (i : I) :
    lpOneColumnsOperator (𝕜 := 𝕜) f C hC hf (lp.single 1 i 1) = f i := by
  simp only [lpOneColumnsOperator, lpOneFamilyOperator_single,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]

theorem norm_lpOneColumnsOperator_le (f : I → F) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C) : ‖lpOneColumnsOperator (𝕜 := 𝕜) f C hC hf‖ ≤ C :=
  norm_lpOneFamilyOperator_le _ C hC _

theorem norm_sub_lpOneColumnsOperator_le (f g : I → F) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hf : ∀ i, ‖f i‖ ≤ C) (hg : ∀ i, ‖g i‖ ≤ D)
    {ε : ℝ} (hε : 0 ≤ ε) (hfg : ∀ i, ‖f i - g i‖ ≤ ε) :
    ‖lpOneColumnsOperator (𝕜 := 𝕜) f C hC hf - lpOneColumnsOperator g D hD hg‖ ≤ ε := by
  apply ellOne_norm_le_of_columns _ hε
  intro i
  simpa only [ContinuousLinearMap.sub_apply, lpOneColumnsOperator_single] using hfg i

end ThesisCommon
