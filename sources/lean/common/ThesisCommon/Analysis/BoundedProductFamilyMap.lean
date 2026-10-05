import ThesisCommon.Analysis.SequenceSpaces

/-! A uniformly bounded family of genuine operators gives a bounded map into
the actual bounded product. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 ι E : Type*} [RCLike 𝕜] {F : ι → Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

def boundedProductFamilyMap (A : ∀ i, E →L[𝕜] F i)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) : E →L[𝕜] lp F ∞ :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => A i x, memℓp_infty ⟨C * ‖x‖, by
        rintro _ ⟨i, rfl⟩
        exact ((A i).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg x))⟩⟩
      map_add' := fun x y => by apply lp.ext; funext i; exact map_add (A i) x y
      map_smul' := fun c x => by apply lp.ext; funext i; exact map_smul (A i) c x }
    C (fun x => lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg x))
      (fun i => ((A i).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg x))))

@[simp] theorem boundedProductFamilyMap_apply (A : ∀ i, E →L[𝕜] F i)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (x : E) (i : ι) :
    boundedProductFamilyMap A C hC hA x i = A i x := rfl

theorem norm_boundedProductFamilyMap_le (A : ∀ i, E →L[𝕜] F i)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) :
    ‖boundedProductFamilyMap A C hC hA‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

end ThesisCommon

