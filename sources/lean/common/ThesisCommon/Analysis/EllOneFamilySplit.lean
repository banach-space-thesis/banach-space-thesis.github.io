import ThesisCommon.Analysis.EllOneFamilySubset
import Mathlib.Topology.Algebra.Module.Equiv

/-! An arbitrary heterogeneous ell-one sum splits into the two complementary
index subfamilies by actual bounded linear maps. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace ThesisCommon
variable {𝕜 I : Type*} [RCLike 𝕜] {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

def ellOneFamilySplit (A : Set I) :
    lp E 1 ≃L[𝕜] (lp (fun i : A => E i.val) 1 × lp (fun i : (Aᶜ : Set I) => E i.val) 1) where
  toFun := (ellOneFamilyRestrict A).prod (ellOneFamilyRestrict Aᶜ)
  invFun := (ellOneFamilyExtend A).coprod (ellOneFamilyExtend Aᶜ)
  left_inv x := DFunLike.congr_fun (ellOneFamilyExtend_restrict_add_compl A) x
  right_inv y := by
    apply Prod.ext
    · apply lp.ext
      funext i
      change ellOneFamilyRestrict (𝕜 := 𝕜) A
        (ellOneFamilyExtend (𝕜 := 𝕜) A y.1 + ellOneFamilyExtend (𝕜 := 𝕜) Aᶜ y.2) i = y.1 i
      simp [i.property]
    · apply lp.ext
      funext i
      change ellOneFamilyRestrict (𝕜 := 𝕜) Aᶜ
        (ellOneFamilyExtend (𝕜 := 𝕜) A y.1 + ellOneFamilyExtend (𝕜 := 𝕜) Aᶜ y.2) i = y.2 i
      simp [show i.val ∉ A from i.property]
  map_add' := map_add ((ellOneFamilyRestrict (𝕜 := 𝕜) A).prod (ellOneFamilyRestrict Aᶜ))
  map_smul' := map_smul ((ellOneFamilyRestrict (𝕜 := 𝕜) A).prod (ellOneFamilyRestrict Aᶜ))
  continuous_toFun := ((ellOneFamilyRestrict (𝕜 := 𝕜) A).prod (ellOneFamilyRestrict Aᶜ)).continuous
  continuous_invFun := ((ellOneFamilyExtend (𝕜 := 𝕜) A).coprod (ellOneFamilyExtend Aᶜ)).continuous

end ThesisCommon
