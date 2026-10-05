import JLMS.OrdinalHeadProjection
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! Initial-segment indicators densely span every ordinal continuous-function
space. The proof uses their actual point-separating star algebra. -/
noncomputable section
namespace Posets
open JLMS
open scoped Pointwise
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096

theorem ordinalHeadIndicator_mul (α β γ : Ordinal.{0}) :
    ordinalHeadIndicator (𝕜 := 𝕜) α β * ordinalHeadIndicator α γ =
      ordinalHeadIndicator α (min β γ) := by
  ext x
  simp only [ContinuousMap.mul_apply, ordinalHeadIndicator_apply, le_min_iff]
  split_ifs <;> simp_all

@[simp] theorem ordinalHeadIndicator_star (α β : Ordinal.{0}) :
    star (ordinalHeadIndicator (𝕜 := 𝕜) α β) = ordinalHeadIndicator α β := by
  ext x
  simp only [ContinuousMap.star_apply, ordinalHeadIndicator_apply]
  split_ifs <;> simp

def ordinalHeadIndicatorMonoid (α : Ordinal.{0}) : Submonoid (OrdinalC 𝕜 α) where
  carrier := Set.range (fun β : OrdinalInterval α => ordinalHeadIndicator α β.val)
  one_mem' := by
    refine ⟨⟨α, Ordinal.zero_le _, le_rfl⟩, ?_⟩
    ext x
    simp [x.property.2]
  mul_mem' := by
    rintro f g ⟨β, rfl⟩ ⟨γ, rfl⟩
    exact ⟨min β γ, (ordinalHeadIndicator_mul α β.val γ.val).symm⟩

theorem ordinalHeadIndicatorMonoid_star (α : Ordinal.{0}) :
    star (ordinalHeadIndicatorMonoid (𝕜 := 𝕜) α : Set (OrdinalC 𝕜 α)) =
      (ordinalHeadIndicatorMonoid (𝕜 := 𝕜) α : Set (OrdinalC 𝕜 α)) := by
  ext f
  change (∃ β : OrdinalInterval α, ordinalHeadIndicator α β.val = star f) ↔
    ∃ β : OrdinalInterval α, ordinalHeadIndicator α β.val = f
  constructor
  · rintro ⟨β, hβ⟩
    exact ⟨β, by simpa using congrArg star hβ⟩
  · rintro ⟨β, rfl⟩
    exact ⟨β, (ordinalHeadIndicator_star α β.val).symm⟩

theorem ordinalHeadIndicators_dense (α : Ordinal.{0}) :
    (Submodule.span 𝕜 (Set.range (fun β : OrdinalInterval α =>
      ordinalHeadIndicator (𝕜 := 𝕜) α β.val))).topologicalClosure = ⊤ := by
  let M := ordinalHeadIndicatorMonoid (𝕜 := 𝕜) α
  let A := StarAlgebra.adjoin 𝕜 (M : Set (OrdinalC 𝕜 α))
  have hA : A.SeparatesPoints := by
    intro x y hxy
    have hv : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · refine ⟨ordinalHeadIndicator (𝕜 := 𝕜) α x.val,
        ⟨ordinalHeadIndicator α x.val, StarAlgebra.subset_adjoin 𝕜 _ ⟨x, rfl⟩, rfl⟩, ?_⟩
      simp [not_le_of_gt hlt]
    · refine ⟨ordinalHeadIndicator (𝕜 := 𝕜) α y.val,
        ⟨ordinalHeadIndicator α y.val, StarAlgebra.subset_adjoin 𝕜 _ ⟨y, rfl⟩, rfl⟩, ?_⟩
      simp [not_le_of_gt hgt]
  have hspan : A.toSubalgebra.toSubmodule = Submodule.span 𝕜 (M : Set (OrdinalC 𝕜 α)) := by
    dsimp [A]
    rw [StarAlgebra.adjoin_eq_span, ordinalHeadIndicatorMonoid_star, Set.union_self,
      Submonoid.closure_eq]
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  have hm := congrArg (fun B : StarSubalgebra 𝕜 (OrdinalC 𝕜 α) =>
    B.toSubalgebra.toSubmodule) htop
  change A.toSubalgebra.toSubmodule.topologicalClosure = ⊤ at hm
  rw [hspan] at hm
  exact hm

end Posets
