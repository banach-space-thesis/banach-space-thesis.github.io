import JLMS.OrdinalMatrixAlgebra
import JLMS.OrdinalHeadProjection

/-!
# Matrix formulas for ordinal head and tail projections

The head projection is diagonal. Consequently, composition on its right
keeps precisely the corresponding columns; its complement removes them.
These identities are used to isolate the tail operator in Ogden 6.16.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem ordinalOperatorRow_congr {α : Ordinal.{u}}
    (S T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (x : OrdinalInterval α)
    (h : ∀ f, S f x = T f x) : ordinalOperatorRow α S x = ordinalOperatorRow α T x := by
  apply congrArg (ordinalAtomicDualModel (𝕜 := 𝕜) α).representation
  ext f
  exact h ((ordinalContinuousCZeroEquiv (𝕜 := 𝕜) α).symm f)

@[simp] theorem ordinalOperatorMatrix_head (α β : Ordinal.{u}) (x y : OrdinalInterval α) :
    ordinalOperatorMatrix α (ordinalHeadProjection (𝕜 := 𝕜) α β) x y =
      if x.val ≤ β then (if x = y then 1 else 0) else 0 := by
  classical
  by_cases hx : x.val ≤ β
  · have hr := ordinalOperatorRow_congr (ordinalHeadProjection (𝕜 := 𝕜) α β)
      (ContinuousLinearMap.id 𝕜 _) x (fun f => by simp [hx])
    change ordinalOperatorRow α (ordinalHeadProjection (𝕜 := 𝕜) α β) x y = _
    rw [hr, if_pos hx]
    by_cases hxy : x = y
    · simpa only [if_pos hxy] using ordinalOperatorMatrix_id (𝕜 := 𝕜) α x y
    · simpa only [if_neg hxy] using ordinalOperatorMatrix_id (𝕜 := 𝕜) α x y
  · have hr := ordinalOperatorRow_congr (ordinalHeadProjection (𝕜 := 𝕜) α β)
      (0 : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) x (fun f => by simp [hx])
    change ordinalOperatorRow α (ordinalHeadProjection (𝕜 := 𝕜) α β) x y = _
    rw [hr]
    simpa only [if_neg hx] using ordinalOperatorMatrix_zero (𝕜 := 𝕜) α x y

@[simp] theorem ordinalOperatorMatrix_comp_head (α β : Ordinal.{u})
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (x y : OrdinalInterval α) :
    ordinalOperatorMatrix α (T.comp (ordinalHeadProjection α β)) x y =
      if y.val ≤ β then ordinalOperatorMatrix α T x y else 0 := by
  classical
  have hs := ordinalOperatorMatrix_comp_hasSum α T (ordinalHeadProjection α β) x y
  have hz (z : OrdinalInterval α) (hzy : z ≠ y) :
      ordinalOperatorMatrix α T x z *
        ordinalOperatorMatrix α (ordinalHeadProjection α β) z y = 0 := by
    simp [hzy]
  have ht : (∑' z : OrdinalInterval α, ordinalOperatorMatrix α T x z *
      ordinalOperatorMatrix α (ordinalHeadProjection α β) z y) =
      ordinalOperatorMatrix α T x y *
        ordinalOperatorMatrix α (ordinalHeadProjection α β) y y := tsum_eq_single y hz
  rw [hs.tsum_eq] at ht
  rw [ht]
  by_cases hy : y.val ≤ β <;> simp [hy]

@[simp] theorem ordinalOperatorMatrix_comp_tail (α β : Ordinal.{u})
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (x y : OrdinalInterval α) :
    ordinalOperatorMatrix α (T.comp
      (ContinuousLinearMap.id 𝕜 _ - ordinalHeadProjection α β)) x y =
      if y.val ≤ β then 0 else ordinalOperatorMatrix α T x y := by
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
    ordinalOperatorMatrix_sub, ordinalOperatorMatrix_comp_head]
  by_cases hy : y.val ≤ β <;> simp [hy]

theorem ordinalOperatorRow_endpoint_comp_tail_eq_zero {α β : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (hrow : ∀ y : OrdinalInterval α, β < y.val →
      ordinalOperatorMatrix α T ⟨α, Ordinal.zero_le _, le_rfl⟩ y = 0) :
    ordinalOperatorRow α (T.comp
      (ContinuousLinearMap.id 𝕜 _ - ordinalHeadProjection α β))
        ⟨α, Ordinal.zero_le _, le_rfl⟩ = 0 := by
  ext y
  change ordinalOperatorMatrix α _ _ y = 0
  rw [ordinalOperatorMatrix_comp_tail]
  split_ifs with hy
  · rfl
  · exact hrow y (lt_of_not_ge hy)

end JLMS
