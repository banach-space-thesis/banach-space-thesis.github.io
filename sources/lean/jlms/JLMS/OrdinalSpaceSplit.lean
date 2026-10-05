import JLMS.OrdinalScattered
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Splitting ordinal function spaces into two summands

For an infinite ordinal β, the clopen intervals [0,α] and (α,α+β]
in [0,α+β] are homeomorphic to [0,α] and [0,β], respectively.
Restriction therefore gives a linear isometry onto the product of the
two continuous-function spaces. This supplies the finite-sum step used
in Section 9, independently of the classification theorem.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Precomposition by a homeomorphism preserves the sup norm. -/
def continuousMapDomainIsometry {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [CompactSpace Y] (e : X ≃ₜ Y) :
    C(Y, 𝕜) ≃ₗᵢ[𝕜] C(X, 𝕜) where
  toFun f := ⟨fun x => f (e x), f.continuous.comp e.continuous⟩
  invFun f := ⟨fun y => f (e.symm y), f.continuous.comp e.symm.continuous⟩
  left_inv f := by ext y; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' f := by
    apply le_antisymm
    · exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun x => f.norm_coe_le_norm (e x)
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro y
      simpa using (ContinuousMap.norm_coe_le_norm
        (⟨fun x => f (e x), f.continuous.comp e.continuous⟩ : C(X, 𝕜)) (e.symm y))

/-- Functions on a disjoint sum form the sup-norm product of the function spaces. -/
def continuousMapSumIsometry {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [CompactSpace Y] :
    C(X ⊕ Y, 𝕜) ≃ₗᵢ[𝕜] C(X, 𝕜) × C(Y, 𝕜) where
  toFun f := (⟨fun x => f (.inl x), f.continuous.comp continuous_inl⟩,
    ⟨fun y => f (.inr y), f.continuous.comp continuous_inr⟩)
  invFun f := ⟨Sum.elim f.1 f.2, f.1.continuous.sumElim f.2.continuous⟩
  left_inv f := by ext x; cases x <;> rfl
  right_inv f := by rfl
  map_add' f g := by rfl
  map_smul' c f := by rfl
  norm_map' f := by
    apply le_antisymm
    · rw [Prod.norm_def]
      apply max_le
      · exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun x => f.norm_coe_le_norm (.inl x)
      · exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun y => f.norm_coe_le_norm (.inr y)
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro z
      change ‖f z‖ ≤ max
        ‖(⟨fun x => f (.inl x), f.continuous.comp continuous_inl⟩ : C(X, 𝕜))‖
        ‖(⟨fun y => f (.inr y), f.continuous.comp continuous_inr⟩ : C(Y, 𝕜))‖
      cases z with
      | inl x =>
        exact (ContinuousMap.norm_coe_le_norm
          (⟨fun x => f (.inl x), f.continuous.comp continuous_inl⟩ : C(X, 𝕜)) x).trans
            (le_max_left _ _)
      | inr y =>
        exact (ContinuousMap.norm_coe_le_norm
          (⟨fun y => f (.inr y), f.continuous.comp continuous_inr⟩ : C(Y, 𝕜)) y).trans
            (le_max_right _ _)

def ordinalSplitLeft (α β : Ordinal.{u}) : OrdinalInterval α → OrdinalInterval (α + β) :=
  fun x => ⟨x.val, x.property.1, x.property.2.trans (Ordinal.le_add_right α β)⟩

def ordinalSplitRight (α β : Ordinal.{u}) (hβ : Ordinal.omega0 ≤ β) :
    OrdinalInterval β → OrdinalInterval (α + β) :=
  fun x => ⟨(α + 1) + x.val, Ordinal.zero_le _, by
    have h := add_le_add_left x.property.2 (α + 1)
    simpa only [add_assoc, Ordinal.one_add_of_omega0_le hβ] using h⟩

theorem ordinalSplitRight_gt (α β : Ordinal.{u}) (hβ : Ordinal.omega0 ≤ β)
    (x : OrdinalInterval β) : α < (ordinalSplitRight α β hβ x).val := by
  exact (lt_add_one α).trans_le (Ordinal.le_add_right (α + 1) x.val)

theorem continuous_ordinalSplitLeft (α β : Ordinal.{u}) :
    Continuous (ordinalSplitLeft α β) := continuous_subtype_val.subtype_mk _

theorem continuous_ordinalSplitRight (α β : Ordinal.{u}) (hβ : Ordinal.omega0 ≤ β) :
    Continuous (ordinalSplitRight α β hβ) := by
  apply Continuous.subtype_mk
  exact (Order.isNormal_iff_strictMono_and_continuous.mp
    (Ordinal.isNormal_add_right (α + 1))).2.comp continuous_subtype_val

theorem ordinalSplit_bijective (α β : Ordinal.{u}) (hβ : Ordinal.omega0 ≤ β) :
    Function.Bijective (Sum.elim (ordinalSplitLeft α β) (ordinalSplitRight α β hβ)) := by
  constructor
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact congrArg (fun z : OrdinalInterval (α + β) => z.val) h
      | inr y =>
        have he := congrArg Subtype.val h
        exact False.elim ((ordinalSplitRight_gt α β hβ y).not_ge (he ▸ x.property.2))
    | inr x =>
      cases y with
      | inl y =>
        have he := congrArg Subtype.val h
        exact False.elim ((ordinalSplitRight_gt α β hβ x).not_ge (he.symm ▸ y.property.2))
      | inr y =>
        apply congrArg Sum.inr
        apply Subtype.ext
        exact add_left_cancel (congrArg Subtype.val h)
  · intro y
    by_cases hy : y.val ≤ α
    · exact ⟨.inl ⟨y.val, y.property.1, hy⟩, Subtype.ext rfl⟩
    · have hay : α + 1 ≤ y.val := Order.add_one_le_iff.mpr (lt_of_not_ge hy)
      let x : OrdinalInterval β := ⟨y.val - (α + 1), Ordinal.zero_le _, by
        apply Ordinal.sub_le.mpr
        simpa only [add_assoc, Ordinal.one_add_of_omega0_le hβ] using y.property.2⟩
      refine ⟨.inr x, Subtype.ext ?_⟩
      exact Ordinal.add_sub_cancel_of_le hay

/-- The two clopen intervals in [0,α+β], for infinite β. -/
def ordinalIntervalSplit (α β : Ordinal.{u}) (hβ : Ordinal.omega0 ≤ β) :
    OrdinalInterval α ⊕ OrdinalInterval β ≃ₜ OrdinalInterval (α + β) :=
  (Equiv.ofBijective _ (ordinalSplit_bijective α β hβ)).toHomeomorphOfContinuousClosed
    ((continuous_ordinalSplitLeft α β).sumElim (continuous_ordinalSplitRight α β hβ))
    (((continuous_ordinalSplitLeft α β).sumElim
      (continuous_ordinalSplitRight α β hβ)).isClosedMap)

/-- The actual isometric decomposition used in Section 9. -/
def ordinalSpaceAddIsometry (α β : Ordinal.{u}) (hβ : Ordinal.omega0 ≤ β) :
    OrdinalC 𝕜 (α + β) ≃ₗᵢ[𝕜] OrdinalC 𝕜 α × OrdinalC 𝕜 β :=
  (continuousMapDomainIsometry (ordinalIntervalSplit α β hβ)).trans continuousMapSumIsometry

/-- Doubling an infinite ordinal corresponds to taking the square of its function space. -/
def ordinalSpaceDoubleIsometry (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α) :
    OrdinalC 𝕜 (α * 2) ≃ₗᵢ[𝕜] OrdinalC 𝕜 α × OrdinalC 𝕜 α := by
  have htwo : α * 2 = α + α := by
    rw [← Ordinal.succ_one, Ordinal.mul_succ, mul_one]
  rw [htwo]
  exact ordinalSpaceAddIsometry (𝕜 := 𝕜) α α hα

end JLMS
