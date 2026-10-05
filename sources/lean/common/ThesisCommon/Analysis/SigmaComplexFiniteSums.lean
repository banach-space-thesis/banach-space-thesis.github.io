import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace ThesisCommon

/-- The coordinate rearrangement used in Sigma Section 2. -/
def complexCrossRegroup (A B C D : Type*)
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C] [NormedAddCommGroup D] [NormedSpace ℂ D] :
    ((A × B) × (C × D)) ≃L[ℂ] ((C × B) × (A × D)) where
  toFun x := ((x.2.1, x.1.2), (x.1.1, x.2.2))
  invFun x := ((x.2.1, x.1.2), (x.1.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- C(K ⊔ L) is linearly homeomorphic to C(K) × C(L), by restriction and pasting.
Both factors have the actual compact-open/sup-norm topology. -/
def complexContinuousSumEquiv (K L : Type*) [TopologicalSpace K] [TopologicalSpace L]
    [CompactSpace K] [CompactSpace L] : C(K ⊕ L, ℂ) ≃L[ℂ] (C(K, ℂ) × C(L, ℂ)) := by
  let e : C(K ⊕ L, ℂ) ≃ₗ[ℂ] (C(K, ℂ) × C(L, ℂ)) :=
    { toFun := fun f => (⟨fun k => f (.inl k), f.continuous.comp continuous_inl⟩,
                         ⟨fun l => f (.inr l), f.continuous.comp continuous_inr⟩)
      invFun := fun fg => ⟨Sum.elim fg.1 fg.2,
        continuous_sum_dom.mpr ⟨fg.1.continuous, fg.2.continuous⟩⟩
      left_inv := by intro f; ext x; cases x <;> rfl
      right_inv := by intro fg; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact LinearEquiv.toContinuousLinearEquivOfBounds e 1 1
    (by
      intro f
      rw [one_mul, Prod.norm_def]
      apply max_le
      · exact (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun k => f.norm_coe_le_norm (.inl k)
      · exact (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun l => f.norm_coe_le_norm (.inr l))
    (by
      intro fg
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg fg)).2
      intro x
      cases x with
      | inl k => exact (fg.1.norm_coe_le_norm k).trans (le_max_left _ _)
      | inr l => exact (fg.2.norm_coe_le_norm l).trans (le_max_right _ _))

end ThesisCommon


