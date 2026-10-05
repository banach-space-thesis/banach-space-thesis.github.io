import ThesisCommon.Analysis.UnitCharge

/-! A pushforward of power-set charges, defined by preimages of tests. -/
noncomputable section
namespace ThesisCommon

def UnitCharge.map {α β : Type*} (μ : UnitCharge α) (f : α → β) : UnitCharge β where
  toFun A := μ (f ⁻¹' A)
  map_empty := μ.map_empty
  map_union _ _ h := μ.map_union _ _ (h.preimage f)
  variation_le F A h := μ.variation_le F (fun j => f ⁻¹' A j)
    (fun _ hi _ hj hij => (h hi hj hij).preimage f)

@[simp] theorem UnitCharge.map_apply {α β : Type*} (μ : UnitCharge α) (f : α → β) (A : Set β) :
    μ.map f A = μ (f ⁻¹' A) := rfl

end ThesisCommon
