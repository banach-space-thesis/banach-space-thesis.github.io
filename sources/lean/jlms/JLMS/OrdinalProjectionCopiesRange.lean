import JLMS.OrdinalProjectionCopies

/-!
# Range equivalences for complemented copies

The two explicit maps implementing a complemented copy also provide its
continuous linear equivalence with the range of the corresponding projection.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

def projectionRangeEquivOfRetraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (u v Q : E →L[𝕜] E)
    (hvu : v.comp u = ContinuousLinearMap.id 𝕜 E) (huv : u.comp v = Q) :
    E ≃L[𝕜] LinearMap.range Q := by
  have hv (x : E) : v (u x) = x := congrArg (fun T : E →L[𝕜] E => T x) hvu
  have hu (x : E) : u (v x) = Q x := congrArg (fun T : E →L[𝕜] E => T x) huv
  have hf (x : E) : Q (u x) = u x := by rw [← hu, hv]
  have hr (z : LinearMap.range Q) : u (v z.val) = z.val := by
    obtain ⟨y, hy⟩ := z.property
    rw [← hy, ← hu, hv]
  exact
    { toFun := fun x => ⟨u x, ⟨u x, hf x⟩⟩
      invFun := fun z => v z.val
      left_inv := hv
      right_inv := fun z => Subtype.ext (hr z)
      map_add' := fun x y => Subtype.ext (u.map_add x y)
      map_smul' := fun a x => Subtype.ext (u.map_smul a x)
      continuous_toFun := u.continuous.subtype_mk _
      continuous_invFun := v.continuous.comp continuous_subtype_val }

def ordinalTailProjectionRangeEquiv (α β : Ordinal.{u})
    (h : Order.succ β + α = α) :
    OrdinalC 𝕜 α ≃L[𝕜] LinearMap.range
      (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α) - ordinalHeadProjection α β) :=
  projectionRangeEquivOfRetraction (ordinalTailExtension α β) (ordinalTailRestriction α β h)
    (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α) - ordinalHeadProjection α β)
    (ordinalTailRestriction_extension α β h) (ordinalTailExtension_restriction α β h)

def initialOrdinalTailProjectionRangeEquiv {c : Cardinal.{u}} (hc : Cardinal.aleph0 ≤ c)
    {β : Ordinal.{u}} (hβ : β < c.ord) :
    OrdinalC 𝕜 c.ord ≃L[𝕜] LinearMap.range
      (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord) - ordinalHeadProjection c.ord β) :=
  ordinalTailProjectionRangeEquiv c.ord β (initialOrdinal_succ_add hc hβ)

end JLMS
