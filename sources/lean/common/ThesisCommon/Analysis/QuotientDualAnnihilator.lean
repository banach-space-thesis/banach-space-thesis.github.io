import ThesisCommon.Analysis.QuasiReflexiveDefinitions

/-! Continuous functionals on a genuine quotient identify with the
annihilator of the subspace. The inverse descends a continuous functional
through the actual quotient topology. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def quotientFunctional (S : Submodule 𝕜 E) (f : E →L[𝕜] 𝕜)
    (hf : S ≤ LinearMap.ker f.toLinearMap) : (E ⧸ S) →L[𝕜] 𝕜 where
  toLinearMap := S.liftQ f.toLinearMap hf
  cont := by
    apply S.isOpenQuotientMap_mkQ.continuous_comp_iff.mp
    exact f.continuous

@[simp] theorem quotientFunctional_mk (S : Submodule 𝕜 E) (f : E →L[𝕜] 𝕜)
    (hf : S ≤ LinearMap.ker f.toLinearMap) (x : E) :
    quotientFunctional S f hf (Submodule.Quotient.mk x) = f x := rfl

/-- The continuous dual of a quotient is the actual annihilator, represented
as the kernel of restriction to the subspace. -/
def quotientDualAnnihilatorEquiv (S : Submodule 𝕜 E) :
    StrongDual 𝕜 (E ⧸ S) ≃ₗ[𝕜]
      LinearMap.ker (banachAdjoint S.subtypeL).toLinearMap where
  toFun f := ⟨f.comp ⟨S.mkQ, continuous_quot_mk⟩, by
    apply ContinuousLinearMap.ext
    intro x
    change f (Submodule.Quotient.mk (p := S) x) = 0
    rw [(Submodule.Quotient.mk_eq_zero S).mpr x.property, map_zero]⟩
  invFun f := quotientFunctional S f.val (by
    intro x hx
    exact congrArg (fun g : S →L[𝕜] 𝕜 => g ⟨x, hx⟩) f.property)
  left_inv f := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using Quotient.inductionOn' with
    | h x => rfl
  right_inv f := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_add' f g := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_smul' a f := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl

/-- Range and kernel of a pair of split linear maps are complementary. -/
theorem range_isCompl_ker_of_rightInverse (r : F →L[𝕜] E) (s : E →L[𝕜] F)
    (h : Function.RightInverse s r) :
    IsCompl (LinearMap.range s.toLinearMap) (LinearMap.ker r.toLinearMap) := by
  constructor
  · rw [disjoint_iff_inf_le]
    rintro x ⟨⟨y, rfl⟩, hy⟩
    change r (s y) = 0 at hy
    have hy0 : y = 0 := (h y).symm.trans hy
    simp [hy0]
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨s (r x), ⟨r x, rfl⟩, x - s (r x), ?_, add_sub_cancel _ _⟩
    change r (x - s (r x)) = 0
    rw [map_sub, h, sub_self]

end ThesisCommon
