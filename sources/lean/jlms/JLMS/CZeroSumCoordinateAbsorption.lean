import JLMS.OrdinalSpaceSumAbsorption

/-!
# Absorbing a factor in one coordinate of a dependent c₀ sum

Unlike infinite constant-sum absorption, this construction works for any
nonempty index set and an arbitrary family of Banach spaces.
-/

noncomputable section
namespace JLMS
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜]

def coordinateHeadIndexEquiv {I : Type u} (i : I) :
    PUnit.{u + 1} ⊕ {j : I // j ≠ i} ≃ I := by
  classical
  exact {
    toFun := fun x => match x with | .inl _ => i | .inr j => j.val
    invFun := fun j => if h : j = i then .inl PUnit.unit else .inr ⟨j, h⟩
    left_inv := by
      intro x
      cases x with
      | inl x => cases x; simp
      | inr j => simp [j.prop]
    right_inv := by intro j; by_cases h : j = i <;> simp [h] }

def cZeroSumCoordinateHeadIsometry {I : Type u} (E : I → Type v)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (i : I) :
    CZeroSum 𝕜 E ≃ₗᵢ[𝕜] E i × CZeroSum 𝕜 (fun j : {j : I // j ≠ i} => E j.val) :=
  (CZeroSum.reindex (𝕜 := 𝕜) (E := E) (coordinateHeadIndexEquiv i)).trans
    (CZeroSum.sumIsometry.trans
      (linearIsometryEquivProdCongr (cZeroSumSingletonIsometry (E i))
        (LinearIsometryEquiv.refl 𝕜 _)))

def cZeroSumAbsorbsAt {I : Type u} (E : I → Type v)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (i : I) (e : (F × E i) ≃L[𝕜] E i) :
    (F × CZeroSum 𝕜 E) ≃L[𝕜] CZeroSum 𝕜 E :=
  let h := (cZeroSumCoordinateHeadIsometry (𝕜 := 𝕜) E i).toContinuousLinearEquiv
  ((ContinuousLinearEquiv.refl 𝕜 F).prodCongr h).trans
    ((ContinuousLinearEquiv.prodAssoc 𝕜 F (E i) _).symm.trans
      ((e.prodCongr (ContinuousLinearEquiv.refl 𝕜 _)).trans h.symm))

end JLMS
