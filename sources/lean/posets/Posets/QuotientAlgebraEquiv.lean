import Posets.QuotientAlgebra

noncomputable section
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {C : Type*} [Ring C] [Algebra 𝕜 C]

/-- Testing products on arbitrary operator representatives is equivalent to
multiplicativity on the entire quotient algebra. -/
theorem isMultiplicative_quotient_iff (f : SeparableQuotient 𝕜 E →ₗ[𝕜] C) :
    IsMultiplicative 𝕜 f ↔
      ∀ S T : E →L[𝕜] E, f (quotientMap 𝕜 E (S * T)) =
        f (quotientMap 𝕜 E S) * f (quotientMap 𝕜 E T) := by
  constructor
  · intro h S T
    simpa only [quotientMap_mul] using h (quotientMap 𝕜 E S) (quotientMap 𝕜 E T)
  · intro h a b
    obtain ⟨S, rfl⟩ := quotientMap_surjective 𝕜 E a
    obtain ⟨T, rfl⟩ := quotientMap_surjective 𝕜 E b
    simpa only [quotientMap_mul] using h S T

/-- In particular, the representative-based algebra isomorphism used in
Corollary 1.7 is an actual bundled algebra equivalence, with the same linear map. -/
def quotientAlgEquivOfRepresentatives (e : SeparableQuotient 𝕜 E ≃ₗ[𝕜] C)
    (h : ∀ S T : E →L[𝕜] E, e (quotientMap 𝕜 E (S * T)) =
      e (quotientMap 𝕜 E S) * e (quotientMap 𝕜 E T)) :
    SeparableQuotient 𝕜 E ≃ₐ[𝕜] C := by
  have hm := (isMultiplicative_quotient_iff e.toLinearMap).mpr h
  have h1 : e 1 = 1 := by
    obtain ⟨a, ha⟩ := e.surjective 1
    have he := hm 1 a
    change e (1 * a) = e 1 * e a at he
    simpa only [one_mul, ha, mul_one] using he.symm
  exact AlgEquiv.ofLinearEquiv e h1 hm

@[simp] theorem quotientAlgEquivOfRepresentatives_apply
    (e : SeparableQuotient 𝕜 E ≃ₗ[𝕜] C)
    (h : ∀ S T : E →L[𝕜] E, e (quotientMap 𝕜 E (S * T)) =
      e (quotientMap 𝕜 E S) * e (quotientMap 𝕜 E T)) (x : SeparableQuotient 𝕜 E) :
    quotientAlgEquivOfRepresentatives e h x = e x := rfl

end Posets
