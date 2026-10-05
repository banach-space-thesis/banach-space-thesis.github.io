import ThesisCommon.Analysis.WienerProjectionDichotomy
import ThesisCommon.Analysis.HyperplaneFiniteCodimension
import ThesisCommon.Analysis.GowersMaureyHyperplanes
import ThesisCommon.Analysis.GowersMaureyInfiniteDimensional

/-! The prime-space consequence of the genuine Wiener quotient, retaining
that explicitly open premise. Actual hyperplane isomorphisms discharge all
finite-codimension inputs for the shift-generated Gowers--Maurey space. -/
noncomputable section
namespace ThesisCommon
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem IsIsomorphicToEveryHyperplane.isPrime_of_wienerQuotient
    (hX : IsIsomorphicToEveryHyperplane ℂ X)
    (hW : HasStrictlySingularWienerQuotient ℂ X) : IsPrimeBanachSpace ℂ X := by
  intro P hP hInf
  rcases hW.projection_finite_or_finiteComplement P hP with hFin | hComp
  · exact False.elim (hInf hFin)
  · let E := LinearMap.range P.toLinearMap
    let Q := ContinuousLinearMap.id ℂ X - P
    letI : FiniteDimensional ℂ (LinearMap.range Q.toLinearMap) := hComp
    have hker : LinearMap.ker Q.toLinearMap = E := by
      ext x
      change x - P x = 0 ↔ ∃ y, P y = x
      constructor
      · intro hx
        exact ⟨x, (sub_eq_zero.mp hx).symm⟩
      · rintro ⟨y, rfl⟩
        have hp := DFunLike.congr_fun hP y
        change P (P y) = P y at hp
        rw [hp, sub_self]
    haveI : FiniteDimensional ℂ (X ⧸ E) := by
      have e := Q.toLinearMap.quotKerEquivRange
      rw [hker] at e
      exact FiniteDimensional.of_injective e.toLinearMap e.injective
    exact hX.finiteCodimension E (projectionRange_isClosed P hP)

theorem GowersMaurey.shiftSpace_prime_of_wienerQuotient
    (D : GowersMaurey.ConstructionData ℂ)
    (hW : HasStrictlySingularWienerQuotient ℂ (GowersMaurey.ShiftSpace D)) :
    IsPrimeBanachSpace ℂ (GowersMaurey.ShiftSpace D) :=
  (GowersMaurey.shiftSpace_everyHyperplane D).isPrime_of_wienerQuotient hW

theorem GowersMaurey.shiftSpace_primary_of_wienerQuotient
    (D : GowersMaurey.ConstructionData ℂ)
    (hW : HasStrictlySingularWienerQuotient ℂ (GowersMaurey.ShiftSpace D)) :
    IsPrimary ℂ (GowersMaurey.ShiftSpace D) :=
  (GowersMaurey.shiftSpace_prime_of_wienerQuotient D hW).isPrimary
    (GowersMaurey.shiftSpace_infiniteDimensional D)

end ThesisCommon
