import ThesisCommon.Analysis.WienerIdempotents
import ThesisCommon.Analysis.StrictlySingularFiniteRank
import ThesisCommon.Analysis.PrimaryDirectSum

/-! The projection consequence of a genuine strictly-singular Wiener
quotient. The quotient hypothesis remains explicit; these results do not
establish the still-open quotient of the actual Gowers--Maurey space. -/
noncomputable section
namespace ThesisCommon
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem strictlySingular_projection_or_complement_of_wiener_map
    (q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ)
    (hker : ∀ T, q T = 0 ↔ IsStrictlySingularOperator T)
    (hunit : q (ContinuousLinearMap.id ℂ X) = lp.single 1 0 1)
    (hmul : ∀ S T, q (S.comp T) = wienerConvolution (q S) (q T))
    (P : X →L[ℂ] X) (hP : P.comp P = P) :
    IsStrictlySingularOperator P ∨
      IsStrictlySingularOperator (ContinuousLinearMap.id ℂ X - P) := by
  have hi : wienerConvolution (q P) (q P) = q P := by rw [← hmul, hP]
  rcases (wienerConvolution_idempotent_iff (q P)).mp hi with h0 | h1
  · exact Or.inl ((hker P).mp h0)
  · right
    apply (hker _).mp
    rw [map_sub, hunit, h1, sub_self]

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem HasStrictlySingularWienerQuotient.strictlySingular_projection_or_complement
    (h : HasStrictlySingularWienerQuotient ℂ X)
    (P : X →L[ℂ] X) (hP : P.comp P = P) :
    IsStrictlySingularOperator P ∨
      IsStrictlySingularOperator (ContinuousLinearMap.id ℂ X - P) := by
  obtain ⟨J, hJ, hclosed, e, heunit, hemul⟩ := h
  letI : IsClosed (operatorIdealSubmodule J : Set (X →L[ℂ] X)) := hclosed
  let q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ :=
    e.toLinearMap.comp (operatorIdealSubmodule J).mkQ
  apply strictlySingular_projection_or_complement_of_wiener_map q ?_ heunit ?_ P hP
  · intro T
    change e ((operatorIdealSubmodule J).mkQ T) = 0 ↔ IsStrictlySingularOperator T
    rw [e.map_eq_zero_iff]
    change Submodule.Quotient.mk T = 0 ↔ IsStrictlySingularOperator T
    rw [Submodule.Quotient.mk_eq_zero]
    exact hJ T
  · intro S T
    apply lp.ext
    funext n
    exact hemul S T n

theorem HasStrictlySingularWienerQuotient.projection_finite_or_finiteComplement
    (h : HasStrictlySingularWienerQuotient ℂ X)
    (P : X →L[ℂ] X) (hP : P.comp P = P) :
    FiniteDimensional ℂ (LinearMap.range P.toLinearMap) ∨
      FiniteDimensional ℂ
        (LinearMap.range (ContinuousLinearMap.id ℂ X - P).toLinearMap) := by
  rcases h.strictlySingular_projection_or_complement P hP with hp | hc
  · exact Or.inl ((isStrictlySingularOperator_projection_iff_finiteDimensional_range P hP).mp hp)
  · exact Or.inr ((isStrictlySingularOperator_projection_iff_finiteDimensional_range
      _ (complementary_projection hP)).mp hc)

end ThesisCommon
