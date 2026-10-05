import ThesisCommon.Analysis.WienerQuotientPrimeness

/-! Projection and primeness consequences of an actual unital Wiener map.
Only its zero kernel being strictly singular is needed for these conclusions;
the reverse kernel inclusion is a separate theorem. -/
noncomputable section
namespace ThesisCommon
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem strictlySingular_projection_or_complement_of_wiener_map_kernel_le
    (q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ)
    (hker : ∀ T, q T = 0 → IsStrictlySingularOperator T)
    (hunit : q (ContinuousLinearMap.id ℂ X) = lp.single 1 0 1)
    (hmul : ∀ S T, q (S.comp T) = wienerConvolution (q S) (q T))
    (P : X →L[ℂ] X) (hP : P.comp P = P) :
    IsStrictlySingularOperator P ∨
      IsStrictlySingularOperator (ContinuousLinearMap.id ℂ X - P) := by
  have hi : wienerConvolution (q P) (q P) = q P := by rw [← hmul, hP]
  rcases (wienerConvolution_idempotent_iff (q P)).mp hi with h0 | h1
  · exact Or.inl (hker P h0)
  · right
    apply hker
    rw [map_sub, hunit, h1, sub_self]

theorem projection_finite_or_finiteComplement_of_wiener_map_kernel_le
    (q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ)
    (hker : ∀ T, q T = 0 → IsStrictlySingularOperator T)
    (hunit : q (ContinuousLinearMap.id ℂ X) = lp.single 1 0 1)
    (hmul : ∀ S T, q (S.comp T) = wienerConvolution (q S) (q T))
    (P : X →L[ℂ] X) (hP : P.comp P = P) :
    FiniteDimensional ℂ (LinearMap.range P.toLinearMap) ∨
      FiniteDimensional ℂ
        (LinearMap.range (ContinuousLinearMap.id ℂ X - P).toLinearMap) := by
  rcases strictlySingular_projection_or_complement_of_wiener_map_kernel_le
    q hker hunit hmul P hP with hp | hc
  · exact Or.inl ((isStrictlySingularOperator_projection_iff_finiteDimensional_range P hP).mp hp)
  · exact Or.inr ((isStrictlySingularOperator_projection_iff_finiteDimensional_range
      _ (complementary_projection hP)).mp hc)

theorem IsIsomorphicToEveryHyperplane.isPrime_of_wienerMap
    (hX : IsIsomorphicToEveryHyperplane ℂ X)
    (q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ)
    (hker : ∀ T, q T = 0 → IsStrictlySingularOperator T)
    (hunit : q (ContinuousLinearMap.id ℂ X) = lp.single 1 0 1)
    (hmul : ∀ S T, q (S.comp T) = wienerConvolution (q S) (q T)) :
    IsPrimeBanachSpace ℂ X := by
  intro P hP hInf
  rcases projection_finite_or_finiteComplement_of_wiener_map_kernel_le
    q hker hunit hmul P hP with hFin | hComp
  · exact False.elim (hInf hFin)
  · let E := LinearMap.range P.toLinearMap
    let Q := ContinuousLinearMap.id ℂ X - P
    letI : FiniteDimensional ℂ (LinearMap.range Q.toLinearMap) := hComp
    have hkerQ : LinearMap.ker Q.toLinearMap = E := by
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
      rw [hkerQ] at e
      exact FiniteDimensional.of_injective e.toLinearMap e.injective
    exact hX.finiteCodimension E (projectionRange_isClosed P hP)

end ThesisCommon
