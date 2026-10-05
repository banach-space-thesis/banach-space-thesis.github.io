import ThesisCommon.Analysis.WienerCharacters

/-! The Wiener quotient obstruction to PFP. This proves a consequence of
the actual quotient specification; it does not assume or prove that the
Gowers--Maurey space has that quotient. The two scalar characters detect
failure of both branches of the factorisation dichotomy.
-/
noncomputable section
namespace ThesisCommon
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def operatorWienerCharacter (q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ)
    (hunit : q (ContinuousLinearMap.id ℂ X) = lp.single 1 0 1)
    (hmul : ∀ S T, q (S.comp T) = wienerConvolution (q S) (q T))
    (z : Circle) : (X →L[ℂ] X) →ₐ[ℂ] ℂ :=
  AlgHom.ofLinearMap ((wienerEvaluate z).toLinearMap.comp q)
    (by change wienerEvaluate z (q (ContinuousLinearMap.id ℂ X)) = 1; simp [hunit])
    (by
      intro S T
      change wienerEvaluate z (q (S.comp T)) = _
      rw [hmul, wienerEvaluate_convolution]
      rfl)

theorem operatorWienerCharacter_apply (q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ)
    (hunit : q (ContinuousLinearMap.id ℂ X) = lp.single 1 0 1)
    (hmul : ∀ S T, q (S.comp T) = wienerConvolution (q S) (q T))
    (z : Circle) (T : X →L[ℂ] X) :
    operatorWienerCharacter q hunit hmul z T = wienerEvaluate z (q T) := rfl

theorem not_factorsIdentity_of_character_zero (φ : (X →L[ℂ] X) →ₐ[ℂ] ℂ)
    (T : X →L[ℂ] X) (hT : φ T = 0) : ¬ FactorsIdentity T X := by
  rintro ⟨U, V, hUV⟩
  have h := congrArg φ hUV
  change φ (U * T * V) = φ 1 at h
  rw [map_mul, map_mul, map_one, hT, mul_zero, zero_mul] at h
  exact zero_ne_one h

theorem not_hasPFP_of_wiener_quotient_map
    (q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ) (hq : Function.Surjective q)
    (hunit : q (ContinuousLinearMap.id ℂ X) = lp.single 1 0 1)
    (hmul : ∀ S T, q (S.comp T) = wienerConvolution (q S) (q T)) : ¬ HasPFP ℂ X := by
  let a : WienerSequences ℂ := (1 / 2 : ℂ) • (lp.single 1 0 1 - lp.single 1 1 1)
  obtain ⟨T, hT⟩ := hq a
  let φ := operatorWienerCharacter q hunit hmul (1 : Circle)
  let ψ := operatorWienerCharacter q hunit hmul (Circle.exp Real.pi)
  have hφ : φ T = 0 := by
    change wienerEvaluate 1 (q T) = 0
    rw [hT]
    simp [a]
  have hψ : ψ T = 1 := by
    change wienerEvaluate (Circle.exp Real.pi) (q T) = 1
    rw [hT]
    simp [a, Circle.coe_exp, Complex.exp_pi_mul_I]
    norm_num
  have hψ' : ψ (ContinuousLinearMap.id ℂ X - T) = 0 := by
    change ψ (1 - T) = 0
    rw [map_sub, map_one, hψ, sub_self]
  intro h
  rcases h T with h | h
  · exact not_factorsIdentity_of_character_zero φ T hφ h
  · exact not_factorsIdentity_of_character_zero ψ _ hψ' h

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
/-- The actual strictly-singular/Wiener quotient forces failure of PFP. -/
theorem HasStrictlySingularWienerQuotient.not_hasPFP
    (h : HasStrictlySingularWienerQuotient ℂ X) : ¬ HasPFP ℂ X := by
  obtain ⟨J, _, hclosed, e, heunit, hemul⟩ := h
  letI : IsClosed (operatorIdealSubmodule J : Set (X →L[ℂ] X)) := hclosed
  let q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ :=
    e.toLinearMap.comp (operatorIdealSubmodule J).mkQ
  apply not_hasPFP_of_wiener_quotient_map q
    (e.surjective.comp (operatorIdealSubmodule J).mkQ_surjective) heunit
  intro S T
  apply lp.ext
  funext n
  exact hemul S T n

end ThesisCommon
