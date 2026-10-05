import ThesisCommon.Analysis.WienerQuotientObstruction
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Real.Cardinality

/-! Unit-circle evaluations give distinct maximal two-sided operator ideals
whenever an actual surjective unital convolution quotient map is supplied.
Only the lower cardinal bound follows here: no classification of all maximal
ideals, nor any quotient property of the Gowers--Maurey space, is assumed.
-/
noncomputable section
namespace ThesisCommon

theorem isCoatom_twoSidedIdeal_ker_of_surjective
    {R K : Type*} [Ring R] [Field K] (φ : R →+* K)
    (hφ : Function.Surjective φ) : IsCoatom (TwoSidedIdeal.ker φ) := by
  refine isCoatom_iff_ge_of_le.mpr ⟨?_, ?_⟩
  · intro htop
    have h := (TwoSidedIdeal.ker φ).one_mem htop
    have hone : (1 : K) = 0 := (map_one φ).symm.trans ((TwoSidedIdeal.mem_ker φ).mp h)
    exact one_ne_zero hone
  · intro J hJ hle x hx
    by_contra hn
    have hn' : φ x ≠ 0 := fun h => hn ((TwoSidedIdeal.mem_ker φ).mpr h)
    obtain ⟨y, hy⟩ := hφ ((φ x)⁻¹)
    have hker : 1 - y * x ∈ TwoSidedIdeal.ker φ := by
      apply (TwoSidedIdeal.mem_ker φ).mpr
      simp [hy, hn']
    have hone : (1 : R) ∈ J := by
      simpa using J.add_mem (hle hker) (J.mul_mem_left y x hx)
    exact hJ (J.eq_top hone)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem operatorWienerCharacter_surjective
    (q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ)
    (hunit : q (ContinuousLinearMap.id ℂ X) = lp.single 1 0 1)
    (hmul : ∀ S T, q (S.comp T) = wienerConvolution (q S) (q T))
    (z : Circle) : Function.Surjective (operatorWienerCharacter q hunit hmul z) := by
  intro c
  refine ⟨c • (1 : X →L[ℂ] X), ?_⟩
  simp

def operatorWienerMaximalIdeal
    (q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ)
    (hunit : q (ContinuousLinearMap.id ℂ X) = lp.single 1 0 1)
    (hmul : ∀ S T, q (S.comp T) = wienerConvolution (q S) (q T))
    (z : Circle) : {J : TwoSidedIdeal (X →L[ℂ] X) // IsCoatom J} :=
  ⟨TwoSidedIdeal.ker (operatorWienerCharacter q hunit hmul z),
    isCoatom_twoSidedIdeal_ker_of_surjective
      (operatorWienerCharacter q hunit hmul z).toRingHom
      (operatorWienerCharacter_surjective q hunit hmul z)⟩

theorem operatorWienerMaximalIdeal_injective
    (q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ) (hq : Function.Surjective q)
    (hunit : q (ContinuousLinearMap.id ℂ X) = lp.single 1 0 1)
    (hmul : ∀ S T, q (S.comp T) = wienerConvolution (q S) (q T)) :
    Function.Injective (operatorWienerMaximalIdeal q hunit hmul) := by
  intro z w hzw
  obtain ⟨T, hT⟩ := hq (lp.single 1 1 1 - (z : ℂ) • lp.single 1 0 1)
  have hz : T ∈ (operatorWienerMaximalIdeal q hunit hmul z).val := by
    change T ∈ TwoSidedIdeal.ker (operatorWienerCharacter q hunit hmul z)
    rw [TwoSidedIdeal.mem_ker, operatorWienerCharacter_apply, hT]
    simp
  rw [hzw] at hz
  change T ∈ TwoSidedIdeal.ker (operatorWienerCharacter q hunit hmul w) at hz
  rw [TwoSidedIdeal.mem_ker, operatorWienerCharacter_apply, hT] at hz
  have heq : (w : ℂ) - (z : ℂ) = 0 := by simpa using hz
  exact Subtype.ext (sub_eq_zero.mp heq).symm

theorem cardinal_circle_eq_continuum : Cardinal.mk Circle = Cardinal.continuum := by
  rw [Cardinal.mk_congr Circle.argEquiv]
  exact Cardinal.mk_Ioc_real (by linarith [Real.pi_pos])

theorem continuum_le_maximalIdeals_of_wiener_quotient_map
    (q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ) (hq : Function.Surjective q)
    (hunit : q (ContinuousLinearMap.id ℂ X) = lp.single 1 0 1)
    (hmul : ∀ S T, q (S.comp T) = wienerConvolution (q S) (q T)) :
    Cardinal.continuum ≤ Cardinal.mk {J : TwoSidedIdeal (X →L[ℂ] X) // IsCoatom J} := by
  have h := Cardinal.lift_mk_le_lift_mk_of_injective
    (operatorWienerMaximalIdeal_injective q hq hunit hmul)
  simpa [cardinal_circle_eq_continuum] using h

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem HasStrictlySingularWienerQuotient.continuum_le_maximalIdeals
    (h : HasStrictlySingularWienerQuotient ℂ X) :
    Cardinal.continuum ≤ Cardinal.mk {J : TwoSidedIdeal (X →L[ℂ] X) // IsCoatom J} := by
  obtain ⟨J, _, hclosed, e, heunit, hemul⟩ := h
  letI : IsClosed (operatorIdealSubmodule J : Set (X →L[ℂ] X)) := hclosed
  let q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ :=
    e.toLinearMap.comp (operatorIdealSubmodule J).mkQ
  apply continuum_le_maximalIdeals_of_wiener_quotient_map q
    (e.surjective.comp (operatorIdealSubmodule J).mkQ_surjective) heunit
  intro S T
  apply lp.ext
  funext n
  exact hemul S T n

end ThesisCommon
