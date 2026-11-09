import NonCalkinAlgebra.QuotientIsoEquiv
import NonCalkinAlgebra.QuotientLinearMap
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe u v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem finiteDimensional_of_compact_identity
    (h : IsCompactOperator (1 : BoundedOperators X)) : FiniteDimensional ℂ X := by
  have hc := h.isCompact_closure_image_closedBall 1
  have heq : (1 : BoundedOperators X).toLinearMap '' Metric.closedBall (0 : X) 1 =
      Metric.closedBall (0 : X) 1 := by
    ext x
    simp only [Set.mem_image, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.one_apply, exists_eq_right]
  rw [heq, closure_eq_iff_isClosed.mpr Metric.isClosed_closedBall] at hc
  exact FiniteDimensional.of_isCompact_closedBall ℂ zero_lt_one hc

/-- The canonical bounded quotient map B(X)/A(X) → B(X)/K(X). -/
def approximableToCompact : OperatorQuotient X .approximable →L[ℂ]
    OperatorQuotient X .compact :=
  quotientLinearMap (operatorIdeal X .approximable) (operatorIdeal X .compact)
    (ContinuousLinearMap.id ℂ (BoundedOperators X))
    (fun T hT => operatorIdeal_le_compact X .approximable hT)

@[simp] theorem approximableToCompact_mk (T : BoundedOperators X) :
    approximableToCompact X (operatorQuotientMap X .approximable T) =
      operatorQuotientMap X .compact T := rfl

theorem approximableToCompact_mul (a b : OperatorQuotient X .approximable) :
    approximableToCompact X (a * b) =
      approximableToCompact X a * approximableToCompact X b := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  rfl

def approximableToCompactAlgHom : OperatorQuotient X .approximable →ₐ[ℂ]
    OperatorQuotient X .compact :=
  { (approximableToCompact X).toLinearMap with
    map_zero' := (approximableToCompact X).map_zero
    map_one' := rfl
    map_mul' := approximableToCompact_mul X
    commutes' := by
      intro c
      simp only [Algebra.algebraMap_eq_smul_one]
      change approximableToCompact X (c • 1) = c • 1
      rw [map_smul]
      rfl }

theorem approximableToCompact_surjective : Function.Surjective (approximableToCompact X) := by
  intro z
  obtain ⟨T, rfl⟩ := operatorQuotientMap_surjective X .compact z
  exact ⟨operatorQuotientMap X .approximable T, rfl⟩

variable {X} (D : Type u) [NormedRing D] [NormedAlgebra ℂ D]
  [Nontrivial D] [CompleteSpace D]

/-- The second half of Theorem 2.2: simplicity transfers an approximable
Calkin representation into a compact Calkin representation. The proof is
valid for any Banach space X, including the zero and finite-dimensional cases. -/
theorem simple_approximable_representation_implies_compact
    (hD : IsTopologicallySimple D) (iso : OperatorQuotientIso X .approximable D) :
    Nonempty (OperatorQuotientIso X .compact D) := by
  classical
  have hXinf : ¬ FiniteDimensional ℂ X := by
    intro hfin
    letI : FiniteDimensional ℂ X := hfin
    have hfinite : HasFiniteRank X (1 : BoundedOperators X) := by
      change FiniteDimensional ℂ (LinearMap.range (1 : BoundedOperators X).toLinearMap)
      infer_instance
    have hq0 := (operatorQuotientMap_eq_zero X .approximable 1).mpr
      (finiteRank_le_approximable X hfinite)
    have h := congrArg iso.toContinuousLinearEquiv hq0
    rw [iso.map_one_representative, map_zero] at h
    exact one_ne_zero h
  let g : D →ₐ[ℂ] OperatorQuotient X .compact :=
    (approximableToCompactAlgHom X).comp iso.toContinuousAlgEquiv.symm.toAlgEquiv.toAlgHom
  let f : D →L[ℂ] OperatorQuotient X .compact :=
    (approximableToCompact X).comp iso.toContinuousLinearEquiv.symm.toContinuousLinearMap
  have hfg (d : D) : f d = g d := rfl
  have hkerClosed : IsClosed (TwoSidedIdeal.ker g : Set D) := by
    have heq : (TwoSidedIdeal.ker g : Set D) = f ⁻¹' {0} := by
      ext d
      exact TwoSidedIdeal.mem_ker g
    rw [heq]
    exact isClosed_singleton.preimage f.continuous
  have hker : TwoSidedIdeal.ker g = ⊥ := by
    rcases hD (TwoSidedIdeal.ker g) hkerClosed with hz | ht
    · exact hz
    · have hone : (1 : D) ∈ TwoSidedIdeal.ker g := by rw [ht]; trivial
      have hz := (TwoSidedIdeal.mem_ker g).mp hone
      rw [_root_.map_one g] at hz
      have hcompact : IsCompactOperator (1 : BoundedOperators X) :=
        (operatorQuotientMap_eq_zero X .compact 1).mp hz
      exact False.elim (hXinf (finiteDimensional_of_compact_identity X hcompact))
  have hinj : Function.Injective f := by
    change Function.Injective g
    exact (TwoSidedIdeal.ker_eq_bot g).mp hker
  have hsurj : Function.Surjective f :=
    (approximableToCompact_surjective X).comp iso.toContinuousLinearEquiv.symm.surjective
  let l : D ≃L[ℂ] OperatorQuotient X .compact :=
    (LinearEquiv.ofBijective f.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquivOfContinuous
      f.continuous
  let e : D ≃A[ℂ] OperatorQuotient X .compact :=
    { toAlgEquiv := AlgEquiv.ofLinearEquiv l.toLinearEquiv (_root_.map_one g) (_root_.map_mul g)
      continuous_toFun := l.continuous
      continuous_invFun := l.symm.continuous }
  exact ⟨OperatorQuotientIso.ofContinuousAlgEquiv e.symm⟩

theorem simple_avoids_both_of_avoids_compact (hD : IsTopologicallySimple D)
    (h : ¬ Nonempty (OperatorQuotientIso X .compact D)) :
    ∀ convention : QuotientConvention, ¬ Nonempty (OperatorQuotientIso X convention D) := by
  intro convention
  cases convention
  · rintro ⟨iso⟩
    exact h (simple_approximable_representation_implies_compact D hD iso)
  · exact h

end NonCalkinAlgebra
