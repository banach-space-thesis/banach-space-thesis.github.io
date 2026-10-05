import ThesisCommon.Analysis.GowersMaureyWienerCompletion
import ThesisCommon.Analysis.GowersMaureyStrictlySingularKernel

/-! The actual bounded linear Wiener representative map, conditional on the
explicit finite-spread approximation conclusion. The map is obtained from
the preceding completeness theorem, not included in the construction data.
Multiplicativity modulo the seminorm kernel remains a separate assertion. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def wienerRepresentativeCoefficients (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) : WienerSequences 𝕜 :=
  Classical.choose (happrox T).exists_unique_wiener_representative.exists

theorem wienerRepresentativeCoefficients_spec (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    spaceOperatorSeminorm D
      (T - laurentOperator D (wienerRepresentativeCoefficients D happrox T)) = 0 :=
  Classical.choose_spec (happrox T).exists_unique_wiener_representative.exists

theorem wienerRepresentativeCoefficients_norm (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    ‖wienerRepresentativeCoefficients D happrox T‖ = spaceOperatorSeminorm D T :=
  wiener_representative_norm D (wienerRepresentativeCoefficients_spec D happrox T)

def wienerRepresentativeLinear (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    (ShiftSpace D →L[𝕜] ShiftSpace D) →ₗ[𝕜] WienerSequences 𝕜 where
  toFun := wienerRepresentativeCoefficients D happrox
  map_add' S T := by
    apply wiener_representative_unique D (wienerRepresentativeCoefficients_spec D happrox (S+T))
    apply le_antisymm _ (apply_nonneg _ _)
    rw [map_add]
    have he : (S+T) -
        (laurentOperator D (wienerRepresentativeCoefficients D happrox S) +
          laurentOperator D (wienerRepresentativeCoefficients D happrox T)) =
        (S - laurentOperator D (wienerRepresentativeCoefficients D happrox S)) +
          (T - laurentOperator D (wienerRepresentativeCoefficients D happrox T)) := by abel
    rw [he]
    exact (map_add_le_add (spaceOperatorSeminorm D) _ _).trans_eq
      (by rw [wienerRepresentativeCoefficients_spec, wienerRepresentativeCoefficients_spec,
        zero_add])
  map_smul' c T := by
    apply wiener_representative_unique D (wienerRepresentativeCoefficients_spec D happrox (c•T))
    rw [map_smul, RingHom.id_apply, ← smul_sub, map_smul_eq_mul,
      wienerRepresentativeCoefficients_spec, mul_zero]

/-- A contractive linear map to literal absolutely summable integer sequences.
Its approximation hypothesis has not yet been discharged for arbitrary operators. -/
def wienerRepresentative (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    (ShiftSpace D →L[𝕜] ShiftSpace D) →L[𝕜] WienerSequences 𝕜 :=
  (wienerRepresentativeLinear D happrox).mkContinuous 1 (fun T => by
    change ‖wienerRepresentativeCoefficients D happrox T‖ ≤ 1 * ‖T‖
    rw [wienerRepresentativeCoefficients_norm, one_mul]
    exact spaceOperatorSeminorm_le_norm D T)

theorem wienerRepresentative_apply (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    wienerRepresentative D happrox T = wienerRepresentativeCoefficients D happrox T := rfl

theorem wienerRepresentative_spec (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    spaceOperatorSeminorm D (T - laurentOperator D (wienerRepresentative D happrox T)) = 0 :=
  wienerRepresentativeCoefficients_spec D happrox T

theorem wienerRepresentative_norm (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    ‖wienerRepresentative D happrox T‖ = spaceOperatorSeminorm D T :=
  wienerRepresentativeCoefficients_norm D happrox T

theorem norm_wienerRepresentative_le (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    ‖wienerRepresentative D happrox‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  rw [wienerRepresentative_norm, one_mul]
  exact spaceOperatorSeminorm_le_norm D T

theorem wienerRepresentative_eq_of_error_zero (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    {T : ShiftSpace D →L[𝕜] ShiftSpace D} {a : WienerSequences 𝕜}
    (ha : spaceOperatorSeminorm D (T - laurentOperator D a) = 0) :
    wienerRepresentative D happrox T = a :=
  wiener_representative_unique D (wienerRepresentative_spec D happrox T) ha

@[simp] theorem wienerRepresentative_laurentOperator (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (a : WienerSequences 𝕜) : wienerRepresentative D happrox (laurentOperator D a) = a := by
  apply wienerRepresentative_eq_of_error_zero D happrox
  rw [sub_self, map_zero]

theorem wienerRepresentative_comp_laurentOperator (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    (wienerRepresentative D happrox).comp (laurentOperator D) =
      ContinuousLinearMap.id 𝕜 (WienerSequences 𝕜) := by
  apply ContinuousLinearMap.ext
  intro a
  exact wienerRepresentative_laurentOperator D happrox a

theorem wienerRepresentative_surjective (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    Function.Surjective (wienerRepresentative D happrox) :=
  fun a => ⟨laurentOperator D a, wienerRepresentative_laurentOperator D happrox a⟩

theorem wienerRepresentative_eq_zero_iff (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    wienerRepresentative D happrox T = 0 ↔ spaceOperatorSeminorm D T = 0 := by
  rw [← wienerRepresentative_norm D happrox T, norm_eq_zero]

theorem wienerRepresentative_error_strictlySingular (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    IsStrictlySingularOperator (T - laurentOperator D (wienerRepresentative D happrox T)) :=
  isStrictlySingularOperator_of_spaceOperatorSeminorm_zero D _
    (wienerRepresentative_spec D happrox T)

end ThesisCommon.GowersMaurey
