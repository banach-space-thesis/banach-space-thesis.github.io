import ThesisCommon.Analysis.GowersMaureySeminormIdeal
import ThesisCommon.Analysis.QuotientContractions

/-! The genuine normed quotient by the closed zero-block-seminorm ideal is
linearly isometric to literal Wiener sequences, under explicit finite-spread
approximation. This does not identify the ideal with all strictly singular
operators. The inverse is the quotient class of actual Laurent synthesis. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev SpaceOperatorSeminormQuotient (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :=
  (ShiftSpace D →L[𝕜] ShiftSpace D) ⧸ operatorIdealSubmodule (spaceOperatorSeminormIdeal D happrox)

instance spaceOperatorSeminormQuotient_normedAddCommGroup (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    NormedAddCommGroup (SpaceOperatorSeminormQuotient D happrox) := inferInstance

instance spaceOperatorSeminormQuotient_normedSpace (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    NormedSpace 𝕜 (SpaceOperatorSeminormQuotient D happrox) := inferInstance

instance spaceOperatorSeminormQuotient_completeSpace (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    CompleteSpace (SpaceOperatorSeminormQuotient D happrox) := inferInstance

def wienerQuotientMap (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    SpaceOperatorSeminormQuotient D happrox →L[𝕜] WienerSequences 𝕜 :=
  quotientLiftL (operatorIdealSubmodule (spaceOperatorSeminormIdeal D happrox))
    (wienerRepresentative D happrox) (by
      intro T hT
      exact (wienerRepresentative_eq_zero_iff D happrox T).mpr
        ((mem_spaceOperatorSeminormIdeal D happrox T).mp hT))

@[simp] theorem wienerQuotientMap_mk (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    wienerQuotientMap D happrox (Submodule.Quotient.mk T) = wienerRepresentative D happrox T := rfl

theorem norm_wienerQuotientMap_le (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    ‖wienerQuotientMap D happrox‖ ≤ 1 :=
  (norm_quotientLiftL_le _ _ _).trans (norm_wienerRepresentative_le D happrox)

def wienerQuotientSection (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    WienerSequences 𝕜 →L[𝕜] SpaceOperatorSeminormQuotient D happrox :=
  (quotientMkL (operatorIdealSubmodule (spaceOperatorSeminormIdeal D happrox))).comp (laurentOperator D)

theorem wienerQuotientSection_apply (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (a : WienerSequences 𝕜) :
    wienerQuotientSection D happrox a = Submodule.Quotient.mk (laurentOperator D a) := rfl

theorem wienerQuotientSection_norm_le (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (a : WienerSequences 𝕜) : ‖wienerQuotientSection D happrox a‖ ≤ ‖a‖ := by
  rw [wienerQuotientSection_apply, ← norm_laurentOperator_eq D a]
  exact Submodule.Quotient.norm_mk_le _ _

theorem wienerQuotientMap_section (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (a : WienerSequences 𝕜) :
    wienerQuotientMap D happrox (wienerQuotientSection D happrox a) = a := by
  rw [wienerQuotientSection_apply, wienerQuotientMap_mk, wienerRepresentative_laurentOperator]

theorem wienerQuotientSection_map (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (x : SpaceOperatorSeminormQuotient D happrox) :
    wienerQuotientSection D happrox (wienerQuotientMap D happrox x) = x := by
  induction x using Quotient.inductionOn' with
  | h T =>
    change wienerQuotientSection D happrox
      (wienerQuotientMap D happrox (Submodule.Quotient.mk T)) = Submodule.Quotient.mk T
    rw [wienerQuotientMap_mk, wienerQuotientSection_apply]
    apply Eq.symm
    apply (Submodule.Quotient.eq _).mpr
    exact (mem_spaceOperatorSeminormIdeal D happrox _).mpr (wienerRepresentative_spec D happrox T)

theorem wienerQuotientMap_norm (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (x : SpaceOperatorSeminormQuotient D happrox) : ‖wienerQuotientMap D happrox x‖ = ‖x‖ := by
  apply le_antisymm
  · exact ((wienerQuotientMap D happrox).le_opNorm x).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (norm_wienerQuotientMap_le D happrox) (norm_nonneg x))
  · have h := wienerQuotientSection_norm_le D happrox (wienerQuotientMap D happrox x)
    rwa [wienerQuotientSection_map] at h

/-- Isometry for mathlib's genuine quotient norm, with explicit Laurent inverse. -/
def wienerQuotientIsometryEquiv (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    SpaceOperatorSeminormQuotient D happrox ≃ₗᵢ[𝕜] WienerSequences 𝕜 :=
  { (wienerQuotientMap D happrox).toLinearMap with
    invFun := wienerQuotientSection D happrox
    left_inv := wienerQuotientSection_map D happrox
    right_inv := wienerQuotientMap_section D happrox
    norm_map' := wienerQuotientMap_norm D happrox }

@[simp] theorem wienerQuotientIsometryEquiv_mk (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    wienerQuotientIsometryEquiv D happrox (Submodule.Quotient.mk T) =
      wienerRepresentative D happrox T := rfl

theorem wienerQuotientIsometryEquiv_symm_apply (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (a : WienerSequences 𝕜) :
    (wienerQuotientIsometryEquiv D happrox).symm a =
      Submodule.Quotient.mk (laurentOperator D a) := rfl

theorem spaceOperatorSeminormQuotient_norm_mk (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    ‖(Submodule.Quotient.mk T : SpaceOperatorSeminormQuotient D happrox)‖ =
      spaceOperatorSeminorm D T := by
  rw [← wienerQuotientMap_norm D happrox, wienerQuotientMap_mk, wienerRepresentative_norm]

theorem wienerQuotientIsometryEquiv_unit (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    wienerQuotientIsometryEquiv D happrox
      (Submodule.Quotient.mk (ContinuousLinearMap.id 𝕜 (ShiftSpace D))) = lp.single 1 0 1 :=
  wienerRepresentative_id D happrox

theorem wienerQuotientIsometryEquiv_comp (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (S T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    wienerQuotientIsometryEquiv D happrox (Submodule.Quotient.mk (S.comp T)) =
      wienerConvolution
        (wienerQuotientIsometryEquiv D happrox (Submodule.Quotient.mk S))
        (wienerQuotientIsometryEquiv D happrox (Submodule.Quotient.mk T)) :=
  wienerRepresentative_comp D happrox S T

end ThesisCommon.GowersMaurey
