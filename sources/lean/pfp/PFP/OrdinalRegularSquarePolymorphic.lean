import ThesisCommon.Analysis.PrimaryIsomorphism
import PFP.OrdinalMatrixMatrixSelection
import PFP.OrdinalInitialQuotientPolymorphic

/-! Uniform primary factorisation at the regular-cardinal square. The
scalar jump operator supplies a large independent diagonal, while matched
ordinal selectors remove all remaining operator-valued matrix entries. -/
noncomputable section
namespace Posets.UniverseRegularMatrix
universe ordU
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

local instance regularSquareSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance regularSquareSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance

theorem regularOrdinalSum_factorsIdentityWith_of_large_jump
    {c : Cardinal.{ordU}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord))
    (S : Set c.ord.toType) (hS : Cardinal.mk c.ord.toType ≤ Cardinal.mk S)
    (hdiag : ∀ i ∈ S, (1 : ℝ) / 2 ≤ ‖regularOrdinalBlockJump hc hu T i i‖) :
    FactorsIdentityWith T (CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord)) 16 := by
  let A := regularOrdinalJumpOperator hc hu T
  have hI : Cardinal.aleph0 < Cardinal.mk c.ord.toType := by
    simpa only [Cardinal.mk_toType, Cardinal.card_ord] using hu
  obtain ⟨e, heS, he⟩ := exists_uncountable_independent_embedding hI S hS
    (cZeroSumMatrixForbidden A) (cZeroSumMatrixForbidden_countable A)
    (cZeroSumMatrixForbidden_self A) (cZeroSumMatrixForbidden_symm A)
  apply regularOrdinalSum_factorsIdentityWith_of_selected_jump hc hu T e (fun i => hdiag _ (heS i))
  intro i j hij
  have hm : cZeroSumScalarMatrix A (e i) (e j) = regularOrdinalBlockJump hc hu T (e i) (e j) :=
    regularOrdinalJumpOperator_single hc hu T (e i) (e j)
  rw [← hm]
  by_contra hn
  exact he i j hij (Or.inr hn)

theorem fullRepeatedRegularOrdinal_hasCPFP_sixteen
    {c : Cardinal.{ordU}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) :
    HasCPFP 𝕜 (CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord)) 16 := by
  classical
  have hI : Cardinal.aleph0 < Cardinal.mk c.ord.toType := by
    simpa only [Cardinal.mk_toType, Cardinal.card_ord] using hu
  letI : Uncountable c.ord.toType := Cardinal.aleph0_lt_mk_iff.mp hI
  intro T
  let S : Set c.ord.toType := {i | (1 : ℝ) / 2 ≤ ‖regularOrdinalBlockJump hc hu T i i‖}
  rcases infinite_twoColor_large c.ord.toType S with hS | hS
  · exact Or.inl (regularOrdinalSum_factorsIdentityWith_of_large_jump hc hu T S hS (fun _ hi => hi))
  · right
    apply regularOrdinalSum_factorsIdentityWith_of_large_jump hc hu
      (ContinuousLinearMap.id 𝕜 _ - T) Sᶜ hS
    intro i hi
    have hn : ¬ (1 : ℝ) / 2 ≤ ‖regularOrdinalBlockJump hc hu T i i‖ := hi
    have hmatrix : regularOrdinalBlockJump hc hu (ContinuousLinearMap.id 𝕜 _ - T) i i =
        1 - regularOrdinalBlockJump hc hu T i i := by
      rw [← regularOrdinalJumpOperator_single hc hu _ i i,
        regularOrdinalJumpOperator_sub, regularOrdinalJumpOperator_id]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
        CZeroSum.sub_apply, CZeroSum.single_apply_self, regularOrdinalJumpOperator_single]
    rw [hmatrix]
    have hh := norm_add_le (regularOrdinalBlockJump hc hu T i i)
      (1 - regularOrdinalBlockJump hc hu T i i)
    rw [add_sub_cancel, norm_one] at hh
    linarith

theorem fullRepeatedRegularOrdinal_hasUPFP
    {c : Cardinal.{ordU}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) :
    HasUPFP 𝕜 (CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord)) :=
  ⟨16, by norm_num, fullRepeatedRegularOrdinal_hasCPFP_sixteen hc hu⟩

/-- The actual square is identified with its full constant ordinal block sum. -/
def initialOrdinalSquareSumEquiv {c : Cardinal.{ordU}} (hu : Cardinal.aleph0 < c) :
    OrdinalC 𝕜 (c.ord * c.ord) ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord) := by
  have hκ : Ordinal.omega0 ≤ c.ord := Cardinal.omega0_le_ord.mpr hu.le
  have heq : c.ord * c.ord / c.ord = c.ord :=
    Ordinal.mul_div_cancel _ (ne_of_gt (Ordinal.omega0_pos.trans_le hκ))
  have e := Posets.UniverseInitialQuotient.initialOrdinalInfiniteQuotientSumEquiv
    (𝕜 := 𝕜) hu (c.ord * c.ord) (mul_le_mul_left' hκ _) le_rfl
  rw [heq] at e
  exact e

theorem regularInitialSquare_hasUPFP
    {c : Cardinal.{ordU}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) :
    HasUPFP 𝕜 (OrdinalC 𝕜 (c.ord * c.ord)) :=
  (fullRepeatedRegularOrdinal_hasUPFP (𝕜 := 𝕜) hc hu).of_equiv (initialOrdinalSquareSumEquiv hu).symm

end Posets.UniverseRegularMatrix



