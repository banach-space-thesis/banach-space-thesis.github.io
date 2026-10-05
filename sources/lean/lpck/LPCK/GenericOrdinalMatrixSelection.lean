/- Universe-polymorphic extension of Posets.OrdinalIdealTransportMatrixSelection. Actual maps and bounds retained; paper-specific ideal statements omitted where they are not needed. -/
import LPCK.GenericOrdinalMatrixScalars
import LPCK.GenericOrdinalDiagonalFactorization
import LPCK.GenericCZeroUncountableFactorization

/-! Selected scalar jumps give a quantitative factorisation through the
actual operator on a full regular-cardinal sum of ordinal C-spaces. -/
noncomputable section
universe u
namespace LPCK.GenericOrdinal
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

local instance matrixSelectionSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance matrixSelectionSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance

theorem cZeroSum_insertCLM_single_constant {I : Type*} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (e : I → I) (he : Function.Injective e) (j : I) (z : X) :
    cZeroSum_insertCLM (𝕜 := 𝕜) (E := fun _ : I => X) e he (CZeroSum.single j z) =
      CZeroSum.single (e j) z := by
  classical
  apply CZeroSum.ext
  intro i
  by_cases hi : ∃ k, e k = i
  · obtain ⟨k, rfl⟩ := hi
    rw [cZeroSum_insertCLM_apply_selected]
    by_cases hk : k = j
    · subst k; simp
    · rw [CZeroSum.single_apply_ne _ _ hk,
        CZeroSum.single_apply_ne _ _ (fun h => hk (he h))]
  · have hij : i ≠ e j := fun h => hi ⟨j, h.symm⟩
    change cZeroSum_insertFun (E := fun _ : I => X) e
      (fun k => CZeroSum.single (𝕜 := 𝕜) (E := fun _ : I => X) j z k) i = _
    simp only [cZeroSum_insertFun, dif_neg hi, CZeroSum.single_apply_ne _ _ hij]

theorem regularOrdinalSum_factorsIdentityWith_of_selected_jump
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord))
    (e : c.ord.toType ↪ c.ord.toType)
    (hdiag : ∀ i, (1 : ℝ) / 2 ≤ ‖regularOrdinalBlockJump hc hu T (e i) (e i)‖)
    (hoff : ∀ i j, i ≠ j → regularOrdinalBlockJump hc hu T (e i) (e j) = 0) :
    FactorsIdentityWith T (CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord)) 16 := by
  let P := cZeroSum_insertCLM (𝕜 := 𝕜) (E := fun _ : c.ord.toType => OrdinalC 𝕜 c.ord) e e.injective
  let Q := CZeroSum.comapCLM (𝕜 := 𝕜) (E := fun _ : c.ord.toType => OrdinalC 𝕜 c.ord) e e.injective
  let D := Q.comp (T.comp P)
  have hblock (i j : c.ord.toType) : regularOrdinalBlock D i j = regularOrdinalBlock T (e i) (e j) := by
    apply ContinuousLinearMap.ext
    intro f
    change T (P (CZeroSum.single j f)) (e i) = T (CZeroSum.single (e j) f) (e i)
    rw [show P (CZeroSum.single j f) = CZeroSum.single (e j) f from
      cZeroSum_insertCLM_single_constant e e.injective j f]
  have hjump (i j : c.ord.toType) : regularOrdinalBlockJump hc hu D i j =
      regularOrdinalBlockJump hc hu T (e i) (e j) := by
    unfold regularOrdinalBlockJump
    rw [hblock]
  obtain ⟨L, R, _, hL, hR, hD⟩ := exists_regularOrdinalSum_diagonal_compression hc hu D
    (fun i j hij => (hjump i j).trans (hoff i j hij))
  let V := (L.comp D).comp R
  have hV (x) (i) : V x i = regularOrdinalBlockJump hc hu D i i • x i := hD x i
  have hf := ordinalSum_factorsIdentityWith_of_selected_diagonal (fun _ : c.ord.toType => c.ord)
    V (fun i => regularOrdinalBlockJump hc hu D i i) hV id Function.injective_id
    (fun _ => le_rfl) (fun i => by simpa only [id_eq, hjump] using hdiag i)
  have hbound : 2 * (‖L‖ * ‖R‖) ≤ 16 := by
    calc
      _ ≤ (2 : ℝ) * (4 * 2) := by gcongr
      _ = 16 := by norm_num
  have hfD := (hf.of_compression L R).mono hbound
  have hP : ‖P‖ ≤ 1 := norm_cZeroSum_insertCLM_le e e.injective
  have hQ : ‖Q‖ ≤ 1 := norm_cZeroSum_comapCLM_le e e.injective
  have hbound' : 16 * (‖Q‖ * ‖P‖) ≤ 16 := by
    calc
      _ ≤ (16 : ℝ) * (1 * 1) := by gcongr
      _ = 16 := by norm_num
  exact (hfD.of_compression Q P).mono hbound'

end LPCK.GenericOrdinal



