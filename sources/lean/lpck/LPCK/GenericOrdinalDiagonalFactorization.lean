/- Universe-polymorphic extension of Posets.OrdinalIdealTransportDiagonalFactorization. Actual maps and bounds retained; paper-specific ideal statements omitted where they are not needed. -/
import LPCK.GenericOrdinalBlockCompression
import LPCK.GenericOrdinalCofinalSelection
import LPCK.GenericOrdinalCofinalMaps

/-! A scalar diagonal bounded away from zero on a cofinal selection preserves
the whole ordinal c₀ sum. Combined with the exact block compression, this gives
a uniform primary factorisation theorem for increasing regular blocks. -/
noncomputable section
namespace LPCK.GenericOrdinal
open JLMS ThesisCommon
universe u v
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

local instance diagonalSumGroup {I : Type u} (E : I → Type v)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance diagonalSumSpace {I : Type u} (E : I → Type v)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

theorem ordinalSum_factorsIdentityWith_of_selected_diagonal
    {I : Type v} (α : I → Ordinal.{u})
    (D : JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (α i)) →L[𝕜]
      JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (α i)))
    (a : I → 𝕜) (hD : ∀ x i, D x i = a i • x i)
    (e : I → I) (he : Function.Injective e) (hα : ∀ i, α i ≤ α (e i))
    (ha : ∀ i, (1 : ℝ) / 2 ≤ ‖a (e i)‖) :
    FactorsIdentityWith D (JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (α i))) 2 := by
  let p (i : I) := ordinalInitialSegmentExtend (𝕜 := 𝕜) (α i) (α (e i))
  let q (i : I) := (a (e i))⁻¹ • ordinalInitialSegmentRead (𝕜 := 𝕜) (α i) (α (e i)) (hα i)
  have hp (i : I) : ‖p i‖ ≤ 1 := norm_ordinalInitialSegmentExtend_le _ _
  have hane (i : I) : a (e i) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (ha i))
  have hainv (i : I) : ‖(a (e i))⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (norm_pos_iff.mpr (hane i))]
    linarith [ha i]
  have hq (i : I) : ‖q i‖ ≤ 2 := by
    change ‖(a (e i))⁻¹ • ordinalInitialSegmentRead (𝕜 := 𝕜) (α i) (α (e i)) (hα i)‖ ≤ _
    rw [norm_smul]
    calc
      _ ≤ (2 : ℝ) * 1 := mul_le_mul (hainv i) (norm_ordinalInitialSegmentRead_le _ _ _)
        (norm_nonneg _) (by norm_num)
      _ = 2 := mul_one _
  let P : JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (α i)) →L[𝕜]
      JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (α i)) :=
    (cZeroSum_insertCLM (𝕜 := 𝕜) e he).comp (CZeroSum.mapCLM p zero_le_one hp)
  let Q : JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (α i)) →L[𝕜]
      JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (α i)) :=
    (CZeroSum.mapCLM q (by norm_num : (0:ℝ) ≤ 2) hq).comp
    (CZeroSum.comapCLM (𝕜 := 𝕜) (E := fun i => OrdinalC 𝕜 (α i)) e he)
  have hP : ‖P‖ ≤ 1 := by
    calc
      _ ≤ ‖cZeroSum_insertCLM (𝕜 := 𝕜) (E := fun i => OrdinalC 𝕜 (α i)) e he‖ *
        ‖CZeroSum.mapCLM p zero_le_one hp‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 : ℝ) * 1 := mul_le_mul (norm_cZeroSum_insertCLM_le e he)
        (CZeroSum.norm_mapCLM_le _ _ _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  have hQ : ‖Q‖ ≤ 2 := by
    calc
      _ ≤ ‖CZeroSum.mapCLM q (by norm_num : (0:ℝ) ≤ 2) hq‖ *
        ‖CZeroSum.comapCLM (𝕜 := 𝕜) (E := fun i => OrdinalC 𝕜 (α i)) e he‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (2 : ℝ) * 1 := mul_le_mul (CZeroSum.norm_mapCLM_le _ _ _)
        (norm_cZeroSum_comapCLM_le e he) (norm_nonneg _) (by norm_num)
      _ = 2 := mul_one _
  refine ⟨Q, P, ?_, (mul_le_mul hQ hP (norm_nonneg _) (by norm_num)).trans_eq (mul_one 2)⟩
  apply ContinuousLinearMap.ext
  intro x
  apply JLMS.CZeroSum.ext
  intro i
  change (a (e i))⁻¹ • ordinalInitialSegmentRead (α i) (α (e i)) (hα i) (D (P x) (e i)) = x i
  rw [hD, map_smul]
  have hpx : P x (e i) = p i (x i) := cZeroSum_insertCLM_apply_selected e he _ i
  rw [hpx]
  change (a (e i))⁻¹ • (a (e i) •
    ordinalInitialSegmentRead (α i) (α (e i)) (hα i)
      (ordinalInitialSegmentExtend (α i) (α (e i)) (x i))) = x i
  rw [ordinalInitialSegmentRead_extend, smul_smul, inv_mul_cancel₀ (hane i), one_smul]

attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

theorem regularOrdinalSum_hasCPFP_sixteen
    {d : Cardinal.{u}} (hd : d.IsRegular) (c : Set.Iio d.ord → Cardinal.{u})
    (hc : ∀ i, (c i).IsRegular) (hu : ∀ i, Cardinal.aleph0 < c i)
    (hindex : ∀ i, i.val.card < c i) (hincrease : StrictMono c) :
    HasCPFP 𝕜 (JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (c i).ord)) 16 := by
  intro T
  obtain ⟨L, R, hLR, hL, hR, hdiag⟩ :=
    exists_regularOrdinalSum_scalar_compression c hc hu hindex hincrease T
  let D : JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (c i).ord) →L[𝕜]
      JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (c i).ord) := (L.comp T).comp R
  let a (i : Set.Iio d.ord) := initialEndpointJump (𝕜 := 𝕜) (hc i) (hu i)
    ((CZeroSum.evalCLM i).comp (T.comp (CZeroSum.singleIsometry i).toContinuousLinearMap))
  have hD (x) (i) : D x i = a i • x i := hdiag x i
  have hbound : 2 * (‖L‖ * ‖R‖) ≤ 16 := by
    calc
      _ ≤ (2 : ℝ) * (4 * 2) := by gcongr
      _ = 16 := by norm_num
  have hcolor (i) : (1:ℝ)/2 ≤ ‖a i‖ ∨ (1:ℝ)/2 ≤ ‖1 - a i‖ := by
    have h := norm_add_le (a i) (1 - a i)
    rw [add_sub_cancel, norm_one] at h
    by_cases h' : (1:ℝ)/2 ≤ ‖a i‖
    · exact Or.inl h'
    · exact Or.inr (by linarith)
  rcases exists_regularOrdinal_twoColor_selection hd
      (fun i => (1:ℝ)/2 ≤ ‖a i‖) (fun i => (1:ℝ)/2 ≤ ‖1-a i‖) hcolor with h | h
  · obtain ⟨e, he, hie, hgood⟩ := h
    have hf := ordinalSum_factorsIdentityWith_of_selected_diagonal
      (fun i => (c i).ord) D a hD e he.injective
      (fun i => Cardinal.ord_le_ord.mpr (hincrease.monotone (hie i))) hgood
    exact Or.inl ((hf.of_compression L R).mono hbound)
  · obtain ⟨e, he, hie, hgood⟩ := h
    have hD' (x : JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (c i).ord)) (i : Set.Iio d.ord) :
        (ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (c i).ord)) - D) x i =
          (1 - a i) • x i := by
      change x i - D x i = _
      rw [hD, sub_smul, one_smul]
    have hf := ordinalSum_factorsIdentityWith_of_selected_diagonal
      (fun i => (c i).ord) (ContinuousLinearMap.id 𝕜 _ - D) (fun i => 1-a i) hD'
      e he.injective (fun i => Cardinal.ord_le_ord.mpr (hincrease.monotone (hie i))) hgood
    rw [← compression_complement T L R hLR] at hf
    exact Or.inr ((hf.of_compression L R).mono hbound)

theorem regularOrdinalSum_hasUPFP
    {d : Cardinal.{u}} (hd : d.IsRegular) (c : Set.Iio d.ord → Cardinal.{u})
    (hc : ∀ i, (c i).IsRegular) (hu : ∀ i, Cardinal.aleph0 < c i)
    (hindex : ∀ i, i.val.card < c i) (hincrease : StrictMono c) :
    HasUPFP 𝕜 (JLMS.CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (c i).ord)) :=
  ⟨16, by norm_num, regularOrdinalSum_hasCPFP_sixteen hd c hc hu hindex hincrease⟩

end LPCK.GenericOrdinal



