/- Universe-polymorphic extension of Posets.OrdinalIdealTransportBlockCompression. Actual maps and bounds retained; paper-specific ideal statements omitted where they are not needed. -/
import LPCK.GenericOrdinalScalarCompression
import JLMS.CZeroSumFinite
import JLMS.CZeroSumOperators

/-! Bounded coordinate compressions assemble on the genuine Banach c₀ sum.
Vanishing of all off-diagonal blocks is checked using its convergent finite
coordinate expansions. -/
noncomputable section
namespace LPCK.GenericOrdinal
set_option synthInstance.maxHeartbeats 200000
open JLMS
universe u v
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000

theorem cZeroSum_mapCLM_single {I : Type u} {E F : I → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    (A : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (i : I) (x : E i) :
    CZeroSum.mapCLM A hC hA (CZeroSum.single i x) = CZeroSum.single i (A i x) := by
  classical
  ext j
  by_cases hj : j = i
  · subst j
    simp
  · simp only [CZeroSum.mapCLM_apply, CZeroSum.single_apply_ne _ _ hj, map_zero]

theorem exists_cZeroSum_scalar_compression {I : Type u} {E : I → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (T : CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 E)
    (l r : ∀ i, E i →L[𝕜] E i) (a : I → 𝕜)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hl : ∀ i, ‖l i‖ ≤ C) (hr : ∀ i, ‖r i‖ ≤ D)
    (hlr : ∀ i, (l i).comp (r i) = ContinuousLinearMap.id 𝕜 _)
    (hdiag : ∀ i x, l i (T (CZeroSum.single i (r i x)) i) = a i • x)
    (hoff : ∀ i j, i ≠ j → ∀ x, l i (T (CZeroSum.single j (r j x)) i) = 0) :
    ∃ L R : CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 E,
      L.comp R = ContinuousLinearMap.id 𝕜 _ ∧ ‖L‖ ≤ C ∧ ‖R‖ ≤ D ∧
      ∀ x i, L (T (R x)) i = a i • x i := by
  classical
  let L := CZeroSum.mapCLM l hC hl
  let R := CZeroSum.mapCLM r hD hr
  refine ⟨L, R, ?_, CZeroSum.norm_mapCLM_le l hC hl,
    CZeroSum.norm_mapCLM_le r hD hr, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    ext i
    exact congrArg (fun V : E i →L[𝕜] E i => V (x i)) (hlr i)
  · intro x i
    let A := (l i).comp ((CZeroSum.evalCLM i).comp (T.comp R))
    have hs := A.hasSum (CZeroSum.hasSum_single x)
    have he (j : I) : A (CZeroSum.single j (x j)) = if j = i then a i • x i else 0 := by
      change l i (T (R (CZeroSum.single j (x j))) i) = _
      rw [cZeroSum_mapCLM_single]
      by_cases hj : j = i
      · subst j
        simp only [ite_true]
        exact hdiag i (x i)
      · rw [if_neg hj]
        exact hoff i j (Ne.symm hj) (x j)
    simp_rw [he] at hs
    exact hs.unique (hasSum_ite_eq i (a i • x i))

attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

theorem exists_regularOrdinalSum_scalar_compression
    {μ : Ordinal.{u}} (c : Set.Iio μ → Cardinal.{u})
    (hc : ∀ i, (c i).IsRegular) (hu : ∀ i, Cardinal.aleph0 < c i)
    (hindex : ∀ i, i.val.card < c i) (hincrease : StrictMono c)
    (T : CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (c i).ord) →L[𝕜]
      CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (c i).ord)) :
    ∃ L R : CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (c i).ord) →L[𝕜]
        CZeroSum 𝕜 (fun i => OrdinalC 𝕜 (c i).ord),
      L.comp R = ContinuousLinearMap.id 𝕜 _ ∧ ‖L‖ ≤ 4 ∧ ‖R‖ ≤ 2 ∧
      ∀ x i, L (T (R x)) i =
        initialEndpointJump (𝕜 := 𝕜) (hc i) (hu i)
          ((CZeroSum.evalCLM i).comp
            (T.comp (CZeroSum.singleIsometry i).toContinuousLinearMap)) • x i := by
  classical
  let B (i j : Set.Iio μ) : OrdinalC 𝕜 (c j).ord →L[𝕜] OrdinalC 𝕜 (c i).ord :=
    (CZeroSum.evalCLM i).comp (T.comp (CZeroSum.singleIsometry j).toContinuousLinearMap)
  have h (i : Set.Iio μ) := exists_initialOrdinal_scalar_compression_small_family
    (hc i) (hu i) (B i i) (hindex i)
    (fun ξ hξ => (c ⟨ξ, hξ.trans i.property⟩).ord)
    (fun ξ hξ => by
      rw [Cardinal.card_ord]
      exact hincrease hξ)
    (fun ξ hξ => B i ⟨ξ, hξ.trans i.property⟩)
    (fun ξ hξ => B ⟨ξ, hξ.trans i.property⟩ i)
  choose l r hlr hdiag hl hr hleft hright using h
  apply exists_cZeroSum_scalar_compression T l r
    (fun i => initialEndpointJump (𝕜 := 𝕜) (hc i) (hu i) (B i i))
    (by norm_num) (by norm_num) hl hr hlr
  · intro i x
    exact congrArg (fun V : OrdinalC 𝕜 (c i).ord →L[𝕜] OrdinalC 𝕜 (c i).ord => V x)
      (hdiag i)
  · intro i j hij x
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hz := hright j i.val hij
      have hz' := congrArg
        (fun V : OrdinalC 𝕜 (c j).ord →L[𝕜] OrdinalC 𝕜 (c i).ord => V x) hz
      change B i j (r j x) = 0 at hz'
      change l i (B i j (r j x)) = 0
      rw [hz', map_zero]
    · have hz := hleft i j.val hji
      exact congrArg
        (fun V : OrdinalC 𝕜 (c j).ord →L[𝕜] OrdinalC 𝕜 (c i).ord => V (r j x)) hz

end LPCK.GenericOrdinal



