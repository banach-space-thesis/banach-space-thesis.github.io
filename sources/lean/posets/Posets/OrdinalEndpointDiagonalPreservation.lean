import Posets.OrdinalEndpointRetractions
import Posets.TransfiniteCZeroInsertion
import Posets.TransfiniteOrdinalColorSelection
import ThesisCommon.Analysis.FactorNormalization

/-! A controlled cofinal preservation step on actual endpoint-zero ordinal
block sums. No PFP assertion is assumed for the whole sum: the hypotheses
describe the operator on every vector and give uniformly bounded factors
on individual blocks. Cofinal selection and the concrete endpoint
retractions recover the identity of the whole sum with bound twice the
local bound. This does not assert that arbitrary operators are diagonal. -/

noncomputable section
namespace Posets
open JLMS ThesisCommon TransfiniteCZero
universe u v
variable {𝕜 : Type*} [RCLike 𝕜] {I : Type v}
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance endpointDiagonalFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance endpointDiagonalFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance endpointDiagonalGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance endpointDiagonalSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance
local instance endpointDiagonalSumGroup (α : I → Ordinal.{u}) :
    NormedAddCommGroup (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) := inferInstance
local instance endpointDiagonalSumSpace (α : I → Ordinal.{u}) :
    NormedSpace 𝕜 (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) := inferInstance

theorem ordinalEndpointSum_factors_of_selected_diagonal
    (α : I → Ordinal.{u})
    (T : CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i)) →L[𝕜]
      CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i)))
    (D : ∀ i, ordinalEndpointZero 𝕜 (α i) →L[𝕜] ordinalEndpointZero 𝕜 (α i))
    (e : I → I) (he : Function.Injective e) (hα : ∀ i, α i ≤ α (e i))
    (hT : ∀ x i, T x (e i) = D (e i) (x (e i)))
    {K : ℝ} (hK : 0 ≤ K)
    (hlocal : ∀ i, FactorsIdentityWith (D (e i)) (ordinalEndpointZero 𝕜 (α (e i))) K) :
    FactorsIdentityWith T (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) (2 * K) := by
  classical
  let E : I → Type _ := fun i => ordinalEndpointZero 𝕜 (α i)
  choose U V hUV hU hV using fun i => (hlocal i).normalized
  let R (i : I) : E (e i) →L[𝕜] E i :=
    (ordinalEndpointRead (𝕜 := 𝕜) (α i) (α (e i)) (hα i)).comp (U i)
  let J (i : I) : E i →L[𝕜] E (e i) :=
    (V i).comp (ordinalEndpointExtend (𝕜 := 𝕜) (α i) (α (e i)) (hα i))
  have hR (i : I) : ‖R i‖ ≤ 2 * K :=
    ((ordinalEndpointRead (𝕜 := 𝕜) (α i) (α (e i)) (hα i)).opNorm_comp_le (U i)).trans
      (mul_le_mul (norm_ordinalEndpointRead_le (𝕜 := 𝕜) _ _ _) (hU i)
        (norm_nonneg _) (by norm_num))
  have hJ (i : I) : ‖J i‖ ≤ 1 := by
    apply ((V i).opNorm_comp_le _).trans
    simpa only [one_mul] using mul_le_mul (hV i)
      (norm_ordinalEndpointExtend_le (𝕜 := 𝕜) _ _ _) (norm_nonneg _) zero_le_one
  let A : CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 E :=
    (CZeroSum.mapCLM R (mul_nonneg (by norm_num) hK) hR).comp
      (CZeroSum.comapCLM (𝕜 := 𝕜) (E := E) e he)
  let B : CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 E :=
    (cZeroSum_insertCLM (𝕜 := 𝕜) (E := E) e he).comp (CZeroSum.mapCLM J zero_le_one hJ)
  refine ⟨A, B, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply CZeroSum.ext
    intro i
    change R i (T (B x) (e i)) = x i
    rw [hT]
    have hb : B x (e i) = J i (x i) :=
      cZeroSum_insertCLM_apply_selected (𝕜 := 𝕜) (E := E) e he _ i
    rw [hb]
    have hi := congrArg (fun L : E (e i) →L[𝕜] E (e i) =>
      L (ordinalEndpointExtend (𝕜 := 𝕜) (α i) (α (e i)) (hα i) (x i))) (hUV i)
    change U i (D (e i) (V i (ordinalEndpointExtend (𝕜 := 𝕜) (α i) (α (e i)) (hα i) (x i)))) =
      ordinalEndpointExtend (𝕜 := 𝕜) (α i) (α (e i)) (hα i) (x i) at hi
    change ordinalEndpointRead (𝕜 := 𝕜) (α i) (α (e i)) (hα i)
      (U i (D (e i) (V i (ordinalEndpointExtend (𝕜 := 𝕜) (α i) (α (e i)) (hα i) (x i))))) = x i
    rw [hi, ordinalEndpointRead_extend]
  · have hA : ‖A‖ ≤ 2 * K := by
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      calc
        _ ≤ (2 * K) * 1 := mul_le_mul (CZeroSum.norm_mapCLM_le R _ hR)
          (norm_cZeroSum_comapCLM_le (𝕜 := 𝕜) (E := E) e he) (norm_nonneg _)
          (mul_nonneg (by norm_num) hK)
        _ = _ := mul_one _
    have hB : ‖B‖ ≤ 1 := by
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      simpa only [one_mul] using mul_le_mul
        (norm_cZeroSum_insertCLM_le (𝕜 := 𝕜) (E := E) e he)
        (CZeroSum.norm_mapCLM_le J zero_le_one hJ) (norm_nonneg _) zero_le_one
    simpa only [mul_one] using mul_le_mul hA hB (norm_nonneg _)
      (mul_nonneg (by norm_num) hK)

theorem ordinalEndpointSum_diagonal_dichotomy
    {c : Cardinal.{v}} (hc : c.IsRegular)
    (α : Set.Iio c.ord → Ordinal.{u}) (hα : Monotone α)
    (T : CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i)) →L[𝕜]
      CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i)))
    (D : ∀ i, ordinalEndpointZero 𝕜 (α i) →L[𝕜] ordinalEndpointZero 𝕜 (α i))
    (hT : ∀ x i, T x i = D i (x i)) {K : ℝ} (hK : 0 ≤ K)
    (hlocal : ∀ i,
      FactorsIdentityWith (D i) (ordinalEndpointZero 𝕜 (α i)) K ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - D i)
        (ordinalEndpointZero 𝕜 (α i)) K) :
    FactorsIdentityWith T (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) (2 * K) ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - T)
      (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) (2 * K) := by
  rcases TransfiniteOrdinal.exists_regularOrdinal_twoColor_selection hc _ _ hlocal with
    ⟨e, he, hge, hgood⟩ | ⟨e, he, hge, hgood⟩
  · exact Or.inl (ordinalEndpointSum_factors_of_selected_diagonal α T D e he.injective
      (fun i => hα (hge i)) (fun x i => hT x (e i)) hK hgood)
  · right
    have hTc (x : CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) (i : Set.Iio c.ord) :
        (ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) - T) x (e i) =
          (ContinuousLinearMap.id 𝕜 (ordinalEndpointZero 𝕜 (α (e i))) - D (e i)) (x (e i)) := by
      change x (e i) - T x (e i) = x (e i) - D (e i) (x (e i))
      rw [hT]
    exact ordinalEndpointSum_factors_of_selected_diagonal (𝕜 := 𝕜) α
      (ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) - T)
      (fun i : Set.Iio c.ord => ContinuousLinearMap.id 𝕜 (ordinalEndpointZero 𝕜 (α i)) - D i)
      e he.injective (fun i => hα (hge i)) hTc hK hgood

end Posets
