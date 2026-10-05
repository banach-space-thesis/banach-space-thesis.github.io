import Posets.OrdinalEndpointDiagonalPreservation
import Posets.CZeroOperatorDiagonal

/-! A quantitative preservation criterion for arbitrary operators on
transfinite ordinal block sums. Both the uniform factors of diagonal
blocks and the finite off-diagonal row bound are explicit hypotheses.
They are not inferred from a square isomorphism or assumed as fields of
the Banach space. -/
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace Posets
open JLMS ThesisCommon
universe u v
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance endpointNearFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance endpointNearFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance endpointNearGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance endpointNearSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance
local instance endpointNearComplete (α : Ordinal.{u}) :
    CompleteSpace (ordinalEndpointZero 𝕜 α) := by
  dsimp only [ordinalEndpointZero]
  infer_instance
local instance endpointNearSumGroup {I : Type v} (α : I → Ordinal.{u}) :
    NormedAddCommGroup (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) := inferInstance
local instance endpointNearSumSpace {I : Type v} (α : I → Ordinal.{u}) :
    NormedSpace 𝕜 (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) := inferInstance

theorem ordinalEndpointSum_nearDiagonal_dichotomy
    {c : Cardinal.{v}} (hc : c.IsRegular)
    (α : Set.Iio c.ord → Ordinal.{u}) (hα : Monotone α)
    (T : CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i)) →L[𝕜]
      CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i)))
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (hsmall : (2 * K) * ε < 1 / 2)
    (hlocal : ∀ i,
      FactorsIdentityWith (cZeroOperatorBlock T i i) (ordinalEndpointZero 𝕜 (α i)) K ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - cZeroOperatorBlock T i i)
        (ordinalEndpointZero 𝕜 (α i)) K)
    (hrow : ∀ i (s : Finset (Set.Iio c.ord)),
      ∑ j ∈ s.erase i, ‖cZeroOperatorBlock T i j‖ ≤ ε) :
    FactorsIdentityWith T (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) (4 * K) ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - T)
      (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) (4 * K) := by
  let D := cZeroOperatorDiagonal T
  have hn : (2 * K) * ‖T - D‖ < 1 / 2 :=
    (mul_le_mul_of_nonneg_left (norm_sub_cZeroOperatorDiagonal_le T hε (fun i s => by
      have hs : @Finset.erase _ (Classical.typeDecidableEq _) s i = s.erase i := by
        ext j
        simp only [Finset.mem_erase]
      rw [hs]
      exact hrow i s))
      (mul_nonneg (by norm_num) hK)).trans_lt hsmall
  rcases ordinalEndpointSum_diagonal_dichotomy hc α hα D
    (fun i => cZeroOperatorBlock T i i) (fun x i => rfl) hK hlocal with h | h
  · left
    convert h.perturb hn using 1
    ring
  · right
    have hd : (ContinuousLinearMap.id 𝕜 _ - T) - (ContinuousLinearMap.id 𝕜 _ - D) =
        -(T - D) := by abel
    have hn' : (2 * K) *
        ‖(ContinuousLinearMap.id 𝕜 _ - T) - (ContinuousLinearMap.id 𝕜 _ - D)‖ < 1 / 2 := by
      rwa [hd, norm_neg]
    convert h.perturb hn' using 1
    ring

end Posets
