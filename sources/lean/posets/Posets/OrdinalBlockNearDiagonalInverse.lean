import Posets.OrdinalBlockNearDiagonalEstimates
import Posets.WolfeNearDiagonalFactorizationInverse

/-! A uniform row approximation gives an actual left inverse on an arbitrary
c₀ sum of compact function spaces. Empty blocks and an empty index set are
allowed; no scalar comparison function is assumed continuous. -/

noncomputable section
open Set Topology
namespace Posets
universe u v w
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
variable {𝕜 : Type w} [RCLike 𝕜] {I : Type u} {L : I → Type v}
  [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)]

local instance ordinalBlockNearInverseCoordinateGroup (i : I) : NormedAddCommGroup C(L i, 𝕜) :=
  inferInstance
local instance ordinalBlockNearInverseCoordinateSpace (i : I) : NormedSpace 𝕜 C(L i, 𝕜) :=
  inferInstance
local instance ordinalBlockNearInverseGroup : NormedAddCommGroup (OrdinalBlockFunctionSum 𝕜 L) :=
  inferInstance
local instance ordinalBlockNearInverseSpace : NormedSpace 𝕜 (OrdinalBlockFunctionSum 𝕜 L) :=
  inferInstance

def ordinalBlockReciprocal (b : ∀ i, C(L i, 𝕜)) (hb : ∀ i x, b i x ≠ 0)
    (i : I) : C(L i, 𝕜) :=
  ⟨fun x => (b i x)⁻¹, (b i).continuous.inv₀ (hb i)⟩

theorem ordinalBlockReciprocal_norm_le (b : ∀ i, C(L i, 𝕜)) {γ : ℝ}
    (hγ : 0 < γ) (hb : ∀ i x, γ ≤ ‖b i x‖) (i : I) :
    ‖ordinalBlockReciprocal b (fun i x => norm_pos_iff.mp (hγ.trans_le (hb i x))) i‖ ≤ 1 / γ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖(b i x)⁻¹‖ ≤ 1 / γ
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le hγ (hb i x)

theorem ordinalBlockNearDiagonal_exists_left_inverse
    (A : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] OrdinalBlockFunctionSum 𝕜 L)
    (a : ∀ i, L i → 𝕜) {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (hdiag : ∀ i x, d ≤ ‖a i x‖)
    (hrow : ∀ i x, ‖(ordinalBlockEvaluation i x).comp A -
      a i x • ordinalBlockEvaluation i x‖ ≤ ε) :
    ∃ B : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] OrdinalBlockFunctionSum 𝕜 L,
      B.comp A = ContinuousLinearMap.id 𝕜 _ ∧ ‖B‖ ≤ 1 / (d - 3 * ε) := by
  have hγ : 0 < d - ε := by linarith
  have hb := ordinalBlockDiagonal_lower A a hε hdiag hrow
  let b := ordinalBlockReciprocal (ordinalBlockDiagonal A)
    (fun i x => norm_pos_iff.mp (hγ.trans_le (hb i x)))
  let D := ordinalBlockDiagonalOperator A
  let Dinv := JLMS.CZeroSum.mapCLM
    (fun i => ContinuousLinearMap.mul 𝕜 C(L i, 𝕜) (b i))
    (show 0 ≤ 1 / (d - ε) by positivity)
    (fun i => (ordinalBlock_multiplier_norm_le i (b i)).trans
      (ordinalBlockReciprocal_norm_le (ordinalBlockDiagonal A) hγ hb i))
  have hDinv : ‖Dinv‖ ≤ 1 / (d - ε) := JLMS.CZeroSum.norm_mapCLM_le _ _ _
  have hInvD : Dinv.comp D = ContinuousLinearMap.id 𝕜 _ := by
    apply ContinuousLinearMap.ext
    intro f
    apply JLMS.CZeroSum.ext
    intro i
    apply ContinuousMap.ext
    intro x
    change (ordinalBlockDiagonal A i x)⁻¹ * (ordinalBlockDiagonal A i x * f i x) = f i x
    rw [← mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mp (hγ.trans_le (hb i x))), one_mul]
  obtain ⟨B, hB, hn⟩ := wolfe_exists_left_inverse_of_approximation A D Dinv hγ
    (show 0 ≤ 2 * ε by positivity) (show 2 * ε < d - ε by linarith)
    hDinv hInvD (ordinalBlockDiagonalOperator_error A a hε hrow)
  refine ⟨B, hB, ?_⟩
  have heq : d - ε - 2 * ε = d - 3 * ε := by ring
  simpa only [heq] using hn

/-- Applying the criterion to an actual compression of a bounded operator. -/
theorem ordinalBlockNearDiagonal_compression_factors
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (J : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] E)
    (Q : F →L[𝕜] OrdinalBlockFunctionSum 𝕜 L)
    (a : ∀ i, L i → 𝕜) {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (hdiag : ∀ i x, d ≤ ‖a i x‖)
    (hrow : ∀ i x, ‖(ordinalBlockEvaluation i x).comp (Q.comp (T.comp J)) -
      a i x • ordinalBlockEvaluation i x‖ ≤ ε) :
    ∃ R : F →L[𝕜] OrdinalBlockFunctionSum 𝕜 L,
      R.comp (T.comp J) = ContinuousLinearMap.id 𝕜 _ ∧ ‖R‖ ≤ ‖Q‖ / (d - 3 * ε) := by
  obtain ⟨B, hB, hn⟩ := ordinalBlockNearDiagonal_exists_left_inverse
    (Q.comp (T.comp J)) a hε hgap hdiag hrow
  refine ⟨B.comp Q, ?_, ?_⟩
  · simpa only [ContinuousLinearMap.comp_assoc] using hB
  · calc
      ‖B.comp Q‖ ≤ ‖B‖ * ‖Q‖ := B.opNorm_comp_le Q
      _ ≤ (1 / (d - 3 * ε)) * ‖Q‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg Q)
      _ = ‖Q‖ / (d - 3 * ε) := by ring

end Posets
