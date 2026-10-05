import ThesisCommon.Analysis.JamesQuasiReflexiveOne

/-! The concrete James bidual splits into the canonical null-sequence part
and its scalar coordinate limit. Both terms are constructed from genuine
continuous bidual functionals. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

theorem jamesBidualLimit_norm_le
    (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    ‖jamesBidualLimit p hp ξ‖ ≤ ‖ξ‖ := by
  apply le_of_tendsto (jamesBidualCoordinate_tendsto p hp ξ).norm
  apply Eventually.of_forall
  intro n
  exact (ξ.le_opNorm (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n)).trans
    ((mul_le_mul_of_nonneg_left
      (JamesSequenceSpace.norm_coordinate_le (𝕜 := 𝕜) (p := p) n)
      (norm_nonneg ξ)).trans_eq (mul_one _))

def jamesBidualLimitContinuous :
    ((JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous (jamesBidualLimitLinear (𝕜 := 𝕜) p hp) 1
    (fun (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) => by
      change ‖jamesBidualLimit (𝕜 := 𝕜) p hp ξ‖ ≤ 1 * ‖ξ‖
      rw [one_mul]
      exact jamesBidualLimit_norm_le (𝕜 := 𝕜) p hp ξ)

@[simp] theorem jamesBidualLimitContinuous_apply
    (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    jamesBidualLimitContinuous (𝕜 := 𝕜) p hp ξ = jamesBidualLimit p hp ξ := rfl

theorem jamesBidualConstant_norm_le (hpl : 1 < p.val.toReal) :
    ‖jamesBidualConstant (𝕜 := 𝕜) p hp hpl‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro φ
  exact weakCauchyValue_norm_le (jamesConstantPrefix p hp)
    (fun ψ => cauchySeq_tendsto_of_complete (jamesConstantPrefix_weakCauchy p hp hpl ψ))
    (jamesConstantPrefix_norm_le p hp) φ

theorem jamesBidual_decomposition (hpl : 1 < p.val.toReal)
    (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    ξ = NormedSpace.inclusionInDoubleDual 𝕜 (JamesSequenceSpace 𝕜 p)
      (jamesBidualNullPart p hp ξ) +
      jamesBidualLimit p hp ξ • jamesBidualConstant (𝕜 := 𝕜) p hp hpl := by
  apply james_bidual_ext_coordinates p hp hpl
  intro n
  change jamesBidualCoordinate p ξ n = jamesBidualNullPart p hp ξ n +
    jamesBidualLimit p hp ξ * jamesBidualConstant (𝕜 := 𝕜) p hp hpl
      (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n)
  rw [jamesBidualNullPart_apply, jamesBidualConstant_coordinate, mul_one, sub_add_cancel]

theorem jamesBidual_mem_image_iff_limit_eq_zero (hpl : 1 < p.val.toReal)
    (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    ξ ∈ bidualImage 𝕜 (JamesSequenceSpace 𝕜 p) ↔ jamesBidualLimit p hp ξ = 0 := by
  rw [← jamesBidualLimit_ker_eq (𝕜 := 𝕜) p hp hpl]
  rfl

end ThesisCommon
