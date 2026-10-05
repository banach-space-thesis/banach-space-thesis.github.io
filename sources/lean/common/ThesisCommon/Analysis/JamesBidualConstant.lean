import ThesisCommon.Analysis.JamesConstantPrefixes
import ThesisCommon.Analysis.JamesShrinkingBasis
import ThesisCommon.Analysis.BoundedWeakCauchyBidual

/-! The bounded constant-one initial sections determine a genuine bidual
element whose values on all coordinate functionals are one. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

theorem jamesConstantPrefix_weakCauchy (hpl : 1 < p.val.toReal)
    (φ : JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) :
    CauchySeq (fun N => φ (jamesConstantPrefix p hp N)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp
    (james_functional_initial_tendsto p hp hpl φ) (ε / 4) (by positivity)
  let ψ := φ.comp (JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) K)
  have hsmall : ‖φ - ψ‖ < ε / 4 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hK K le_rfl
  refine ⟨K, fun N hN M hM => ?_⟩
  have heq : φ (jamesConstantPrefix p hp N) - φ (jamesConstantPrefix p hp M) =
      (φ - ψ) (jamesConstantPrefix p hp N - jamesConstantPrefix p hp M) := by
    simp [ψ, map_sub, jamesConstantPrefix_initial p hp K N hN,
      jamesConstantPrefix_initial p hp K M hM]
  have hbound : ‖jamesConstantPrefix (𝕜 := 𝕜) p hp N - jamesConstantPrefix p hp M‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      have hn := jamesConstantPrefix_norm_le (𝕜 := 𝕜) p hp N
      have hm := jamesConstantPrefix_norm_le (𝕜 := 𝕜) p hp M
      linarith)
  rw [dist_eq_norm, heq]
  calc
    _ ≤ ‖φ - ψ‖ * ‖jamesConstantPrefix p hp N - jamesConstantPrefix p hp M‖ :=
      (φ - ψ).le_opNorm _
    _ ≤ ‖φ - ψ‖ * 2 := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ < (ε / 4) * 2 := mul_lt_mul_of_pos_right hsmall (by norm_num)
    _ < ε := by linarith

def jamesBidualConstant (hpl : 1 < p.val.toReal) :
    (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  boundedWeakCauchyBidual (jamesConstantPrefix p hp)
    (fun φ => cauchySeq_tendsto_of_complete (jamesConstantPrefix_weakCauchy p hp hpl φ))
    (jamesConstantPrefix_norm_le p hp)

theorem jamesBidualConstant_coordinate (hpl : 1 < p.val.toReal) (n : ℕ) :
    jamesBidualConstant (𝕜 := 𝕜) p hp hpl
      (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n) = 1 := by
  have ht := boundedWeakCauchyBidual_tendsto (jamesConstantPrefix (𝕜 := 𝕜) p hp)
    (fun φ => cauchySeq_tendsto_of_complete (jamesConstantPrefix_weakCauchy p hp hpl φ))
    (jamesConstantPrefix_norm_le p hp) (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n)
  have ht' : Tendsto (fun N => JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n
      (jamesConstantPrefix p hp N)) atTop (𝓝 (1 : 𝕜)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with N hN
    simp [JamesSequenceSpace.coordinate, hN]
  exact tendsto_nhds_unique ht ht'

end ThesisCommon
