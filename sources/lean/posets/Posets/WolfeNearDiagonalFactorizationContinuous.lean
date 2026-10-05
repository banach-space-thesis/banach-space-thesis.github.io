import Posets.WolfeNearDiagonalFactorization

/-! The same explicit factorization for ordinary C(L) restriction and
extension maps, transported through the canonical compact C–C₀ isometry. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 L E F : Type*} [RCLike 𝕜] [TopologicalSpace L] [CompactSpace L]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def wolfeContinuousCompression
    (T : E →L[𝕜] F) (J : C(L, 𝕜) →L[𝕜] E) (Q : F →L[𝕜] C(L, 𝕜)) :
    JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 L :=
  (JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := L)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Q.comp (T.comp (J.comp
      (JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := L)).symm.toContinuousLinearEquiv.toContinuousLinearMap)))

theorem wolfe_nearDiagonal_continuous_compression_factors
    (M : JLMS.AtomicDualModel 𝕜 L)
    (T : E →L[𝕜] F) (J : C(L, 𝕜) →L[𝕜] E) (Q : F →L[𝕜] C(L, 𝕜))
    {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (hdiag : ∀ x, d ≤ ‖wolfeAtomicCrossRow M (wolfeContinuousCompression T J Q) x x‖)
    (hoff : ∀ x, ‖JLMS.atomicRestriction M ({x}ᶜ)
      ((JLMS.evaluation x).comp (wolfeContinuousCompression T J Q))‖ ≤ ε) :
    ∃ R : F →L[𝕜] C(L, 𝕜),
      R.comp (T.comp J) = ContinuousLinearMap.id 𝕜 C(L, 𝕜) ∧ ‖R‖ ≤ ‖Q‖ / (d - 3 * ε) := by
  let e := JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := L)
  let J₀ := J.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let Q₀ := e.toContinuousLinearEquiv.toContinuousLinearMap.comp Q
  have hcomp : Q₀.comp (T.comp J₀) = wolfeContinuousCompression T J Q := by
    ext f x
    rfl
  obtain ⟨R₀, hR₀, hn⟩ := wolfe_nearDiagonal_compression_factors M T J₀ Q₀ hε hgap
    (by simpa only [hcomp] using hdiag) (by simpa only [hcomp] using hoff)
  let R := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp R₀
  have hQ : ‖Q₀‖ ≤ ‖Q‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Q)
    intro f
    change ‖e (Q f)‖ ≤ _
    rw [e.norm_map]
    exact Q.le_opNorm f
  have hR : ‖R‖ ≤ ‖R₀‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R₀)
    intro f
    change ‖e.symm (R₀ f)‖ ≤ _
    rw [e.symm.norm_map]
    exact R₀.le_opNorm f
  refine ⟨R, ?_, hR.trans (hn.trans (div_le_div_of_nonneg_right hQ (sub_pos.mpr hgap).le))⟩
  apply ContinuousLinearMap.ext
  intro f
  have h := DFunLike.congr_fun hR₀ (e f)
  change R₀ (T (J (e.symm (e f)))) = e f at h
  rw [e.symm_apply_apply] at h
  change e.symm (R₀ (T (J f))) = f
  rw [h, e.symm_apply_apply]

end Posets
