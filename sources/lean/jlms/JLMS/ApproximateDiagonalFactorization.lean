import JLMS.CZeroIdentity
import JLMS.QuantitativeNeumann

/-!
# Correct a nearly diagonal factorization by Neumann inversion

Normalize the diagonal error by a left inverse of norm at most 1/γ.
The normalized product is at distance at most ε/γ<1 from the identity.
Neumann inversion corrects it exactly, producing an outgoing map of norm
at most 1/(γ−ε), while retaining the contractive incoming map.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem exists_factorization_of_approximate_diagonal
    (R : cZero 𝕜 →L[𝕜] X) (U : X →L[𝕜] cZero 𝕜) (V : cZero 𝕜 →L[𝕜] cZero 𝕜)
    (D Dinv : cZero 𝕜 →L[𝕜] cZero 𝕜)
    {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 ≤ ε) (hεγ : ε < γ)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (hDinv : ‖Dinv‖ ≤ 1 / γ)
    (hInvD : Dinv.comp D = ContinuousLinearMap.id 𝕜 (cZero 𝕜))
    (herror : ‖D - (U.comp R).comp V‖ ≤ ε) :
    ∃ W : X →L[𝕜] cZero 𝕜,
      (W.comp R).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧ ‖W‖ ≤ 1 / (γ - ε) := by
  have hne : cZeroUnit 𝕜 0 ≠ 0 := by
    intro h
    have he := congrArg (fun a : cZero 𝕜 => a 0) h
    simpa using he
  letI : Nontrivial (cZero 𝕜) := ⟨⟨cZeroUnit 𝕜 0, 0, hne⟩⟩
  let P := (U.comp R).comp V
  let F := Dinv.comp P
  have hdiff : ContinuousLinearMap.id 𝕜 (cZero 𝕜) - F = Dinv.comp (D - P) := by
    rw [ContinuousLinearMap.comp_sub, hInvD]
  have hclose : ‖ContinuousLinearMap.id 𝕜 (cZero 𝕜) - F‖ ≤ ε / γ := by
    rw [hdiff]
    calc
      _ ≤ ‖Dinv‖ * ‖D - P‖ := Dinv.opNorm_comp_le _
      _ ≤ (1 / γ) * ε := mul_le_mul hDinv herror (norm_nonneg (D - P)) (one_div_pos.mpr hγ).le
      _ = ε / γ := by ring
  have hrad : ε / γ < 1 := (div_lt_one hγ).mpr hεγ
  obtain ⟨G, hGF, hG⟩ := exists_inverse_near_identity F (div_nonneg hε hγ.le) hrad hclose
  let W := G.comp (Dinv.comp U)
  have hDU : ‖Dinv.comp U‖ ≤ 1 / γ :=
    (Dinv.opNorm_comp_le U).trans (by
      simpa using mul_le_mul hDinv hU (norm_nonneg U) (one_div_pos.mpr hγ).le)
  refine ⟨W, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro a
    exact congrArg (fun L : cZero 𝕜 →L[𝕜] cZero 𝕜 => L a) hGF
  · calc
      ‖W‖ ≤ ‖G‖ * ‖Dinv.comp U‖ := G.opNorm_comp_le _
      _ ≤ (1 / (1 - ε / γ)) * (1 / γ) := mul_le_mul hG hDU (norm_nonneg (Dinv.comp U))
        (one_div_pos.mpr (sub_pos.mpr hrad)).le
      _ = 1 / (γ - ε) := by field_simp

end JLMS
