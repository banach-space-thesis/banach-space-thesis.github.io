import PEMS.ExtremallyDisconnectedInfinityFactorization
import PEMS.CZeroFixingUpperBound

/-! Theorem 6.7 as typeset: both sequence spaces are unindexed, so the
infinite set Γ does not enter the maps. The existing countable construction
supplies the stronger complemented factorization when the lower bound is
positive. A negative threshold also allows the zero extension. -/

noncomputable section
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
open ThesisCommon
open scoped ENNReal
namespace PEMS

variable {𝕜 : Type} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

local instance exactRosenthalBidualGroup :
    NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

local instance exactRosenthalBidualSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

theorem theorem_6_7_printed (Γ : Type*) [Infinite Γ] [CompleteSpace E] [CompleteSpace F]
    (P : StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] E) (hP : ‖P‖ ≤ 1)
    (hPJ : ∀ x, P (NormedSpace.inclusionInDoubleDual 𝕜 E x) = x)
    (T : E →L[𝕜] F) (V : CZero 𝕜 →L[𝕜] E) (hV : ‖V‖ ≤ 1)
    {δ : ℝ} (hδ : δ < minimumModulus (T.comp V)) :
    ∃ W : EllInfinity 𝕜 →L[𝕜] E, δ < minimumModulus (T.comp W) := by
  let x₀ : EllInfinity 𝕜 := lp.single ∞ 0 (1 : 𝕜)
  have hx₀ : ‖x₀‖ = 1 := by
    change ‖(lp.single ∞ 0 (1 : 𝕜) : EllInfinity 𝕜)‖ = 1
    rw [lp.norm_single (by simp : (0 : ENNReal) < ∞), norm_one]
  by_cases hd : δ < 0
  · refine ⟨0, hd.trans_le ?_⟩
    apply le_csInf
    · exact ⟨_, x₀, hx₀, rfl⟩
    · rintro _ ⟨x, _, rfl⟩
      exact norm_nonneg _
  let c := minimumModulus (T.comp V)
  have hc : 0 < c := (le_of_not_gt hd).trans_lt hδ
  obtain ⟨U, W, hUW, hU, _⟩ := theorem_6_7_countable P hP hPJ T V hV hc
    (minimumModulus_cZero_mul_norm_le (T.comp V))
  refine ⟨W, hδ.trans_le ?_⟩
  apply le_csInf
  · exact ⟨_, x₀, hx₀, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have heq : U (T (W x)) = x := DFunLike.congr_fun hUW x
    have hu := U.le_opNorm (T (W x))
    rw [heq, hx] at hu
    have hbound : 1 ≤ 1 / c * ‖T (W x)‖ :=
      hu.trans (mul_le_mul_of_nonneg_right hU (norm_nonneg _))
    change c ≤ ‖T (W x)‖
    rwa [one_div, ← div_eq_inv_mul, le_div_iff₀ hc, one_mul] at hbound

end PEMS
