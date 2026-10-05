import ThesisCommon.Analysis.LpHaarNearDiagonalCompression
import ThesisCommon.Analysis.LpHaarMultiplierStabilization

/-! Combine the actual near-diagonal reduction and multiplier stabilization.
Both retractions have norm at most one, so the errors remain uniform. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical
namespace ThesisCommon
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

include hp in
theorem intervalLp_scalar_compression_meanZero
    (T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hTmean : ∀ f, lpHaarIntegral (T f) = 0)
    (hTconst : T (lpHaarRawVector 𝕜 p none) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A B : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p, ∃ c : 𝕜,
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ A.comp B = ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) ∧
      (∀ f, lpHaarIntegral (A f) = lpHaarIntegral f) ∧
      (∀ f, lpHaarIntegral (B f) = lpHaarIntegral f) ∧
      ∀ f, lpHaarIntegral f = 0 →
        ‖((A.comp T).comp B) f - c • f‖ ≤ (3 * ε / 4) * ‖f‖ := by
  obtain ⟨A₁, B₁, D, hA₁, hB₁, hAB₁, hmA₁, hmB₁, herror, hdiag⟩ :=
    lpHaar_near_diagonal_compression 𝕜 p hp T hTmean hTconst hε
  let S := (A₁.comp T).comp B₁
  let d (n : ℕ) (k : Fin (2 ^ n)) := lpHaarDyadicCoefficient 𝕜 p n k (S (lpHaarDyadic 𝕜 p n k))
  obtain ⟨A₂, B₂, c, hA₂, hB₂, hAB₂, hmA₂, hmB₂, hscalar⟩ :=
    lpHaar_multiplier_scalar_compression 𝕜 p hp D d hdiag hε
  let A := A₂.comp A₁
  let B := B₁.comp B₂
  have hA : ‖A‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by nlinarith [norm_nonneg A₁, norm_nonneg A₂])
  have hB : ‖B‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by nlinarith [norm_nonneg B₁, norm_nonneg B₂])
  have hAB : A.comp B = ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) := by
    dsimp only [A, B]
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc A₁ B₁ B₂,
      hAB₁, ContinuousLinearMap.id_comp, hAB₂]
  refine ⟨A, B, c, hA, hB, hAB, fun f => (hmA₂ _).trans (hmA₁ f),
    fun f => (hmB₁ _).trans (hmB₂ f), ?_⟩
  intro f hf
  have hbf : ‖B₂ f‖ ≤ ‖f‖ := by simpa only [one_mul] using B₂.le_of_opNorm_le hB₂ f
  have he : ‖A₂ ((S - D) (B₂ f))‖ ≤ (ε / 4) * ‖f‖ := by
    calc
      _ ≤ ‖(S - D) (B₂ f)‖ := by
        simpa only [one_mul] using A₂.le_of_opNorm_le hA₂ ((S - D) (B₂ f))
      _ ≤ (ε / 4) * ‖B₂ f‖ := (S - D).le_of_opNorm_le herror (B₂ f)
      _ ≤ _ := mul_le_mul_of_nonneg_left hbf (by positivity)
  have hsc := hscalar f hf
  have heq : ((A.comp T).comp B) f - c • f =
      A₂ ((S - D) (B₂ f)) + (((A₂.comp D).comp B₂) f - c • f) := by
    simp only [A, B, S, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
    abel
  rw [heq]
  have h := norm_add_le (A₂ ((S - D) (B₂ f))) (((A₂.comp D).comp B₂) f - c • f)
  nlinarith

end ThesisCommon
