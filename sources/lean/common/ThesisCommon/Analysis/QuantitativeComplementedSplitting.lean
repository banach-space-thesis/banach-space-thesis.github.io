import ThesisCommon.Analysis.IsomorphismBoundCalculus
import ThesisCommon.Analysis.QuantitativeDecompositionDefinitions

/-! The first step of Appendix A with its printed constant. The maps are
the actual projection/kernel splitting followed by the supplied rescaled
isomorphism, with the genuine finite-p product norm, including p=∞. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem lpProductNorm_le_add (r : BanachExponent) (z : BanachDirectSum r X Y) :
    ‖z‖ ≤ ‖z.fst‖ + ‖z.snd‖ := by
  have he : z = WithLp.toLp r.val (z.fst, (0 : Y)) + WithLp.toLp r.val ((0 : X), z.snd) := by
    apply WithLp.ofLp_injective r.val
    change (z.fst, z.snd) = (z.fst + 0, 0 + z.snd)
    simp
  calc
    ‖z‖ = ‖WithLp.toLp r.val (z.fst, (0 : Y)) + WithLp.toLp r.val ((0 : X), z.snd)‖ :=
      congrArg norm he
    _ ≤ ‖WithLp.toLp r.val (z.fst, (0 : Y))‖ + ‖WithLp.toLp r.val ((0 : X), z.snd)‖ := norm_add_le _ _
    _ = ‖z.fst‖ + ‖z.snd‖ := by rw [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd]

theorem complemented_lp_splitting_withBound (r : BanachExponent) (E : Submodule 𝕜 X)
    (P : X →L[𝕜] E) (hP : ∀ y : E, P (y : X) = y)
    {Cproj Ciso : ℝ} (hproj : 0 ≤ Cproj) (hiso : 1 ≤ Ciso)
    (hPn : ‖P‖ ≤ Cproj) (hE : IsomorphicWithBound 𝕜 Y E Ciso) :
    IsomorphicWithBound 𝕜 X
      (BanachDirectSum r Y (LinearMap.ker P.toLinearMap)) (decompositionAuxBound Cproj Ciso) := by
  obtain ⟨S, hS⟩ := hE.exists_sqrt_normBound hiso
  let F := LinearMap.ker P.toLinearMap
  let e₀ := ContinuousLinearEquiv.equivOfRightInverse P E.subtypeL hP
  let Φ : X ≃L[𝕜] BanachDirectSum r Y F :=
    (e₀.trans (S.symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 F))).trans
      (WithLp.prodContinuousLinearEquiv r.val 𝕜 Y F).symm
  let A : ℝ := Real.sqrt Ciso * Cproj + 1 + Cproj
  let B : ℝ := 2 * (Real.sqrt Ciso + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hPbound (x : X) : ‖P x‖ ≤ Cproj * ‖x‖ := P.le_of_opNorm_le hPn x
  have hΦ : ‖Φ.toContinuousLinearMap‖ ≤ A := by
    apply ContinuousLinearMap.opNorm_le_bound _ hA
    intro x
    refine (lpProductNorm_le_add r (Φ x)).trans ?_
    change ‖S.symm (P x)‖ + ‖x - (P x : X)‖ ≤ A * ‖x‖
    have h₁ := (hS.2 (P x)).trans
      (mul_le_mul_of_nonneg_left (hPbound x) (Real.sqrt_nonneg Ciso))
    have h₂ := (norm_sub_le x (P x : X)).trans (add_le_add_left (hPbound x) ‖x‖)
    dsimp [A]
    nlinarith
  have hΨ : ‖Φ.symm.toContinuousLinearMap‖ ≤ B := by
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro z
    change ‖(S z.fst : X) + (z.snd : X)‖ ≤ B * ‖z‖
    have h₁ := (hS.1 z.fst).trans
      (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le (p := r.val) (α := Y) (β := F) z)
        (Real.sqrt_nonneg Ciso))
    have h₂ := WithLp.norm_snd_le (p := r.val) (α := Y) (β := F) z
    refine (norm_add_le _ _).trans ?_
    change ‖S z.fst‖ + ‖z.snd‖ ≤ B * ‖z‖
    apply (add_le_add h₁ h₂).trans
    dsimp [B]
    nlinarith [norm_nonneg z, mul_nonneg (Real.sqrt_nonneg Ciso) (norm_nonneg z)]
  refine ⟨Φ, ?_⟩
  have h := mul_le_mul hΦ hΨ (norm_nonneg Φ.symm.toContinuousLinearMap) hA
  have he : A * B = decompositionAuxBound Cproj Ciso := by
    dsimp [A, B, decompositionAuxBound]
    ring
  exact h.trans_eq he

theorem HasComplementedCopyWithBound.exists_lp_decomposition
    {Cproj Ciso : ℝ} (h : HasComplementedCopyWithBound 𝕜 X Y Cproj Ciso)
    (r : BanachExponent) (hproj : 0 ≤ Cproj) (hiso : 1 ≤ Ciso) :
    ∃ (E : Submodule 𝕜 X) (P : X →L[𝕜] E),
      IsomorphicWithBound 𝕜 X (BanachDirectSum r Y (LinearMap.ker P.toLinearMap))
        (decompositionAuxBound Cproj Ciso) := by
  obtain ⟨E, _hclosed, P, hP, hPn, hE⟩ := h
  exact ⟨E, P, complemented_lp_splitting_withBound r E P hP hproj hiso hPn hE⟩

end ThesisCommon
