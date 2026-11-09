import PL1.BochnerResolvents
import PL1.ExponentialTail
import PL1.CompactWalshMultiplier

/-!
# Exact smoothing factorization of the truncated resolvents

The equality is proved for the actual Bochner averages on Haar L1. Its
conditional Lp-to-L2 corollary needs only a genuine extension of one noise
operator on the common L1/Lp domain. Hypercontractivity itself is not assumed
to have been proved by this file.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace PL1.Noise
open Walsh ExponentialTime

variable (𝕜 : Type*) [RCLike 𝕜] (rates : ℕ → ℝ≥0)

theorem truncatedResolventL1_character (t : PositiveTime) (ε : ℝ≥0) (F : Finset ℕ) :
    truncatedResolventL1 𝕜 rates t ε (scalarCharacterLp 𝕜 1 F) =
      ((Real.exp (-(ε : ℝ) * ((t : ℝ)⁻¹ + rateSum rates F)) *
        (1 + (t : ℝ) * rateSum rates F)⁻¹ : ℝ) : 𝕜) • scalarCharacterLp 𝕜 1 F := by
  rw [truncatedResolventL1_apply]
  simp only [noiseL1_character, integral_smul_const]
  rw [integral_laplace_Ici_ofReal t.property _ (rateSum_nonneg rates F)]

/-- Removing the initial time interval is exactly exponential damping followed
by a resolvent and the noise operator at the cutoff time. -/
theorem truncatedResolventL1_eq_resolvent_comp_noise (t : PositiveTime) (ε : ℝ≥0) :
    truncatedResolventL1 𝕜 rates t ε =
      ((Real.exp (-(ε : ℝ) / (t : ℝ)) : ℝ) : 𝕜) •
        (resolventL1 𝕜 rates t).comp (noiseL1 𝕜 rates ε) := by
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  simp only [truncatedResolventL1_character, smul_apply,
    ContinuousLinearMap.comp_apply, noiseL1_character, map_smul,
    resolventL1_scalarCharacter, smul_smul]
  congr 1
  rw [show -(ε : ℝ) * ((t : ℝ)⁻¹ + rateSum rates F) =
      -(ε : ℝ) / (t : ℝ) + -(ε : ℝ) * rateSum rates F by ring,
    Real.exp_add]
  simp only [RCLike.ofReal_mul]
  ring

theorem truncatedResolventL1_eq_noise_comp_resolvent (t : PositiveTime) (ε : ℝ≥0) :
    truncatedResolventL1 𝕜 rates t ε =
      ((Real.exp (-(ε : ℝ) / (t : ℝ)) : ℝ) : 𝕜) •
        (noiseL1 𝕜 rates ε).comp (resolventL1 𝕜 rates t) := by
  rw [truncatedResolventL1_eq_resolvent_comp_noise, noiseL1_resolvent_commute]

variable {𝕜 rates}

/-- A compatible smoothing extension at the cutoff time gives a bounded
Hilbert-valued extension of the actual truncated L1 resolvent. -/
def truncatedResolventLpToL2 (t : PositiveTime) (ε : ℝ≥0)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (H : Lp 𝕜 p haar →L[𝕜] Lp 𝕜 2 haar) :
    Lp 𝕜 p haar →L[𝕜] Lp 𝕜 2 haar :=
  ((Real.exp (-(ε : ℝ) / (t : ℝ)) : ℝ) : 𝕜) •
    (WalshMultiplier.actualResolventL2 𝕜 rates t).comp H

theorem truncatedResolventLpToL2_overlap (t : PositiveTime) (ε : ℝ≥0)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (H : Lp 𝕜 p haar →L[𝕜] Lp 𝕜 2 haar)
    (hH : ∀ (g : Lp 𝕜 1 haar) (f : Lp 𝕜 p haar),
      g =ᵐ[haar] f → noiseL1 𝕜 rates ε g = l2ToL1 (H f))
    (g : Lp 𝕜 1 haar) (f : Lp 𝕜 p haar) (hgf : g =ᵐ[haar] f) :
    truncatedResolventL1 𝕜 rates t ε g =
      l2ToL1 (truncatedResolventLpToL2 (rates := rates) t ε H f) := by
  rw [truncatedResolventL1_eq_resolvent_comp_noise]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    truncatedResolventLpToL2, map_smul]
  rw [hH g f hgf]
  congr 1
  exact (DFunLike.congr_fun (WalshMultiplier.actualResolventL2_l2ToL1 𝕜 rates t) (H f)).symm

theorem norm_truncatedResolventLpToL2_le (t : PositiveTime) (ε : ℝ≥0)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (H : Lp 𝕜 p haar →L[𝕜] Lp 𝕜 2 haar) :
    ‖truncatedResolventLpToL2 (rates := rates) t ε H‖ ≤
      Real.exp (-(ε : ℝ) / (t : ℝ)) * ‖H‖ := by
  rw [truncatedResolventLpToL2, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (WalshMultiplier.norm_actualResolventL2_le_one 𝕜 rates t) (norm_nonneg H))

end PL1.Noise
