import SurveyStatements.P5L1VariationPermutations
import Mathlib.GroupTheory.Perm.Basic

/-! Reynolds averages built from the actual terminal dyadic transfer maps.
The finite group acts on terminal cells, and no unconditionality assumption
is made about the L¹ Haar system. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [Fintype G]

def terminalReynolds (M : ℕ) (ρ : G →* Equiv.Perm (Fin (2 ^ M)))
    (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 :=
  (Fintype.card G : 𝕜)⁻¹ • ∑ g : G,
    (terminalPermutation 𝕜 M (ρ g⁻¹)).comp
      (R.comp (terminalPermutation 𝕜 M (ρ g)))

theorem terminalReynolds_apply (M : ℕ) (ρ : G →* Equiv.Perm (Fin (2 ^ M)))
    (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) (f : IntervalL1 𝕜) :
    terminalReynolds M ρ R f = (Fintype.card G : 𝕜)⁻¹ • ∑ g : G,
      terminalPermutation 𝕜 M (ρ g⁻¹) (R (terminalPermutation 𝕜 M (ρ g) f)) := by
  simp only [terminalReynolds, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]

theorem terminalReynolds_norm_le (M : ℕ) (ρ : G →* Equiv.Perm (Fin (2 ^ M)))
    (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) :
    ‖terminalReynolds M ρ R‖ ≤ ‖R‖ := by
  have hc : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R)
  intro f
  rw [terminalReynolds_apply, norm_smul, norm_inv, RCLike.norm_natCast]
  have ht (g : G) :
      ‖terminalPermutation 𝕜 M (ρ g⁻¹) (R (terminalPermutation 𝕜 M (ρ g) f))‖ ≤
        ‖R‖ * ‖f‖ := by
    calc
      _ ≤ ‖R (terminalPermutation 𝕜 M (ρ g) f)‖ := by
        have h := (terminalPermutation 𝕜 M (ρ g⁻¹)).le_opNorm
          (R (terminalPermutation 𝕜 M (ρ g) f))
        exact h.trans (by
          simpa using mul_le_mul_of_nonneg_right
            (terminalPermutation_norm_le 𝕜 M (ρ g⁻¹)) (norm_nonneg _))
      _ ≤ ‖R‖ * ‖terminalPermutation 𝕜 M (ρ g) f‖ := R.le_opNorm _
      _ ≤ ‖R‖ * ‖f‖ := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg R)
        have h := (terminalPermutation 𝕜 M (ρ g)).le_opNorm f
        exact h.trans (by
          simpa using mul_le_mul_of_nonneg_right
            (terminalPermutation_norm_le 𝕜 M (ρ g)) (norm_nonneg f))
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖terminalPermutation 𝕜 M (ρ g⁻¹)
        (R (terminalPermutation 𝕜 M (ρ g) f))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ _g : G, (‖R‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun g _ => ht g)) (inv_nonneg.mpr hc.le)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

theorem terminalReynolds_commutes (M : ℕ) (ρ : G →* Equiv.Perm (Fin (2 ^ M)))
    (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) (a : G) :
    (terminalPermutation 𝕜 M (ρ a)).comp (terminalReynolds M ρ R) =
      (terminalReynolds M ρ R).comp (terminalPermutation 𝕜 M (ρ a)) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply]
  rw [terminalReynolds_apply, map_smul, map_sum, terminalReynolds_apply]
  congr 1
  have hterms (g : G) :
      terminalPermutation 𝕜 M (ρ a)
          (terminalPermutation 𝕜 M (ρ g⁻¹)
            (R (terminalPermutation 𝕜 M (ρ g) f))) =
      terminalPermutation 𝕜 M (ρ ((g * a⁻¹)⁻¹))
        (R (terminalPermutation 𝕜 M (ρ (g * a⁻¹))
          (terminalPermutation 𝕜 M (ρ a) f))) := by
    have hm (σ τ : Equiv.Perm (Fin (2 ^ M))) (x : IntervalL1 𝕜) :
        terminalPermutation 𝕜 M σ (terminalPermutation 𝕜 M τ x) =
          terminalPermutation 𝕜 M (σ * τ) x :=
      congrArg (fun L : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 => L x)
        (terminalPermutation_mul 𝕜 M σ τ)
    rw [hm, hm]
    simp only [mul_inv_rev, inv_inv, map_mul, map_inv]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [Finset.sum_congr rfl (fun g _ => hterms g)]
  exact Fintype.sum_equiv (Equiv.mulRight a⁻¹) _ _ (fun _ => rfl)

theorem terminalReynolds_coordinate_zero_of_input_flip
    (M : ℕ) (ρ : G →* Equiv.Perm (Fin (2 ^ M)))
    (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) (a : G)
    (v : IntervalL1 𝕜) (q : IntervalL1 𝕜 →L[𝕜] 𝕜)
    (hv : terminalPermutation 𝕜 M (ρ a) v = -v)
    (hq : ∀ y : IntervalL1 𝕜, q (terminalPermutation 𝕜 M (ρ a) y) = q y) :
    q (terminalReynolds M ρ R v) = 0 := by
  have h := congrArg q (congrArg
    (fun L : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 => L v)
    (terminalReynolds_commutes M ρ R a))
  change q (terminalPermutation 𝕜 M (ρ a) (terminalReynolds M ρ R v)) =
    q (terminalReynolds M ρ R (terminalPermutation 𝕜 M (ρ a) v)) at h
  rw [hq, hv, map_neg, map_neg] at h
  exact CharZero.eq_neg_self_iff.mp h

theorem terminalReynolds_coordinate_zero_of_output_flip
    (M : ℕ) (ρ : G →* Equiv.Perm (Fin (2 ^ M)))
    (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) (a : G)
    (v : IntervalL1 𝕜) (q : IntervalL1 𝕜 →L[𝕜] 𝕜)
    (hv : terminalPermutation 𝕜 M (ρ a) v = v)
    (hq : ∀ y : IntervalL1 𝕜, q (terminalPermutation 𝕜 M (ρ a) y) = -q y) :
    q (terminalReynolds M ρ R v) = 0 := by
  have h := congrArg q (congrArg
    (fun L : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 => L v)
    (terminalReynolds_commutes M ρ R a))
  change q (terminalPermutation 𝕜 M (ρ a) (terminalReynolds M ρ R v)) =
    q (terminalReynolds M ρ R (terminalPermutation 𝕜 M (ρ a) v)) at h
  rw [hq, hv] at h
  exact CharZero.neg_eq_self_iff.mp h

end SurveyStatements.P5L1Variation

