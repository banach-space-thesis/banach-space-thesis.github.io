import Posets.SzlenkOrdinalBoundsProjection
import Mathlib.SetTheory.Ordinal.Arithmetic

/-! Iterating a uniform dual-ball radius decrease through blocks of ordinal
length κ gives the Szlenk bound κω. -/
noncomputable section
open Set Topology
namespace Posets
variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem szlenkIterate_add_subset (ε : ℝ) (K : Set (WeakDual 𝕜 E)) (α β : Ordinal) :
    szlenkIterate ε K (α + β) ⊆ szlenkIterate ε (szlenkIterate ε K α) β := by
  induction β using SuccOrder.limitRecOn with
  | isMin β hβ =>
      obtain rfl := hβ.eq_bot
      simp only [Ordinal.bot_eq_zero, add_zero, szlenkIterate_zero, Set.Subset.refl]
  | succ β hβ ih =>
      rw [Ordinal.add_succ, szlenkIterate_succ, szlenkIterate_succ]
      exact szlenkDeriv_mono ε ih
  | isSuccLimit β hβ ih =>
      intro x hx
      rw [szlenkIterate_limit ε _ β hβ]
      apply mem_iInter.mpr
      intro γ
      exact ih γ.val γ.property (szlenkIterate_antitone ε K
        (add_le_add_left γ.property.le α) hx)

theorem szlenkIterate_ball_mul_nat {κ : Ordinal} {ε c : ℝ}
    (hshrink : ∀ R : ℝ, szlenkIterate ε (szlenkDualBall (𝕜 := 𝕜) (E := E) R) κ ⊆
      szlenkDualBall (R - c)) (R : ℝ) (n : ℕ) :
    szlenkIterate ε (szlenkDualBall (𝕜 := 𝕜) (E := E) R) (κ * n) ⊆
      szlenkDualBall (R - n * c) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      have hh := (szlenkIterate_add_subset ε (szlenkDualBall R) (κ * n) κ).trans
        ((szlenkIterate_mono ε κ ih).trans (hshrink (R - n * c)))
      convert hh using 1
      congr 1
      push_cast
      ring

theorem operatorSzlenkBound_of_ball_shrink {κ : Ordinal}
    (hshrink : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ R : ℝ, szlenkIterate ε (szlenkDualBall (𝕜 := 𝕜) (E := E) R) κ ⊆
        szlenkDualBall (R - c)) :
    OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 E) (κ * Ordinal.omega0) := by
  rw [OperatorSzlenkBound, adjointUnitBall_id]
  intro ε hε
  obtain ⟨c, hc, hstep⟩ := hshrink ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / c)
  have hnc : 1 < (n : ℝ) * c := (div_lt_iff₀ hc).mp hn
  have he : weakStarUnitBall 𝕜 E = szlenkDualBall 1 := by
    ext φ
    simp only [weakStarUnitBall, szlenkDualBall, Set.mem_preimage,
      Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq]
  rw [he]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro φ hφ
  have hφn := szlenkIterate_antitone ε (szlenkDualBall (𝕜 := 𝕜) (E := E) 1)
    (mul_le_mul_left' (Ordinal.nat_lt_omega0 n).le κ) hφ
  have hb := szlenkIterate_ball_mul_nat hstep 1 n hφn
  change ‖WeakDual.toStrongDual φ‖ ≤ 1 - (n : ℝ) * c at hb
  have := norm_nonneg (WeakDual.toStrongDual φ)
  linarith

end Posets
