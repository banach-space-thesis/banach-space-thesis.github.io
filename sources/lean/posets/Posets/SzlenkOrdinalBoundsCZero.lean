import Posets.SzlenkOrdinalBoundsCZeroCoordinates

/-! The actual Szlenk upper bound of scalar c₀. Each positive-scale
derivation reduces the dual-ball radius by a fixed positive amount. -/

noncomputable section
open Set Topology Filter ThesisCommon
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]

def cZeroDualBall (R : ℝ) : Set (WeakDual 𝕜 (cZero 𝕜)) :=
  {φ | ‖WeakDual.toStrongDual φ‖ ≤ R}

theorem szlenkDeriv_cZeroDualBall {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    szlenkDeriv ε (cZeroDualBall (𝕜 := 𝕜) R) ⊆ cZeroDualBall (R - ε / 4) := by
  intro x hx
  change ‖WeakDual.toStrongDual x‖ ≤ R - ε / 4
  by_contra hn
  obtain ⟨s, hs⟩ := cZeroDual_finite_mass_approx (WeakDual.toStrongDual x) (lt_of_not_ge hn)
  let U : Set (WeakDual 𝕜 (cZero 𝕜)) :=
    {φ | (∑ i ∈ s, ‖φ (JLMS.cZeroUnit 𝕜 i) - x (JLMS.cZeroUnit 𝕜 i)‖) < ε / 8}
  have hU : IsOpen U := isOpen_lt
    (continuous_finset_sum s (fun i _ => ((WeakDual.eval_continuous _).sub continuous_const).norm))
    continuous_const
  have hxU : x ∈ U := by
    change (∑ i ∈ s, ‖x (JLMS.cZeroUnit 𝕜 i) - x (JLMS.cZeroUnit 𝕜 i)‖) < ε / 8
    simp only [sub_self, norm_zero, Finset.sum_const_zero]
    positivity
  obtain ⟨a, ha, b, hb, hab⟩ := hx.2 U hU hxU
  have haR : ‖WeakDual.toStrongDual a‖ ≤ R := ha.1
  have hbR : ‖WeakDual.toStrongDual b‖ ≤ R := hb.1
  have haU : (∑ i ∈ s, ‖a (JLMS.cZeroUnit 𝕜 i) - x (JLMS.cZeroUnit 𝕜 i)‖) < ε / 8 := ha.2
  have hbU : (∑ i ∈ s, ‖b (JLMS.cZeroUnit 𝕜 i) - x (JLMS.cZeroUnit 𝕜 i)‖) < ε / 8 := hb.2
  have hahead := cZeroDual_head_norm_le (WeakDual.toStrongDual x) (WeakDual.toStrongDual a) s
  have hbhead := cZeroDual_head_norm_le (WeakDual.toStrongDual x) (WeakDual.toStrongDual b) s
  have htri := cZeroDual_head_distance_triangle (WeakDual.toStrongDual a)
    (WeakDual.toStrongDual b) (WeakDual.toStrongDual x) s
  have hnorm := cZeroDual_norm_sub_le_head_tails (WeakDual.toStrongDual a) (WeakDual.toStrongDual b) s
  simp only [WeakDual.toStrongDual_apply] at hs hahead hbhead htri hnorm
  have hea : (∑ i ∈ s, ‖x (JLMS.cZeroUnit 𝕜 i) - a (JLMS.cZeroUnit 𝕜 i)‖) =
      ∑ i ∈ s, ‖a (JLMS.cZeroUnit 𝕜 i) - x (JLMS.cZeroUnit 𝕜 i)‖ :=
    Finset.sum_congr rfl (fun i _ => norm_sub_rev _ _)
  have heb : (∑ i ∈ s, ‖x (JLMS.cZeroUnit 𝕜 i) - b (JLMS.cZeroUnit 𝕜 i)‖) =
      ∑ i ∈ s, ‖b (JLMS.cZeroUnit 𝕜 i) - x (JLMS.cZeroUnit 𝕜 i)‖ :=
    Finset.sum_congr rfl (fun i _ => norm_sub_rev _ _)
  rw [hea] at hahead
  rw [heb] at hbhead
  linarith

theorem szlenkIterate_cZeroDualBall_nat {ε : ℝ} (hε : 0 < ε) (R : ℝ) (n : ℕ) :
    szlenkIterate ε (cZeroDualBall (𝕜 := 𝕜) R) (n : Ordinal) ⊆
      cZeroDualBall (R - n * (ε / 4)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Ordinal.natCast_succ, szlenkIterate_succ]
      have hh := (szlenkDeriv_mono ε ih).trans (szlenkDeriv_cZeroDualBall hε (R - n * (ε / 4)))
      convert hh using 1
      congr 1
      push_cast
      ring

theorem cZero_szlenkBound_omega0 :
    OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 (cZero 𝕜)) Ordinal.omega0 := by
  rw [OperatorSzlenkBound, adjointUnitBall_id]
  intro ε hε
  have hball : weakStarUnitBall 𝕜 (cZero 𝕜) = cZeroDualBall 1 := by
    ext φ
    simp only [weakStarUnitBall, Set.mem_preimage, Metric.mem_closedBall,
      dist_zero_right, cZeroDualBall, Set.mem_setOf_eq]
  rw [hball]
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / ε)
  have hnε : 1 < (n : ℝ) * (ε / 4) := by
    have hh := (div_lt_iff₀ hε).mp hn
    nlinarith
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro φ hφ
  have hφn := szlenkIterate_antitone ε (cZeroDualBall (𝕜 := 𝕜) 1)
    (Ordinal.nat_lt_omega0 n).le hφ
  have hnorm := szlenkIterate_cZeroDualBall_nat hε 1 n hφn
  change ‖WeakDual.toStrongDual φ‖ ≤ 1 - (n : ℝ) * (ε / 4) at hnorm
  have := norm_nonneg (WeakDual.toStrongDual φ)
  linarith

end Posets
