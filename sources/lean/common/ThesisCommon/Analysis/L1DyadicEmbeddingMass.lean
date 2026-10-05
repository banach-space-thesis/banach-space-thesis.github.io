import ThesisCommon.Analysis.L1DyadicMaximumMass
import ThesisCommon.Analysis.L1RademacherMaximumBound

/-! Every genuine bounded-below interval L1 embedding has uniformly positive
dyadic maximum mass. This is the Rademacher direction of the Enflo criterion,
proved for all RCLike fields without any disjoint-tree extraction premise. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem l1Dyadic_signed_sum_norm (n : ℕ) (ε : Fin (2 ^ n) → Bool) :
    ‖∑ i : Fin (2 ^ n), signedValue (ε i) (l1DyadicIndicator 𝕜 n i)‖ = 1 := by
  rw [l1_sign_sum_norm]
  have hh : (fun x => ‖∑ i : Fin (2 ^ n), signedValue (ε i) (l1DyadicIndicator 𝕜 n i x)‖)
      =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun _ => (1 : ℝ) := by
    filter_upwards [ae_all_iff.mpr (fun k : Fin (2 ^ n) => l1DyadicIndicator_coe 𝕜 n k),
      lpHaarLevelCells_cover n] with x hx hcover
    obtain ⟨k, hk⟩ := mem_iUnion.mp hcover
    have hs : (∑ i : Fin (2 ^ n), signedValue (ε i) (l1DyadicIndicator 𝕜 n i x)) =
        signedValue (ε k) (1 : 𝕜) := by
      rw [Finset.sum_eq_single k]
      · rw [hx k, indicator_of_mem hk]
      · intro j _ hj
        have hjx : x ∉ lpHaarCell n j :=
          fun hjx => Set.disjoint_left.mp (lpHaarLevelCells_disjoint n hj) hjx hk
        rw [hx j, indicator_of_notMem hjx]
        cases ε j <;> simp [signedValue]
      · simp
    rw [hs, norm_signedValue, norm_one]
  rw [integral_congr_ae hh, integral_const]
  simp [measureReal_def, Real.volume_Icc]

theorem map_l1Dyadic_signed_sum {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Y) (n : ℕ) (ε : Fin (2 ^ n) → Bool) :
    T (∑ i : Fin (2 ^ n), signedValue (ε i) (l1DyadicIndicator 𝕜 n i)) =
      ∑ i : Fin (2 ^ n), signedValue (ε i) (T (l1DyadicIndicator 𝕜 n i)) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases ε i <;> simp [signedValue]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem l1DyadicMaximumMass_mul_norm_of_boundedBelow
    (T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ) {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ f, c * ‖f‖ ≤ ‖T f‖) (n : ℕ) :
    c ^ 2 ≤ l1DyadicMaximumMass T n * ‖T‖ := by
  have hs (ε : Fin (2 ^ n) → Bool) :
      c ≤ ‖∑ i : Fin (2 ^ n), signedValue (ε i) (T (l1DyadicIndicator 𝕜 n i))‖ := by
    have h := hT (∑ i : Fin (2 ^ n), signedValue (ε i) (l1DyadicIndicator 𝕜 n i))
    rw [l1Dyadic_signed_sum_norm, mul_one, map_l1Dyadic_signed_sum] at h
    exact h
  have h := l1_lower_sign_norm_square_le (2 ^ n)
    (fun j => T (l1DyadicIndicator 𝕜 n j)) hc hs
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (l1DyadicMaximumMass_nonneg T n)
  rw [Fin.sum_univ_eq_sum_range (fun j => ‖T (l1DyadicIndicator 𝕜 n j)‖)]
  exact l1DyadicImage_sum_norm_le T n

theorem hasPersistentDyadicMaximumMass_of_boundedBelow
    (T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ) {c : ℝ} (hc : 0 < c)
    (hT : ∀ f, c * ‖f‖ ≤ ‖T f‖) : HasPersistentDyadicMaximumMass T := by
  have hden : 0 < ‖T‖ + 1 := by positivity
  refine ⟨c ^ 2 / (‖T‖ + 1), div_pos (sq_pos_of_pos hc) hden, ?_⟩
  intro N
  refine ⟨N, le_rfl, ?_⟩
  apply (div_le_iff₀ hden).mpr
  have h := l1DyadicMaximumMass_mul_norm_of_boundedBelow T hc.le hT N
  have hmass := l1DyadicMaximumMass_nonneg T N
  nlinarith

theorem not_boundedBelow_of_l1DyadicMaximumMass_tendsto_zero
    (T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ)
    (hvanish : Tendsto (l1DyadicMaximumMass T) atTop (𝓝 0)) {c : ℝ} (hc : 0 < c) :
    ¬ ∀ f, c * ‖f‖ ≤ ‖T f‖ := by
  intro hT
  exact hasPersistentDyadicMaximumMass_not_tendsto_zero
    (hasPersistentDyadicMaximumMass_of_boundedBelow T hc hT) hvanish

end ThesisCommon
