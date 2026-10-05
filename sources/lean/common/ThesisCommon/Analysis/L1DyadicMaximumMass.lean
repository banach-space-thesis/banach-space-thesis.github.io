import ThesisCommon.Analysis.L1FiniteMaximumMass
import ThesisCommon.Analysis.LpHaarDyadicMean
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Dyadic maximum-mass estimates for actual scalar interval L1 operators.
For any operator P, one of P and id-P has mass at least one half at
arbitrarily fine dyadic levels. This is a preliminary Enflo selection step;
no complemented-tree extraction is asserted here. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

def l1DyadicIndicator (n k : ℕ) : IntervalLp 𝕜 ⟨1, le_rfl⟩ :=
  indicatorConstLp 1 (show MeasurableSet (lpHaarCell n k) from measurableSet_Ioc)
    (measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _) 1

theorem l1DyadicIndicator_coe (n k : ℕ) :
    l1DyadicIndicator 𝕜 n k =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      (lpHaarCell n k).indicator (fun _ => (1 : 𝕜)) := indicatorConstLp_coeFn

theorem l1DyadicIndicator_norm (n k : ℕ) (hk : k < 2 ^ n) :
    ‖l1DyadicIndicator 𝕜 n k‖ = intervalLpDyadicRadius n := by
  rw [l1DyadicIndicator, norm_indicatorConstLp (by norm_num) (by norm_num),
    norm_one, one_mul, measureReal_def, lpHaarCell_measure n k hk,
    ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]
  simp

theorem l1DyadicIndicator_sum_norm (n : ℕ) :
    ∑ k ∈ Finset.range (2 ^ n), ‖l1DyadicIndicator 𝕜 n k‖ = 1 := by
  calc
    _ = ∑ _k ∈ Finset.range (2 ^ n), intervalLpDyadicRadius n :=
      Finset.sum_congr rfl (fun k hk => l1DyadicIndicator_norm 𝕜 n k (Finset.mem_range.mp hk))
    _ = 1 := by simpa using lpHaarRadius_cancel n

variable {𝕜} {X : Type*} [MeasurableSpace X] {μ : Measure X}

def l1DyadicMaximumMass (T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ) (n : ℕ) : ℝ :=
  l1FiniteMaximumMass (2 ^ n) (fun k => T (l1DyadicIndicator 𝕜 n k))

theorem l1DyadicMaximumMass_nonneg
    (T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ) (n : ℕ) :
    0 ≤ l1DyadicMaximumMass T n := l1FiniteMaximumMass_nonneg _ _

theorem l1DyadicImage_sum_norm_le
    (T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 ^ n), ‖T (l1DyadicIndicator 𝕜 n k)‖ ≤ ‖T‖ := by
  calc
    _ ≤ ∑ k ∈ Finset.range (2 ^ n), ‖T‖ * ‖l1DyadicIndicator 𝕜 n k‖ :=
      Finset.sum_le_sum (fun k _ => T.le_opNorm _)
    _ = ‖T‖ := by rw [← Finset.mul_sum, l1DyadicIndicator_sum_norm, mul_one]

theorem l1DyadicMaximumMass_le_norm
    (T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ) (n : ℕ) :
    l1DyadicMaximumMass T n ≤ ‖T‖ :=
  (l1FiniteMaximumMass_le_sum_norm _ _).trans (l1DyadicImage_sum_norm_le T n)

theorem l1DyadicMaximumMass_add_le
    (T S : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ) (n : ℕ) :
    l1DyadicMaximumMass (T + S) n ≤ l1DyadicMaximumMass T n + l1DyadicMaximumMass S n :=
  l1FiniteMaximumMass_add_le _ _ _

theorem l1DyadicMaximumMass_le_add_norm_sub
    (T S : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ) (n : ℕ) :
    l1DyadicMaximumMass T n ≤ l1DyadicMaximumMass S n + ‖T - S‖ := by
  exact (l1FiniteMaximumMass_le_add_sum_norm_sub (2 ^ n)
    (fun k => T (l1DyadicIndicator 𝕜 n k)) (fun k => S (l1DyadicIndicator 𝕜 n k))).trans
      (add_le_add le_rfl (l1DyadicImage_sum_norm_le (T - S) n))

theorem l1DyadicMaximumMass_lipschitz
    (T S : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ) (n : ℕ) :
    |l1DyadicMaximumMass T n - l1DyadicMaximumMass S n| ≤ ‖T - S‖ := by
  have h₁ := l1DyadicMaximumMass_le_add_norm_sub T S n
  have h₂ := l1DyadicMaximumMass_le_add_norm_sub S T n
  rw [norm_sub_rev S T] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem l1DyadicMaximumMass_id (n : ℕ) :
    l1DyadicMaximumMass (ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 ⟨1, le_rfl⟩)) n = 1 := by
  have hh : (fun x => finiteMaxNorm (2 ^ n) (fun k => l1DyadicIndicator 𝕜 n k x))
      =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun _ => (1 : ℝ) := by
    filter_upwards [ae_all_iff.mpr (fun k => l1DyadicIndicator_coe 𝕜 n k),
      lpHaarLevelCells_cover n] with x hx hcover
    apply le_antisymm
    · apply finiteMaxNorm_le zero_le_one
      intro k _
      rw [hx k]
      by_cases hk : x ∈ lpHaarCell n k <;> simp [hk]
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hcover
      have hb := norm_le_finiteMaxNorm (fun j => l1DyadicIndicator 𝕜 n j x) k.isLt
      simpa only [hx k, indicator_of_mem hk, norm_one] using hb
  change (∫ x, finiteMaxNorm (2 ^ n) (fun k => l1DyadicIndicator 𝕜 n k x)
    ∂(volume.restrict (Icc (0 : ℝ) 1))) = 1
  rw [integral_congr_ae hh, integral_const]
  simp [measureReal_def, Real.volume_Icc]

/-- Failure of maximum-mass decay is a concrete integral condition. -/
def HasPersistentDyadicMaximumMass
    (T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n, N ≤ n ∧ ε ≤ l1DyadicMaximumMass T n

theorem l1DyadicMaximumMass_projection_branch
    (P : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩) :
    (∀ N : ℕ, ∃ n, N ≤ n ∧ (1 / 2 : ℝ) ≤ l1DyadicMaximumMass P n) ∨
      (∀ N : ℕ, ∃ n, N ≤ n ∧ (1 / 2 : ℝ) ≤
        l1DyadicMaximumMass (ContinuousLinearMap.id 𝕜 _ - P) n) := by
  have hsum (n : ℕ) : 1 ≤ l1DyadicMaximumMass P n +
      l1DyadicMaximumMass (ContinuousLinearMap.id 𝕜 _ - P) n := by
    have h := l1DyadicMaximumMass_add_le P (ContinuousLinearMap.id 𝕜 _ - P) n
    rw [← add_sub_assoc, add_sub_cancel_left, l1DyadicMaximumMass_id] at h
    exact h
  by_cases hP : ∀ N : ℕ, ∃ n, N ≤ n ∧ (1 / 2 : ℝ) ≤ l1DyadicMaximumMass P n
  · exact Or.inl hP
  · push_neg at hP
    obtain ⟨N, hN⟩ := hP
    right
    intro M
    refine ⟨max M N, le_max_left _ _, ?_⟩
    have hsmall := hN (max M N) (le_max_right _ _)
    have hlarge := hsum (max M N)
    linarith

theorem hasPersistentDyadicMaximumMass_or_complement
    (P : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩) :
    HasPersistentDyadicMaximumMass P ∨
      HasPersistentDyadicMaximumMass (ContinuousLinearMap.id 𝕜 _ - P) := by
  rcases l1DyadicMaximumMass_projection_branch P with h | h
  · exact Or.inl ⟨1 / 2, by norm_num, h⟩
  · exact Or.inr ⟨1 / 2, by norm_num, h⟩

theorem hasPersistentDyadicMaximumMass_subsequence
    {T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ}
    (h : HasPersistentDyadicMaximumMass T) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ n, ε ≤ l1DyadicMaximumMass T (σ n) := by
  obtain ⟨ε, hε, h⟩ := h
  obtain ⟨σ, hσ, hs⟩ := extraction_of_frequently_atTop (frequently_atTop.mpr h)
  exact ⟨ε, hε, σ, hσ, hs⟩

theorem hasPersistentDyadicMaximumMass_not_tendsto_zero
    {T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ}
    (h : HasPersistentDyadicMaximumMass T) :
    ¬ Tendsto (l1DyadicMaximumMass T) atTop (𝓝 0) := by
  intro hz
  obtain ⟨ε, hε, σ, hσ, hs⟩ := hasPersistentDyadicMaximumMass_subsequence h
  have hh : ε ≤ 0 := ge_of_tendsto (hz.comp hσ.tendsto_atTop) (Eventually.of_forall hs)
  exact (not_le_of_gt hε) hh

/-- One fixed branch admits arbitrarily fine genuine dyadic partitions with
uniformly positive image maximum mass. The cell measures tend to zero. -/
theorem exists_l1DyadicMaximumMass_branch_levels
    (P : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩) :
    ∃ (T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩)
      (σ : ℕ → ℕ), (T = P ∨ T = ContinuousLinearMap.id 𝕜 _ - P) ∧ StrictMono σ ∧
      (∀ n, (1 / 2 : ℝ) ≤ l1DyadicMaximumMass T (σ n)) ∧
      Tendsto (fun n => intervalLpDyadicRadius (σ n)) atTop (𝓝 0) := by
  have hp : Tendsto intervalLpDyadicRadius atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  rcases l1DyadicMaximumMass_projection_branch P with h | h
  · obtain ⟨σ, hσ, hs⟩ := extraction_of_frequently_atTop (frequently_atTop.mpr h)
    exact ⟨P, σ, Or.inl rfl, hσ, hs, hp.comp hσ.tendsto_atTop⟩
  · obtain ⟨σ, hσ, hs⟩ := extraction_of_frequently_atTop (frequently_atTop.mpr h)
    exact ⟨ContinuousLinearMap.id 𝕜 _ - P, σ, Or.inr rfl, hσ, hs, hp.comp hσ.tendsto_atTop⟩

end ThesisCommon
