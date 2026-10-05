import ThesisCommon.Analysis.EllOneColumns
import ThesisCommon.Analysis.PositiveMatrix

/-! Scalar phase alignment for bounded finite sums and the absolute row
bound for functionals on actual scalar ell_infinity. No representation of
an arbitrary functional by its unit-vector coefficients is asserted.
-/
noncomputable section
open Filter Topology
open scoped BigOperators ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The manuscript's finite synthesis estimate; the empty maximum is zero. -/
def HasBoundedFiniteSums {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (K : ℝ) : Prop :=
  ∀ (F : Finset ℕ) (a : ℕ → 𝕜),
    ‖∑ n ∈ F, a n • x n‖ ≤ K * ((F.sup (fun n => ‖a n‖₊) : NNReal) : ℝ)

theorem HasBoundedFiniteSums.unit_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {x : ℕ → E} {K : ℝ}
    (h : HasBoundedFiniteSums (𝕜 := 𝕜) x K) (hK : 0 ≤ K)
    (F : Finset ℕ) (a : ℕ → 𝕜) (ha : ∀ n ∈ F, ‖a n‖ ≤ 1) :
    ‖∑ n ∈ F, a n • x n‖ ≤ K := by
  have hh : F.sup (fun n => ‖a n‖₊) ≤ 1 := Finset.sup_le (fun n hn => ha n hn)
  have hh' : ((F.sup (fun n => ‖a n‖₊) : NNReal) : ℝ) ≤ 1 := hh
  exact (h F a).trans ((mul_le_mul_of_nonneg_left hh' hK).trans_eq (mul_one K))

/-- Align phases before applying the functional; this works over R or C. -/
theorem sum_norm_apply_le_of_unit_sums {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (φ : E →L[𝕜] 𝕜)
    (x : ℕ → E) (K : ℝ)
    (h : ∀ (F : Finset ℕ) (a : ℕ → 𝕜), (∀ n ∈ F, ‖a n‖ ≤ 1) →
      ‖∑ n ∈ F, a n • x n‖ ≤ K) (F : Finset ℕ) :
    ∑ n ∈ F, ‖φ (x n)‖ ≤ ‖φ‖ * K := by
  choose a ha hphase using fun n => RCLike.exists_norm_eq_mul_self (φ (x n))
  have heq : φ (∑ n ∈ F, a n • x n) = ((∑ n ∈ F, ‖φ (x n)‖ : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun n _ => (hphase n).symm)
  calc
    _ = ‖φ (∑ n ∈ F, a n • x n)‖ := by
      rw [heq, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    _ ≤ ‖φ‖ * ‖∑ n ∈ F, a n • x n‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * K := mul_le_mul_of_nonneg_left (h F a (fun n _ => (ha n).le)) (norm_nonneg _)

theorem infinity_norm_sum_single_le (F : Finset ℕ) (a : ℕ → 𝕜) :
    ‖∑ n ∈ F, a n • (lp.single ∞ n (1 : 𝕜) : lp (fun _ : ℕ => 𝕜) ∞)‖ ≤
      ((F.sup (fun n => ‖a n‖₊) : NNReal) : ℝ) := by
  classical
  apply lp.norm_le_of_forall_le (NNReal.coe_nonneg _)
  intro m
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · exact Finset.le_sup (f := fun n => ‖a n‖₊) hm
  · simpa only [norm_zero] using NNReal.coe_nonneg (F.sup (fun n => ‖a n‖₊))

theorem infinity_functional_row_sum_le
    (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜) (F : Finset ℕ) :
    ∑ n ∈ F, ‖φ (lp.single ∞ n (1 : 𝕜))‖ ≤ ‖φ‖ := by
  have h : HasBoundedFiniteSums (fun n => (lp.single ∞ n (1 : 𝕜) :
      lp (fun _ : ℕ => 𝕜) ∞)) 1 := fun F a => by
    simpa only [one_mul] using infinity_norm_sum_single_le F a
  simpa only [mul_one] using sum_norm_apply_le_of_unit_sums φ _ 1
    (h.unit_bound zero_le_one) F

theorem infinity_functional_row_summable
    (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜) :
    Summable (fun n => ‖φ (lp.single ∞ n (1 : 𝕜))‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (infinity_functional_row_sum_le φ)

theorem infinity_functional_row_tsum_le
    (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜) :
    (∑' n, ‖φ (lp.single ∞ n (1 : 𝕜))‖) ≤ ‖φ‖ :=
  (infinity_functional_row_summable φ).tsum_le_of_sum_le (infinity_functional_row_sum_le φ)

theorem bounded_finite_sums_coordinate_sum_le
    {x : ℕ → lp (fun _ : ℕ => 𝕜) ∞} {K : ℝ} (hK : 0 ≤ K)
    (h : HasBoundedFiniteSums (𝕜 := 𝕜) x K) (m : ℕ) (F : Finset ℕ) :
    ∑ n ∈ F, ‖x n m‖ ≤ K := by
  exact (sum_norm_apply_le_of_unit_sums (lpCoordinate (𝕜 := 𝕜) ∞ m) x K
    (h.unit_bound hK) F).trans
      ((mul_le_mul_of_nonneg_right (norm_lpCoordinate_le (𝕜 := 𝕜) (X := 𝕜) ∞ m) hK).trans_eq (one_mul _))

theorem bounded_finite_sums_coordinate_tendsto_zero
    {x : ℕ → lp (fun _ : ℕ => 𝕜) ∞} {K : ℝ} (hK : 0 ≤ K)
    (h : HasBoundedFiniteSums (𝕜 := 𝕜) x K) (m : ℕ) :
    Tendsto (fun n => x n m) atTop (𝓝 0) := by
  have hs : Summable (fun n => ‖x n m‖) := summable_of_sum_le
    (fun n => norm_nonneg _) (bounded_finite_sums_coordinate_sum_le hK h m)
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr hs.tendsto_atTop_zero

theorem bounded_finite_sums_small_future
    {x : ℕ → lp (fun _ : ℕ => 𝕜) ∞} {K : ℝ} (hK : 0 ≤ K)
    (h : HasBoundedFiniteSums (𝕜 := 𝕜) x K) {ε : ℝ} (hε : 0 < ε)
    {M : Set ℕ} (hM : M.Infinite) (N : ℕ) :
    ∃ n ∈ M, N < n ∧ {m ∈ M | ‖x n m‖ ≤ ε}.Infinite := by
  obtain ⟨n, hn, B, hB, hBA, _, hsmall⟩ := bounded_columns_small_row
    (fun n m => ‖x n m‖) (bounded_finite_sums_coordinate_sum_le hK h) hε (infinite_above hM N)
  exact ⟨n, hn.1, hn.2, Set.Infinite.mono (fun m hm => ⟨(hBA hm).1, (hsmall m hm).le⟩) hB⟩

end ThesisCommon



