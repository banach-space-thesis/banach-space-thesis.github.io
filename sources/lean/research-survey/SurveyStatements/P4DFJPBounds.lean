import SurveyStatements.P4DFJPDiagonal

/-!
# The exact ambient range and the bounded generating set of the DFJP space
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Set Metric
open scoped ENNReal

namespace SurveyStatements.P4

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

lemma tsum_dfjpGauge_sq_le_of_mem {K : Set E} (h0 : (0 : E) ∈ K)
    {x : E} (hx : x ∈ K) :
    (∑' j : ℤ, (dfjpGauge K j x) ^ 2) ≤ (4 / 3 : ℝ) * (1 + ‖x‖ ^ 2) := by
  have hgeom : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : (∑' n : ℕ, (1 / 4 : ℝ) ^ n) = 4 / 3 := by
    rw [tsum_geometric_of_norm_lt_one]
    · norm_num
    · norm_num
  have hpos : Summable (fun n : ℕ => (dfjpGauge K (n : ℤ) x) ^ 2) :=
    hgeom.of_nonneg_of_le (fun _ => sq_nonneg _) (dfjpGauge_sq_le_positive_tail hx)
  have hneg : Summable (fun n : ℕ => (dfjpGauge K (-(n : ℤ)) x) ^ 2) :=
    (hgeom.mul_left (‖x‖ ^ 2)).of_nonneg_of_le
      (fun _ => sq_nonneg _) (dfjpGauge_sq_le_negative_tail h0 x)
  rw [Summable.tsum_of_nat_of_neg
    (f := fun j : ℤ => (dfjpGauge K j x) ^ 2) hpos hneg]
  calc
    _ ≤ (∑' n : ℕ, (dfjpGauge K (n : ℤ) x) ^ 2) +
        (∑' n : ℕ, (dfjpGauge K (-(n : ℤ)) x) ^ 2) :=
      sub_le_self _ (sq_nonneg _)
    _ ≤ (∑' n : ℕ, (1 / 4 : ℝ) ^ n) +
        (∑' n : ℕ, ‖x‖ ^ 2 * (1 / 4 : ℝ) ^ n) :=
      add_le_add (hpos.tsum_le_tsum (dfjpGauge_sq_le_positive_tail hx) hgeom)
        (hneg.tsum_le_tsum (dfjpGauge_sq_le_negative_tail h0 x) (hgeom.mul_left _))
    _ = (4 / 3 : ℝ) * (1 + ‖x‖ ^ 2) := by rw [tsum_mul_left, hsum]; ring

namespace DFJPSpace

variable (D : DFJPGaugeData 𝕜 E)

lemma summable_gauge_sq (f : DFJPSpace D) :
    Summable (fun j : ℤ => (dfjpGauge D.carrier j (inclusion D f)) ^ 2) := by
  have h := (lp.memℓp f.val).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  convert h using 1
  funext j
  rw [DFJPScale.norm_eq_gauge]
  change _ = (dfjpGauge D.carrier j ((DFJPScale.linearEquiv D j) (f.val j))) ^ 2
  rw [coordinate_eq]

/-- The ambient range is exactly the square-summable gauge set in the paper. -/
lemma range_inclusion : Set.range (inclusion D) =
    {x : E | Summable (fun j : ℤ => (dfjpGauge D.carrier j x) ^ 2)} := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    exact summable_gauge_sq D f
  · intro hx
    exact ⟨ofSummable D x hx, inclusion_ofSummable D x hx⟩

lemma norm_ofMem_sq_le {x : E} (hx : x ∈ D.carrier) :
    ‖ofMem D hx‖ ^ 2 ≤ (4 / 3 : ℝ) * (1 + D.normBound ^ 2) := by
  rw [norm_sq, inclusion_ofMem]
  exact (tsum_dfjpGauge_sq_le_of_mem D.zero_mem hx).trans
    (mul_le_mul_of_nonneg_left (add_le_add_left
      (pow_le_pow_left₀ (norm_nonneg x) (mem_closedBall_zero_iff.mp (D.norm_le hx)) 2) 1)
      (by norm_num))

lemma norm_ofMem_le {x : E} (hx : x ∈ D.carrier) :
    ‖ofMem D hx‖ ≤ Real.sqrt ((4 / 3 : ℝ) * (1 + D.normBound ^ 2)) := by
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  exact norm_ofMem_sq_le D hx

/-- The generating set is bounded in the actual square-summable gauge norm. -/
lemma generatingSet_isBounded : Bornology.IsBounded
    {f : DFJPSpace D | inclusion D f ∈ D.carrier} := by
  apply (Metric.isBounded_iff_subset_closedBall (0 : DFJPSpace D)).mpr
  refine ⟨Real.sqrt ((4 / 3 : ℝ) * (1 + D.normBound ^ 2)), ?_⟩
  intro f hf
  have heq : ofMem D hf = f := inclusion_injective D (by simp)
  rw [mem_closedBall_zero_iff, ← heq]
  exact norm_ofMem_le D hf

end DFJPSpace

end SurveyStatements.P4
