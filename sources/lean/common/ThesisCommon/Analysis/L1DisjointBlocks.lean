import ThesisCommon.Analysis.RCLikeL1DisjointCut
import Mathlib.Order.Interval.Finset.Basic

/-! Exact norm and disjointness identities for finite signed blocks of
almost-everywhere disjoint real or complex L1 functions. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}

theorem lOne_finset_smul_sum_coe (f : ℕ → Lp 𝕜 1 μ) (a : ℕ → 𝕜) (s : Finset ℕ) :
    (∑ i ∈ s, a i • f i : Lp 𝕜 1 μ) =ᵐ[μ] fun x => ∑ i ∈ s, a i • f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero 𝕜 1 μ)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (a i • f i) (∑ j ∈ s, a j • f j),
      Lp.coeFn_smul (a i) (f i), ih] with x hx hix hsx
    simpa only [Pi.add_apply, Pi.smul_apply, hix, hsx] using hx

private theorem norm_smul_sum_of_disjoint (f : ℕ → 𝕜) (a : ℕ → 𝕜) (s : Finset ℕ)
    (hd : Pairwise fun i j => f i = 0 ∨ f j = 0) :
    ‖∑ i ∈ s, a i • f i‖ = ∑ i ∈ s, ‖a i‖ * ‖f i‖ := by
  classical
  by_cases h : ∃ i ∈ s, f i ≠ 0
  · obtain ⟨i, hi, hfi⟩ := h
    have hz : ∀ j, j ≠ i → f j = 0 := fun j hji => (hd hji.symm).resolve_left hfi
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · exact norm_smul _ _
    · intro j _ hji
      simp [hz j hji]
    · simp [hi]
    · intro j _ hji
      simp [hz j hji]
    · simp [hi]
  · push_neg at h
    have hz : (∑ i ∈ s, a i • f i) = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [h i hi, smul_zero])
    rw [hz, norm_zero]
    symm
    exact Finset.sum_eq_zero fun i hi => by rw [h i hi, norm_zero, mul_zero]

private theorem ae_pairwise_all (f : ℕ → Lp 𝕜 1 μ)
    (hd : Pairwise fun i j => ∀ᵐ x ∂μ, f i x = 0 ∨ f j x = 0) :
    ∀ᵐ x ∂μ, Pairwise fun i j => f i x = 0 ∨ f j x = 0 := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Eventually.of_forall fun _ h => False.elim (h hij)
  · exact (hd hij).mono fun _ h _ => h

theorem norm_lOne_finset_smul_sum_of_ae_disjoint (f : ℕ → Lp 𝕜 1 μ)
    (hd : Pairwise fun i j => ∀ᵐ x ∂μ, f i x = 0 ∨ f j x = 0)
    (a : ℕ → 𝕜) (s : Finset ℕ) :
    ‖∑ i ∈ s, a i • f i‖ = ∑ i ∈ s, ‖a i‖ * ‖f i‖ := by
  classical
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ x, ∑ i ∈ s, ‖a i‖ * ‖f i x‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [lOne_finset_smul_sum_coe f a s, ae_pairwise_all f hd] with x hx hdx
      rw [hx]
      exact norm_smul_sum_of_disjoint (fun i => f i x) a s hdx
    _ = ∑ i ∈ s, ∫ x, ‖a i‖ * ‖f i x‖ ∂μ := by
      exact integral_finset_sum s (fun i _ => (L1.integrable_coeFn (f i)).norm.const_mul _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul, L1.norm_eq_integral_norm]

theorem ae_disjoint_lOne_block_sums (f : ℕ → Lp 𝕜 1 μ)
    (hd : Pairwise fun i j => ∀ᵐ x ∂μ, f i x = 0 ∨ f j x = 0)
    (a : ℕ → 𝕜) (s : ℕ → Finset ℕ) (hs : Pairwise fun n m => Disjoint (s n) (s m)) :
    Pairwise fun n m => ∀ᵐ x ∂μ,
      (∑ i ∈ s n, a i • f i : Lp 𝕜 1 μ) x = 0 ∨
      (∑ i ∈ s m, a i • f i : Lp 𝕜 1 μ) x = 0 := by
  classical
  intro n m hnm
  filter_upwards [lOne_finset_smul_sum_coe f a (s n),
    lOne_finset_smul_sum_coe f a (s m), ae_pairwise_all f hd] with x hn hm hx
  rw [hn, hm]
  by_cases h : ∃ i ∈ s n, f i x ≠ 0
  · obtain ⟨i, hi, hfi⟩ := h
    right
    apply Finset.sum_eq_zero
    intro j hj
    have hij : i ≠ j := by
      rintro rfl
      exact Finset.disjoint_left.mp (hs hnm) hi hj
    rw [(hx hij).resolve_left hfi, smul_zero]
  · left
    push_neg at h
    exact Finset.sum_eq_zero fun i hi => by rw [h i hi, smul_zero]

theorem pairwise_disjoint_successive_Ioc {i : ℕ → ℕ} (hi : StrictMono i) :
    Pairwise fun n m => Disjoint (Finset.Ioc (i n) (i (n + 1)))
      (Finset.Ioc (i m) (i (m + 1))) := by
  intro n m hnm
  apply Finset.disjoint_left.mpr
  intro j hn hm
  simp only [Finset.mem_Ioc] at hn hm
  rcases lt_or_gt_of_ne hnm with h | h
  · have hle : i (n + 1) ≤ i m := hi.monotone (Nat.succ_le_of_lt h)
    omega
  · have hle : i (m + 1) ≤ i n := hi.monotone (Nat.succ_le_of_lt h)
    omega

/-- Convex averages over successive blocks preserve scalar limits. -/
theorem tendsto_weighted_successive_blocks {f : ℕ → ℝ} {c : ℝ}
    (hf : Tendsto f atTop (𝓝 c)) (i : ℕ → ℕ) (hi : StrictMono i)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hsum : ∀ n, (∑ j ∈ Finset.Ioc (i n) (i (n + 1)), a j) = 1) :
    Tendsto (fun n => ∑ j ∈ Finset.Ioc (i n) (i (n + 1)), a j * f j) atTop (𝓝 c) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hf (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have heq : (∑ j ∈ Finset.Ioc (i n) (i (n + 1)), a j * f j) - c =
      ∑ j ∈ Finset.Ioc (i n) (i (n + 1)), a j * (f j - c) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [Real.dist_eq, heq]
  calc
    _ ≤ ∑ j ∈ Finset.Ioc (i n) (i (n + 1)), |a j * (f j - c)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Ioc (i n) (i (n + 1)), a j * (ε / 2) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (ha j)]
      apply mul_le_mul_of_nonneg_left _ (ha j)
      have hnj : n ≤ j := (hi.id_le n).trans (Finset.mem_Ioc.mp hj).1.le
      exact (hN j (hn.trans hnj)).le
    _ = ε / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
    _ < ε := by linarith

end ThesisCommon
