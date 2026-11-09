import SurveyStatements.P1OrderedBlockObstruction
import SurveyStatements.P1WeakDifferences
import SurveyStatements.P1SuccessivePairs

/-! Expand normalized successive pairs into the original sequence. The
boundedness estimate includes prefixes ending between the two pair indices. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def normalizedPairBlock (s : ℕ → X) (p q : ℕ → ℕ) (n : ℕ) : ℕ →₀ ℂ :=
  Finsupp.single (p n) (‖s (p n) - s (q n)‖ : ℂ)⁻¹ -
    Finsupp.single (q n) (‖s (p n) - s (q n)‖ : ℂ)⁻¹

def normalizedPairCoefficients (s : ℕ → X) (p q : ℕ → ℕ)
    (a : ℕ → ℂ) : ℕ → ℂ :=
  orderedBlockCoefficients (normalizedPairBlock s p q) a

theorem normalizedPairBlock_support (s : ℕ → X) (p q : ℕ → ℕ)
    (hpair : ∀ n, p n < q n ∧ q n < p (n + 1)) :
    ∀ n i, i ∈ (normalizedPairBlock s p q n).support →
      p n ≤ i ∧ i < p (n + 1) := by
  intro n i hi
  have hi' := Finsupp.support_sub hi
  rcases Finset.mem_union.mp hi' with hi' | hi'
  · have hip : i = p n := by
      by_contra hne
      simp [Finsupp.mem_support_iff, Finsupp.single_apply, hne] at hi'
    subst i
    exact ⟨le_rfl, (hpair n).1.trans (hpair n).2⟩
  · have hiq : i = q n := by
      by_contra hne
      simp [Finsupp.mem_support_iff, Finsupp.single_apply, hne] at hi'
    subst i
    exact ⟨(hpair n).1.le, (hpair n).2⟩

theorem normalizedPairBlock_linearCombination (s : ℕ → X) (p q : ℕ → ℕ) (n : ℕ) :
    Finsupp.linearCombination ℂ s (normalizedPairBlock s p q n) =
      unitNormalize (s (p n) - s (q n)) := by
  simp [normalizedPairBlock, unitNormalize, smul_sub]

private theorem paired_prefix_decomposition
    (e : ℕ → X) (m : ℕ → ℕ) (hm : StrictMono m) (b : ℕ → ℕ →₀ ℂ)
    (hsupport : ∀ n i, i ∈ (b n).support → m n ≤ i ∧ i < m (n + 1))
    (a : ℕ → ℂ) {n N : ℕ} (hn : m n ≤ N) (hN : N ≤ m (n + 1)) :
    sequencePartialSum e (orderedBlockCoefficients b a) N =
      sequencePartialSum (fun k => Finsupp.linearCombination ℂ e (b k)) a n +
        a n • sequencePartialSum e (b n) N := by
  classical
  have hcoeff : ∀ i ∈ Finset.range N,
      orderedBlockCoefficients b a i = (∑ k ∈ Finset.range (n + 1), a k • b k) i := by
    intro i hi
    exact orderedBlockCoefficients_eq_prefix m hm b hsupport a
      ((Finset.mem_range.mp hi).trans_le hN)
  have hEq : sequencePartialSum e (orderedBlockCoefficients b a) N =
      ∑ k ∈ Finset.range (n + 1), a k • sequencePartialSum e (b k) N := by
    unfold sequencePartialSum
    calc
      _ = ∑ i ∈ Finset.range N,
          (∑ k ∈ Finset.range (n + 1), a k • b k) i • e i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoeff i hi]
      _ = _ := by
        simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
          Finset.sum_smul, mul_smul]
        rw [Finset.sum_comm]
        simp_rw [← Finset.smul_sum]
  rw [hEq, Finset.sum_range_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hsub : (b k).support ⊆ Finset.range N := by
    intro i hi
    have hi' := (hsupport k i hi).2
    have hkm := hm.monotone (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk))
    exact Finset.mem_range.mpr (hi'.trans_le (hkm.trans hn))
  rw [← linearCombination_eq_partialSum e (b k) hsub]

private theorem single_prefix (s : ℕ → X) (i N : ℕ) (z : ℂ) :
    sequencePartialSum s (Finsupp.single i z) N = if i < N then z • s i else 0 := by
  classical
  by_cases hi : i < N
  · simp [sequencePartialSum, Finsupp.single_apply, hi, Finset.sum_ite_eq']
  · simp [sequencePartialSum, Finsupp.single_apply, hi, Finset.sum_ite_eq']

theorem normalizedPairBlock_prefix (s : ℕ → X) (p q : ℕ → ℕ) (n N : ℕ) :
    sequencePartialSum s (normalizedPairBlock s p q n) N =
      (if p n < N then (‖s (p n) - s (q n)‖ : ℂ)⁻¹ • s (p n) else 0) -
        (if q n < N then (‖s (p n) - s (q n)‖ : ℂ)⁻¹ • s (q n) else 0) := by
  simp only [normalizedPairBlock, sequencePartialSum, Finsupp.sub_apply, sub_smul,
    Finset.sum_sub_distrib]
  exact congrArg₂ (· - ·) (single_prefix s (p n) N _) (single_prefix s (q n) N _)

theorem normalizedPairCoefficients_bounded (s : ℕ → X) (p q : ℕ → ℕ)
    (hpair : ∀ n, p n < q n ∧ q n < p (n + 1))
    {r M : ℝ} (hr : 0 < r) (hlower : ∀ n, r ≤ ‖s (p n) - s (q n)‖)
    (hM : ∀ n, ‖s n‖ ≤ M) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (hbound : HasBoundedPartialSums
      (fun n => unitNormalize (s (p n) - s (q n))) a) :
    HasBoundedPartialSums s (normalizedPairCoefficients s p q a) := by
  classical
  have hp : StrictMono p := (successivePairs_strictMono hpair).1
  have hsupport := normalizedPairBlock_support s p q hpair
  obtain ⟨B, hB⟩ := hbound
  have hB0 : 0 ≤ B := by simpa [sequencePartialSum] using hB 0
  have hM0 : 0 ≤ M := (norm_nonneg (s 0)).trans (hM 0)
  refine ⟨B + M / r, ?_⟩
  intro N
  by_cases hstart : N ≤ p 0
  · have hz : sequencePartialSum s (normalizedPairCoefficients s p q a) N = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hc := orderedBlockCoefficients_eq_prefix p hp (normalizedPairBlock s p q)
        hsupport a ((Finset.mem_range.mp hi).trans_le hstart)
      simp only [Finset.range_zero, Finset.sum_empty, Finsupp.zero_apply] at hc
      simp [normalizedPairCoefficients, hc]
    rw [hz, norm_zero]
    positivity
  · have hex : ∃ n, N < p (n + 1) :=
      ⟨N, (Nat.lt_succ_self N).trans_le (hp.id_le (N + 1))⟩
    let n := Nat.find hex
    have hN : N < p (n + 1) := Nat.find_spec hex
    have hn : p n ≤ N := by
      cases hn0 : n with
      | zero => omega
      | succ k =>
        have hk : ¬ N < p (k + 1) := Nat.find_min hex (by omega : k < Nat.find hex)
        simpa [hn0] using Nat.le_of_not_gt hk
    have hEq := paired_prefix_decomposition s p hp (normalizedPairBlock s p q)
      hsupport a hn hN.le
    simp only [normalizedPairBlock_linearCombination] at hEq
    change ‖sequencePartialSum s (orderedBlockCoefficients (normalizedPairBlock s p q) a) N‖ ≤ _
    rw [hEq, normalizedPairBlock_prefix]
    by_cases hq : q n < N
    · have hpn : p n < N := (hpair n).1.trans hq
      rw [if_pos hpn, if_pos hq, ← smul_sub]
      change ‖sequencePartialSum (fun n => unitNormalize (s (p n) - s (q n))) a n +
        a n • unitNormalize (s (p n) - s (q n))‖ ≤ _
      simpa only [sequencePartialSum, Finset.sum_range_succ] using
        (hB (n + 1)).trans (le_add_of_nonneg_right (div_nonneg hM0 hr.le))
    · rw [if_neg hq, sub_zero]
      by_cases hpn : p n < N
      · rw [if_pos hpn]
        calc
          _ ≤ ‖sequencePartialSum (fun n => unitNormalize (s (p n) - s (q n))) a n‖ +
              ‖a n • ((‖s (p n) - s (q n)‖ : ℂ)⁻¹ • s (p n))‖ := norm_add_le _ _
          _ ≤ B + M / r := by
            apply add_le_add (hB n)
            simp only [norm_smul, norm_inv, Complex.norm_real,
              Real.norm_of_nonneg (norm_nonneg _)]
            have hdpos := lt_of_lt_of_le hr (hlower n)
            have hinv : ‖s (p n) - s (q n)‖⁻¹ ≤ r⁻¹ :=
              (inv_le_inv₀ hdpos hr).mpr (hlower n)
            calc
              _ ≤ 1 * (r⁻¹ * M) :=
                mul_le_mul (ha n) (mul_le_mul hinv (hM _) (norm_nonneg _) (inv_nonneg.mpr hr.le))
                  (mul_nonneg (inv_nonneg.mpr hdpos.le) (norm_nonneg _)) (by norm_num)
              _ = M / r := by ring
      · simp only [if_neg hpn, smul_zero, add_zero]
        exact (hB n).trans (le_add_of_nonneg_right (div_nonneg hM0 hr.le))

theorem normalizedPairCoefficients_at_first (s : ℕ → X) (p q : ℕ → ℕ)
    (hpair : ∀ n, p n < q n ∧ q n < p (n + 1)) (a : ℕ → ℂ) (n : ℕ) :
    normalizedPairCoefficients s p q a (p n) =
      a n * (‖s (p n) - s (q n)‖ : ℂ)⁻¹ := by
  have hp : StrictMono p := (successivePairs_strictMono hpair).1
  have hEq := orderedBlockCoefficients_at_interval p hp (normalizedPairBlock s p q)
    (normalizedPairBlock_support s p q hpair) a
    (show p n ≤ p n ∧ p n < p (n + 1) from
      ⟨le_rfl, (hpair n).1.trans (hpair n).2⟩)
  simpa [normalizedPairCoefficients, normalizedPairBlock, (hpair n).1.ne] using hEq

/-- A bounded original sequence bounds the normalization denominators, so
vanishing expanded coefficients force vanishing pair coefficients. -/
theorem normalizedPairCoefficients_tendsto_zero_imp (s : ℕ → X) (p q : ℕ → ℕ)
    (hpair : ∀ n, p n < q n ∧ q n < p (n + 1))
    {r M : ℝ} (hr : 0 < r) (hlower : ∀ n, r ≤ ‖s (p n) - s (q n)‖)
    (hM : ∀ n, ‖s n‖ ≤ M) (a : ℕ → ℂ)
    (hzero : Tendsto (normalizedPairCoefficients s p q a) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  have hp : StrictMono p := (successivePairs_strictMono hpair).1
  have hM0 : 0 ≤ M := (norm_nonneg (s 0)).trans (hM 0)
  have hupper : ∀ n, ‖a n‖ ≤ (2 * M) *
      ‖normalizedPairCoefficients s p q a (p n)‖ := by
    intro n
    have hdpos : 0 < ‖s (p n) - s (q n)‖ := lt_of_lt_of_le hr (hlower n)
    have hdnz : (‖s (p n) - s (q n)‖ : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
    have haEq : a n = normalizedPairCoefficients s p q a (p n) *
        (‖s (p n) - s (q n)‖ : ℂ) := by
      rw [normalizedPairCoefficients_at_first s p q hpair a n]
      field_simp [hdnz]
    have hdle : ‖s (p n) - s (q n)‖ ≤ 2 * M :=
      (norm_sub_le _ _).trans (by linarith [hM (p n), hM (q n)])
    calc
      ‖a n‖ = ‖normalizedPairCoefficients s p q a (p n)‖ *
          ‖s (p n) - s (q n)‖ := by
        rw [haEq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      _ ≤ ‖normalizedPairCoefficients s p q a (p n)‖ * (2 * M) :=
        mul_le_mul_of_nonneg_left hdle (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hlim : Tendsto (fun n => (2 * M) *
      ‖normalizedPairCoefficients s p q a (p n)‖) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, norm_zero, mul_zero] using
      (hzero.comp hp.tendsto_atTop).norm.const_mul (2 * M)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun n => norm_nonneg _) hupper hlim)

theorem normalizedPairCoefficients_not_tendsto_zero (s : ℕ → X) (p q : ℕ → ℕ)
    (hpair : ∀ n, p n < q n ∧ q n < p (n + 1))
    {r M : ℝ} (hr : 0 < r) (hlower : ∀ n, r ≤ ‖s (p n) - s (q n)‖)
    (hM : ∀ n, ‖s n‖ ≤ M) (a : ℕ → ℂ) (ha : ¬ Tendsto a atTop (𝓝 0)) :
    ¬ Tendsto (normalizedPairCoefficients s p q a) atTop (𝓝 0) :=
  fun h => ha (normalizedPairCoefficients_tendsto_zero_imp s p q hpair hr hlower hM a h)

end SurveyStatements.P1
