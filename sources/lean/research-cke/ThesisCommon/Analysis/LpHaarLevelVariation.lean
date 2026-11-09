import ThesisCommon.Analysis.LpHaarDyadic
import ThesisCommon.Analysis.HaarFunctionalVariation

/-! Uniform variation and vanishing variance of the real or complex
dyadic Haar atoms tested against any bounded Lp functional. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon

theorem lpHaar_coeFn_finset_sum {𝕜 α ι : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} (s : Finset ι) (f : ι → Lp 𝕜 p μ) :
    (fun x => (∑ i ∈ s, f i) x) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero 𝕜 p μ
  | @insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hx hs
    change (f i + ∑ j ∈ s, f j) x = f i x + (∑ j ∈ s, f j) x at hx
    rw [hs] at hx
    exact hx

theorem norm_sum_le_of_disjoint_values {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (v : ι → E)
    (hd : ∀ i j, i ≠ j → v i = 0 ∨ v j = 0) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ i, ‖v i‖ ≤ C) : ‖∑ i, v i‖ ≤ C := by
  by_cases h : ∃ i, v i ≠ 0
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · exact hv i
    · intro j _ hji
      exact (hd i j hji.symm).resolve_left hi
    · simp
  · push_neg at h
    simpa [h] using hC

theorem lpHaarFunction_zero_of_not_mem (𝕜 : Type*) [RCLike 𝕜]
    (n k : ℕ) (x : ℝ) (hx : x ∉ lpHaarCell n k) :
    lpHaarFunction 𝕜 (lpHaarCell (n + 1) (2 * k))
      (lpHaarCell (n + 1) (2 * k + 1)) x = 0 := by
  have hn : x ∉ lpHaarCell (n + 1) (2 * k) ∪ lpHaarCell (n + 1) (2 * k + 1) := by
    rwa [lpHaarCell_children]
  simp only [mem_union, not_or] at hn
  simp [lpHaarFunction, hn.1, hn.2]

local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

theorem lpHaarDyadic_level_sum_norm_le (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n : ℕ) (a : Fin (2 ^ n) → 𝕜) (ha : ∀ k, ‖a k‖ ≤ 1) :
    ‖∑ k, a k • lpHaarDyadic 𝕜 p n k‖ ≤ 1 := by
  have hbound : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ‖(∑ k, a k • lpHaarDyadic 𝕜 p n k : IntervalLp 𝕜 p) x‖ ≤ 1 := by
    have hsm := ae_all_iff.mpr (fun k : Fin (2 ^ n) =>
      Lp.coeFn_smul (a k) (lpHaarDyadic 𝕜 p n k))
    have hv := ae_all_iff.mpr (fun k : Fin (2 ^ n) =>
      lpHaarVector_coe (𝕜 := 𝕜) (p := p.val) (μ := volume.restrict (Icc (0 : ℝ) 1))
        (lpHaarCell (n + 1) (2 * k)) (lpHaarCell (n + 1) (2 * k + 1))
        measurableSet_Ioc measurableSet_Ioc)
    filter_upwards [lpHaar_coeFn_finset_sum Finset.univ (fun k => a k • lpHaarDyadic 𝕜 p n k),
      hsm, hv] with x hsum hsm hv
    rw [hsum]
    have hraw (k : Fin (2 ^ n)) : lpHaarDyadic 𝕜 p n k x =
        lpHaarFunction 𝕜 (lpHaarCell (n + 1) (2 * k))
          (lpHaarCell (n + 1) (2 * k + 1)) x := hv k
    refine norm_sum_le_of_disjoint_values _ ?_ zero_le_one ?_
    · intro i j hij
      by_cases hi : x ∈ lpHaarCell n i
      · right
        have hj : x ∉ lpHaarCell n j := fun hj =>
          Set.disjoint_left.mp (lpHaarCell_disjoint_sameLevel n
            (fun h => hij (Fin.ext h))) hi hj
        rw [hsm j]
        change a j * lpHaarDyadic 𝕜 p n j x = 0
        rw [hraw j, lpHaarFunction_zero_of_not_mem 𝕜 n j x hj]
        simp
      · left
        rw [hsm i]
        change a i * lpHaarDyadic 𝕜 p n i x = 0
        rw [hraw i, lpHaarFunction_zero_of_not_mem 𝕜 n i x hi]
        simp
    · intro k
      rw [hsm k]
      change ‖a k * lpHaarDyadic 𝕜 p n k x‖ ≤ 1
      rw [hraw k, norm_mul]
      rw [lpHaarFunction_norm _ _ (lpHaarCell_disjoint_sameLevel (n + 1) (by omega))]
      by_cases hx : x ∈ lpHaarCell (n + 1) (2 * k) ∪ lpHaarCell (n + 1) (2 * k + 1)
      · simpa [hx] using ha k
      · simp [hx]
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound zero_le_one hbound

theorem lpHaarDyadic_functional_variation_le (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (φ : IntervalLp 𝕜 p →L[𝕜] 𝕜) (n : ℕ) :
    (∑ k : Fin (2 ^ n), ‖φ (lpHaarDyadic 𝕜 p n k)‖) ≤ ‖φ‖ := by
  simpa using haar_functional_variation_le (fun k : Fin (2 ^ n) => lpHaarDyadic 𝕜 p n k)
    φ (lpHaarDyadic_level_sum_norm_le 𝕜 p n)

theorem lpHaarDyadic_functional_variance_le (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (hp : p.val ≠ ∞) (φ : IntervalLp 𝕜 p →L[𝕜] 𝕜) (n : ℕ) :
    (∑ k : Fin (2 ^ n), ‖φ (lpHaarDyadic 𝕜 p n k)‖ ^ 2) ≤
      ‖φ‖ ^ 2 * intervalLpDyadicRadius n ^ (1 / p.val.toReal) := by
  have h := haar_functional_variance_le (fun k : Fin (2 ^ n) => lpHaarDyadic 𝕜 p n k)
    φ (Real.rpow_nonneg (intervalLpDyadicRadius_pos n).le _)
    (fun k => (lpHaarDyadic_norm 𝕜 p hp n k k.isLt).le)
    (lpHaarDyadic_level_sum_norm_le 𝕜 p n)
  convert h using 1 <;> ring

end ThesisCommon
