import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Signed successive blocks of a weakly convergent sequence. The construction
uses the equality of weak and norm closures of real convex sets (Mazur's
theorem), and does not assume a convex-block selection principle. -/
noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace ThesisCommon

private theorem sum_Ioc_shift {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (N m : ℕ) :
    (∑ i ∈ Finset.Ioc N (N + 1 + m), f (i - (N + 1))) =
      ∑ j ∈ Finset.range (m + 1), f j := by
  apply Finset.sum_bij (fun i _ => i - (N + 1))
  · intro i hi
    simp only [Finset.mem_Ioc] at hi
    simp only [Finset.mem_range]
    omega
  · intro i hi j hj hij
    simp only [Finset.mem_Ioc] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨N + 1 + j, ?_, by omega⟩
    simp only [Finset.mem_Ioc]
    omega
  · intros
    rfl

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- Every tail of a weakly convergent sequence has a finite convex combination
arbitrarily close in norm to its weak limit. Coefficients are real, even for a
complex space. The finite combination is padded with zeros to a genuine interval. -/
theorem exists_convex_tail_block {x : ℕ → E} {l : E}
    (hx : Tendsto (fun n => toWeakSpace 𝕜 E (x n)) atTop
      (𝓝 (toWeakSpace 𝕜 E l))) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, N < M ∧ ∃ w : ℕ → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∑ i ∈ Finset.Ioc N M, w i) = 1 ∧
      ‖(∑ i ∈ Finset.Ioc N M, w i • x i) - l‖ < ε := by
  classical
  let v : ℕ → E := fun j => x (N + 1 + j)
  have hv : Tendsto (fun j => toWeakSpace 𝕜 E (v j)) atTop
      (𝓝 (toWeakSpace 𝕜 E l)) := by
    simpa [v, Nat.add_comm] using hx.comp (tendsto_add_atTop_nat (N + 1))
  have hlw : toWeakSpace 𝕜 E l ∈
      closure (toWeakSpace 𝕜 E '' convexHull ℝ (range v)) :=
    mem_closure_of_tendsto hv (Filter.Eventually.of_forall fun j =>
      ⟨v j, subset_convexHull ℝ (range v) (mem_range_self j), rfl⟩)
  rw [← (convex_convexHull ℝ (range v)).toWeakSpace_closure 𝕜] at hlw
  obtain ⟨z, hz, hzl⟩ := hlw
  have hzl' : z = l := (toWeakSpace 𝕜 E).injective hzl
  subst z
  obtain ⟨y, hy, hyε⟩ := Metric.mem_closure_iff.mp hz ε hε
  rw [convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨s, a, ha, hsum, rfl⟩ := hy
  rw [Finset.affineCombination_eq_linear_combination s v a hsum] at hyε
  have hs : s ⊆ Finset.range (s.sup id + 1) := by
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
  let b : ℕ → ℝ := fun j => if j ∈ s then a j else 0
  have hb : ∀ j, 0 ≤ b j := by
    intro j
    simp only [b]
    split_ifs with hj
    · exact ha j hj
    · exact le_rfl
  have hb_sum : (∑ j ∈ Finset.range (s.sup id + 1), b j) = 1 := by
    rw [← Finset.sum_subset hs]
    · simpa [b] using hsum
    · intro j _ hj
      simp [b, hj]
  have hb_vec : (∑ j ∈ Finset.range (s.sup id + 1), b j • v j) =
      ∑ j ∈ s, a j • v j := by
    rw [← Finset.sum_subset hs]
    · apply Finset.sum_congr rfl
      intro j hj
      simp [b, hj]
    · intro j _ hj
      simp [b, hj]
  refine ⟨N + 1 + s.sup id, by omega, fun i => b (i - (N + 1)),
    fun i => hb _, ?_, ?_⟩
  · exact (sum_Ioc_shift b N (s.sup id)).trans hb_sum
  · have heq : (∑ i ∈ Finset.Ioc N (N + 1 + s.sup id),
        b (i - (N + 1)) • x i) = ∑ j ∈ s, a j • v j := by
      calc
        _ = ∑ i ∈ Finset.Ioc N (N + 1 + s.sup id),
            b (i - (N + 1)) • v (i - (N + 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' := (Finset.mem_Ioc.mp hi).1
          simp only [v]
          congr 2
          omega
        _ = _ := (sum_Ioc_shift (fun j => b j • v j) N (s.sup id)).trans hb_vec
    rw [heq]
    simpa only [dist_eq_norm, norm_sub_rev] using hyε

private theorem sum_Ioc_split {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) {N M L : ℕ} (hNM : N ≤ M) (hML : M ≤ L) :
    (∑ i ∈ Finset.Ioc N L, f i) =
      (∑ i ∈ Finset.Ioc N M, f i) + ∑ i ∈ Finset.Ioc M L, f i := by
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hNM hML, Finset.sum_union]
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' := (Finset.mem_Ioc.mp hi).2
  have hj' := (Finset.mem_Ioc.mp hj).1
  omega

/-- A normalized signed combination on a finite interval in any prescribed
tail can have arbitrarily small norm. Its positive and negative coefficients
are obtained from two consecutive convex combinations near the same limit. -/
theorem exists_normalized_signed_tail_block {x : ℕ → E} {l : E}
    (hx : Tendsto (fun n => toWeakSpace 𝕜 E (x n)) atTop
      (𝓝 (toWeakSpace 𝕜 E l))) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℕ, N < L ∧ ∃ a : ℕ → ℝ,
      (∑ i ∈ Finset.Ioc N L, |a i|) = 1 ∧
      ‖∑ i ∈ Finset.Ioc N L, a i • x i‖ < ε := by
  classical
  obtain ⟨M, hNM, a, ha, ha_sum, haε⟩ := exists_convex_tail_block hx N hε
  obtain ⟨L, hML, b, hb, hb_sum, hbε⟩ := exists_convex_tail_block hx M hε
  let c : ℕ → ℝ := fun i => if i ≤ M then (1 / 2 : ℝ) * a i else -(1 / 2 : ℝ) * b i
  have hc₁ (i : ℕ) (hi : i ∈ Finset.Ioc N M) : c i = (1 / 2 : ℝ) * a i := by
    simp [c, (Finset.mem_Ioc.mp hi).2]
  have hc₂ (i : ℕ) (hi : i ∈ Finset.Ioc M L) : c i = -(1 / 2 : ℝ) * b i := by
    simp [c, not_le.mpr (Finset.mem_Ioc.mp hi).1]
  refine ⟨L, hNM.trans hML, c, ?_, ?_⟩
  · rw [sum_Ioc_split _ hNM.le hML.le]
    have h₁ : (∑ i ∈ Finset.Ioc N M, |c i|) = (1 / 2 : ℝ) := by
      calc
        _ = ∑ i ∈ Finset.Ioc N M, (1 / 2 : ℝ) * a i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hc₁ i hi, abs_of_nonneg (mul_nonneg (by norm_num) (ha i))]
        _ = _ := by rw [← Finset.mul_sum, ha_sum]; norm_num
    have h₂ : (∑ i ∈ Finset.Ioc M L, |c i|) = (1 / 2 : ℝ) := by
      calc
        _ = ∑ i ∈ Finset.Ioc M L, (1 / 2 : ℝ) * b i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hc₂ i hi, neg_mul, abs_neg,
            abs_of_nonneg (mul_nonneg (by norm_num) (hb i))]
        _ = _ := by rw [← Finset.mul_sum, hb_sum]; norm_num
    rw [h₁, h₂]
    norm_num
  · have heq : (∑ i ∈ Finset.Ioc N L, c i • x i) =
        (1 / 2 : ℝ) • ((∑ i ∈ Finset.Ioc N M, a i • x i) -
          ∑ i ∈ Finset.Ioc M L, b i • x i) := by
      rw [sum_Ioc_split _ hNM.le hML.le]
      have h₁ : (∑ i ∈ Finset.Ioc N M, c i • x i) =
          (1 / 2 : ℝ) • ∑ i ∈ Finset.Ioc N M, a i • x i := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hc₁ i hi, mul_smul]
      have h₂ : (∑ i ∈ Finset.Ioc M L, c i • x i) =
          -(1 / 2 : ℝ) • ∑ i ∈ Finset.Ioc M L, b i • x i := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hc₂ i hi, mul_smul]
      rw [h₁, h₂, smul_sub, neg_smul, sub_eq_add_neg]
    rw [heq, norm_smul]
    norm_num only [norm_div, norm_one, Real.norm_ofNat]
    have hnorm := norm_sub_le
      ((∑ i ∈ Finset.Ioc N M, a i • x i) - l)
      ((∑ i ∈ Finset.Ioc M L, b i • x i) - l)
    rw [sub_sub_sub_cancel_right] at hnorm
    nlinarith

/-- Coefficients specified separately on successive, disjoint blocks can be
realized by a single sequence. Values outside those blocks are set to zero. -/
theorem exists_coefficients_on_successive_blocks {A : Type*} [Zero A]
    (i : ℕ → ℕ) (hi : StrictMono i) (a : ℕ → ℕ → A) :
    ∃ α : ℕ → A, ∀ n j, j ∈ Finset.Ioc (i n) (i (n + 1)) → α j = a n j := by
  classical
  have unique {j n m : ℕ}
      (hn : j ∈ Finset.Ioc (i n) (i (n + 1)))
      (hm : j ∈ Finset.Ioc (i m) (i (m + 1))) : n = m := by
    simp only [Finset.mem_Ioc] at hn hm
    rcases lt_trichotomy n m with h | h | h
    · have hle := hi.monotone (Nat.succ_le_of_lt h)
      change i (n + 1) ≤ i m at hle
      omega
    · exact h
    · have hle := hi.monotone (Nat.succ_le_of_lt h)
      change i (m + 1) ≤ i n at hle
      omega
  let α : ℕ → A := fun j => if h : ∃ n, j ∈ Finset.Ioc (i n) (i (n + 1))
    then a h.choose j else 0
  refine ⟨α, ?_⟩
  intro n j hj
  have hex : ∃ m, j ∈ Finset.Ioc (i m) (i (m + 1)) := ⟨n, hj⟩
  simp only [α, dif_pos hex]
  rw [unique hex.choose_spec hj]

/-- A weakly convergent sequence has normalized signed successive blocks
converging in norm to zero. There is one coefficient sequence for all blocks.
The proof works in normed spaces; completeness is not needed. -/
theorem exists_weaklyConvergent_signed_blocks_real {x : ℕ → E} {l : E}
    (hx : Tendsto (fun n => toWeakSpace 𝕜 E (x n)) atTop
      (𝓝 (toWeakSpace 𝕜 E l))) :
    ∃ (i : ℕ → ℕ) (α : ℕ → ℝ), StrictMono i ∧
      (∀ n, (∑ j ∈ Finset.Ioc (i n) (i (n + 1)), |α j|) = 1) ∧
      Tendsto (fun n => ∑ j ∈ Finset.Ioc (i n) (i (n + 1)), α j • x j)
        atTop (𝓝 0) := by
  classical
  have hblocks (n N : ℕ) : ∃ L : ℕ, N < L ∧ ∃ a : ℕ → ℝ,
      (∑ j ∈ Finset.Ioc N L, |a j|) = 1 ∧
      ‖∑ j ∈ Finset.Ioc N L, a j • x j‖ < 1 / ((n : ℝ) + 1) :=
    exists_normalized_signed_tail_block hx N (by positivity)
  choose L hL a ha hnorm using hblocks
  let i : ℕ → ℕ := Nat.rec 0 (fun n prev => L n prev)
  have hi_succ (n : ℕ) : i (n + 1) = L n (i n) := rfl
  have hi : StrictMono i := strictMono_nat_of_lt_succ (fun n => hL n (i n))
  obtain ⟨α, hα⟩ := exists_coefficients_on_successive_blocks i hi (fun n => a n (i n))
  have hsum (n : ℕ) : (∑ j ∈ Finset.Ioc (i n) (i (n + 1)), α j • x j) =
      ∑ j ∈ Finset.Ioc (i n) (L n (i n)), a n (i n) j • x j := by
    rw [← hi_succ]
    exact Finset.sum_congr rfl (fun j hj => by rw [hα n j hj])
  refine ⟨i, α, hi, ?_, ?_⟩
  · intro n
    calc
      _ = ∑ j ∈ Finset.Ioc (i n) (i (n + 1)), |a n (i n) j| :=
        Finset.sum_congr rfl (fun j hj => by rw [hα n j hj])
      _ = 1 := ha n (i n)
  · apply squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [hsum]
    exact (hnorm n (i n)).le

/-- Real-or-complex scalar version of the signed block theorem. The modulus
normalization is stated using scalar norms, which are absolute values over ℝ
and complex moduli over ℂ. The coefficients constructed here are real scalars
embedded into the scalar field. -/
theorem exists_weaklyConvergent_signed_blocks {x : ℕ → E} {l : E}
    (hx : Tendsto (fun n => toWeakSpace 𝕜 E (x n)) atTop
      (𝓝 (toWeakSpace 𝕜 E l))) :
    ∃ (i : ℕ → ℕ) (α : ℕ → 𝕜), StrictMono i ∧
      (∀ n, (∑ j ∈ Finset.Ioc (i n) (i (n + 1)), ‖α j‖) = 1) ∧
      Tendsto (fun n => ∑ j ∈ Finset.Ioc (i n) (i (n + 1)), α j • x j)
        atTop (𝓝 0) := by
  obtain ⟨i, α, hi, hα, hlim⟩ := exists_weaklyConvergent_signed_blocks_real hx
  refine ⟨i, fun j => (α j : 𝕜), hi, ?_, ?_⟩
  · simpa only [RCLike.norm_ofReal] using hα
  · simpa only [← RCLike.real_smul_eq_coe_smul] using hlim

end ThesisCommon
