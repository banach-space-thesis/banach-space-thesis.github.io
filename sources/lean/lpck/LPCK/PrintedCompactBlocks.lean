import ThesisCommon.Analysis.CompactScalarForward
import ThesisCommon.Analysis.CoordinateMasks
import Mathlib.Analysis.MeanInequalities

/-! Disjoint finite blocks of the scalar ℓp target. A noncompact operator
has infinitely many large disjoint adjoint tests; every signed or phased
sum of N tests grows at most as N^(1-1/p). -/
noncomputable section
open Filter Set
open scoped ENNReal Topology BigOperators
namespace LPCK.Printed
open ThesisCommon

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

private abbrev ScalarLp := lp (fun _ : ℕ => 𝕜) p

private def mask (A : Set ℕ) : ScalarLp (𝕜 := 𝕜) p →L[𝕜] ScalarLp (𝕜 := 𝕜) p :=
  lpCoordinateProjection p A

private theorem mask_finset_compact (A : Finset ℕ) :
    IsCompactOperator (mask (𝕜 := 𝕜) p (A : Set ℕ)) := by
  classical
  let F (i : ℕ) : ScalarLp (𝕜 := 𝕜) p →L[𝕜] ScalarLp (𝕜 := 𝕜) p :=
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) p i).comp (lpCoordinate p i)
  have hId : IsCompactOperator (ContinuousLinearMap.id 𝕜 𝕜) :=
    ⟨Metric.closedBall 0 1, isCompact_closedBall _ _, by simpa using
      (Metric.closedBall_mem_nhds (0 : 𝕜) zero_lt_one : Metric.closedBall 0 1 ∈ 𝓝 (0 : 𝕜))⟩
  have hF (i : ℕ) : IsCompactOperator (F i) := by
    exact (hId.comp_clm (lpCoordinate (𝕜 := 𝕜) (X := 𝕜) p i)).clm_comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) p i)
  have hsum (s : Finset ℕ) :
      IsCompactOperator (⇑(∑ i ∈ s, F i : ScalarLp (𝕜 := 𝕜) p →L[𝕜] ScalarLp (𝕜 := 𝕜) p)) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (isCompactOperator_zero (M₁ := ScalarLp (𝕜 := 𝕜) p) (M₂ := ScalarLp (𝕜 := 𝕜) p))
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hF i).add ih
  have heq : mask (𝕜 := 𝕜) p (A : Set ℕ) = ∑ i ∈ A, F i := by
    ext z : 1
    apply lp.ext
    funext i
    simp only [mask, lpCoordinateProjection_apply, ContinuousLinearMap.sum_apply, lp.coeFn_sum,
      Finset.sum_apply, F, ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
      lpCoordinate_apply, Finset.mem_coe]
    simp [lp.single_apply, Finset.sum_ite_eq', eq_comm]
  exact heq ▸ hsum A

private theorem mask_tail_comp_le (hp : 0 < p.toReal)
    (T : X →L[𝕜] ScalarLp (𝕜 := 𝕜) p) (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ k, ‖(mask p (↑(Finset.Ico N k) : Set ℕ)).comp T‖ ≤ δ) :
    ‖(mask p (Ici N)).comp T‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro x
  apply lp.norm_le_of_forall_sum_le hp (mul_nonneg hδ (norm_nonneg x))
  intro s
  let k := s.sup id + 1
  have hk (i : ℕ) (hi : i ∈ s) : i < k :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have heq (i : ℕ) (hi : i ∈ s) :
      mask p (Ici N) (T x) i = mask p (↑(Finset.Ico N k) : Set ℕ) (T x) i := by
    simp only [mask, lpCoordinateProjection_apply, mem_Ici, Finset.mem_coe, Finset.mem_Ico,
      hk i hi, and_true]
  calc
    _ = ∑ i ∈ s, ‖mask p (↑(Finset.Ico N k) : Set ℕ) (T x) i‖ ^ p.toReal := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ContinuousLinearMap.comp_apply, heq i hi]
    _ ≤ ‖mask p (↑(Finset.Ico N k) : Set ℕ) (T x)‖ ^ p.toReal :=
      lp.sum_rpow_le_norm_rpow hp _ _
    _ ≤ (δ * ‖x‖) ^ p.toReal := Real.rpow_le_rpow (norm_nonneg _)
      ((((mask p (↑(Finset.Ico N k) : Set ℕ)).comp T).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (h k) (norm_nonneg x))) hp.le

private theorem exists_large_finset_blocks (hp : 0 < p.toReal)
    (T : X →L[𝕜] ScalarLp (𝕜 := 𝕜) p) (hT : ¬ IsCompactOperator T) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ A : ℕ → Finset ℕ, Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      ∀ n, δ < ‖(mask p (A n : Set ℕ)).comp T‖ := by
  classical
  have hbad : ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ k, δ < ‖(mask p (↑(Finset.Ico N k) : Set ℕ)).comp T‖ := by
    by_contra! hn
    apply hT
    change T ∈ {S : X →L[𝕜] ScalarLp (𝕜 := 𝕜) p | IsCompactOperator S}
    rw [← isClosed_setOf_isCompactOperator.closure_eq]
    apply Metric.mem_closure_iff.2
    intro ε hε
    obtain ⟨N, hN⟩ := hn (ε/2) (half_pos hε)
    let P := mask (𝕜 := 𝕜) p (↑(Finset.range N) : Set ℕ)
    refine ⟨P.comp T, ?_, ?_⟩
    · change IsCompactOperator (P ∘ T)
      exact (mask_finset_compact (𝕜 := 𝕜) p (Finset.range N)).comp_clm T
    have heq : T - P.comp T = (mask p (Ici N)).comp T := by
      ext z : 1
      apply lp.ext
      funext n
      change T z n - P (T z) n = mask p (Ici N) (T z) n
      by_cases hn : n < N
      · simp [P, mask, hn, not_le_of_gt hn]
      · simp [P, mask, hn, le_of_not_gt hn]
    rw [dist_eq_norm, heq]
    exact (mask_tail_comp_le p hp T N (half_pos hε).le hN).trans_lt (half_lt_self hε)
  obtain ⟨δ, hδ, h⟩ := hbad
  choose k hk using h
  have hlt (N : ℕ) : N < k N := by
    by_contra! hle
    have hempty : (Finset.Ico N (k N) : Set ℕ) = ∅ := by
      ext n
      simp only [Finset.mem_coe, Finset.mem_Ico, mem_empty_iff_false, iff_false]
      omega
    have hz : mask (𝕜 := 𝕜) p ∅ = 0 := by
      ext z : 1
      apply lp.ext
      funext n
      simp [mask]
    have hn := hk N
    rw [hempty, hz, ContinuousLinearMap.zero_comp, norm_zero] at hn
    linarith
  let m : ℕ → ℕ := fun n => Nat.rec 0 (fun _ r => k r) n
  have hm : StrictMono m := strictMono_nat_of_lt_succ (fun n => hlt (m n))
  refine ⟨δ, hδ, fun n => Finset.Ico (m n) (m (n+1)), ?_, fun n => hk (m n)⟩
  intro i j hij
  apply Finset.disjoint_left.2
  intro a hai haj
  have hi := Finset.mem_Ico.1 hai
  have hj := Finset.mem_Ico.1 haj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge ((hm.monotone (Nat.succ_le_of_lt h)).trans hj.1)) hi.2
  · exact (not_lt_of_ge ((hm.monotone (Nat.succ_le_of_lt h)).trans hi.1)) hj.2

private theorem finite_block_norm_rpow (hp : 0 < p.toReal) (A : Finset ℕ)
    (z : ScalarLp (𝕜 := 𝕜) p) :
    ‖mask p (A : Set ℕ) z‖ ^ p.toReal = ∑ j ∈ A, ‖z j‖ ^ p.toReal := by
  rw [lp.norm_rpow_eq_tsum hp]
  rw [tsum_eq_sum (s := A) (fun j hj => by
    simp [mask, hj, Real.zero_rpow hp.ne'])]
  exact Finset.sum_congr rfl (fun j hj => by simp [mask, hj])

private theorem phased_block_bound (hp : 1 ≤ p.toReal) {N : ℕ}
    (A : Fin N → Finset ℕ) (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (φ : Fin N → ScalarLp (𝕜 := 𝕜) p →L[𝕜] 𝕜) (hφ : ∀ i, ‖φ i‖ ≤ 1)
    (c : Fin N → 𝕜) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ‖∑ i, c i • (φ i).comp (mask p (A i : Set ℕ))‖ ≤
      (N : ℝ) ^ ((p.toReal - 1) / p.toReal) := by
  classical
  have hp0 := zero_lt_one.trans_le hp
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  intro z
  let d (i : Fin N) := ‖mask p (A i : Set ℕ) z‖
  have hsum : (∑ i, d i ^ p.toReal) ≤ ‖z‖ ^ p.toReal := by
    simp only [d, finite_block_norm_rpow p hp0]
    rw [← Finset.sum_biUnion (fun i _ j _ h => hd h)]
    exact lp.sum_rpow_le_norm_rpow hp0 _ _
  have hmean := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := Finset.univ) (f := d) hp (fun _ _ => norm_nonneg _)
  rw [Finset.card_univ, Fintype.card_fin] at hmean
  have hpower := hmean.trans (mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hprod : (0 : ℝ) ≤ (N : ℝ) ^ ((p.toReal - 1) / p.toReal) * ‖z‖ := by positivity
  have hbound : (∑ i, d i) ≤ (N : ℝ) ^ ((p.toReal - 1) / p.toReal) * ‖z‖ := by
    by_contra! hh
    have hlt := Real.rpow_lt_rpow hprod hh hp0
    rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (norm_nonneg _),
      ← Real.rpow_mul (Nat.cast_nonneg _), div_mul_cancel₀ _ hp0.ne'] at hlt
    exact (not_lt_of_ge hpower) hlt
  apply le_trans _ hbound
  rw [ContinuousLinearMap.sum_apply]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, norm_smul]
  have h₁ : ‖c i‖ * ‖φ i (mask p (A i : Set ℕ) z)‖ ≤ ‖φ i (mask p (A i : Set ℕ) z)‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc i) (norm_nonneg (φ i (mask p (A i : Set ℕ) z)))
  have h₂ : ‖φ i (mask p (A i : Set ℕ) z)‖ ≤ ‖mask p (A i : Set ℕ) z‖ :=
    ((φ i).le_opNorm _).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hφ i) (norm_nonneg (mask p (A i : Set ℕ) z)))
  exact h₁.trans h₂

/-- A noncompact operator into finite scalar ℓp has disjoint large adjoint
tests with a uniform bound on every finite phased sum. -/
theorem exists_noncompact_adjoint_tests (hp : p ≠ ∞)
    (T : X →L[𝕜] ScalarLp (𝕜 := 𝕜) p) (hT : ¬ IsCompactOperator T) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ f : ℕ → ScalarLp (𝕜 := 𝕜) p →L[𝕜] 𝕜,
      (∀ n, δ ≤ ‖(f n).comp T‖) ∧
      ∀ N (e : Fin N ↪ ℕ) (c : Fin N → 𝕜), (∀ i, ‖c i‖ ≤ 1) →
        ‖∑ i, c i • f (e i)‖ ≤ (N : ℝ) ^ ((p.toReal - 1) / p.toReal) := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  obtain ⟨δ, hδ, A, hA, h⟩ := exists_large_finset_blocks p (zero_lt_one.trans_le hp1) T hT
  choose φ hφ hpost using fun n => exists_norming_postcomposition ((mask p (A n : Set ℕ)).comp T)
  refine ⟨δ / 2, half_pos hδ, fun n => (φ n).comp (mask p (A n : Set ℕ)), ?_, ?_⟩
  · intro n
    rw [ContinuousLinearMap.comp_assoc]
    linarith [h n, hpost n]
  · intro N e c hc
    exact phased_block_bound p hp1 (fun i => A (e i))
      (fun _ _ hne => hA (fun he => hne (e.injective he))) (fun i => φ (e i))
      (fun i => hφ (e i)) c hc

end LPCK.Printed
