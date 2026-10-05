import JLMS.PairedDisjointFunctions
import JLMS.PointDifferenceEvaluation

/-!
# A contractively complemented copy of c₀ in C₀(K)

For infinite scattered locally compact Hausdorff K, choose distinct points
converging in the one-point compactification and disjoint compact clopen
neighborhoods along a subsequence. Paired indicators define the inclusion;
half-difference evaluations define the projection. Both are contractions
and their composition is the identity, hence both norms are exactly one.

The infinite-K hypothesis corrects the finite-space exception in Lemma 8.1;
the project's finite cases already cover those K separately.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

theorem exists_cZero_retract_of_pointNeighborhoods
    (p : ℕ → K) (x : OnePoint K)
    (ht : Tendsto (fun n => (p n : OnePoint K)) atTop (𝓝 x))
    (U : ℕ → Set K) (hU : ∀ n, IsClopen (U n)) (hcU : ∀ n, IsCompact (U n))
    (hpU : ∀ n, p n ∈ U n) (hUd : Pairwise fun i j => Disjoint (U i) (U j)) :
    ∃ A : cZero 𝕜 →L[𝕜] CZero 𝕜 K, ∃ B : CZero 𝕜 K →L[𝕜] cZero 𝕜,
      B.comp A = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 := by
  classical
  let η (n : ℕ) := clopenIndicator (𝕜 := 𝕜) (U n) (hU n) (hcU n)
  have hη : ∀ n, ‖η n‖ ≤ 1 := fun n => norm_clopenIndicator_le _ _ _
  have hηd : Pairwise fun i j => Disjoint (Function.support (η i)) (Function.support (η j)) := by
    intro i j hij
    apply (hUd hij).mono
    · intro y hy
      by_contra hout
      exact hy (by simp [η, hout])
    · intro y hy
      by_contra hout
      exact hy (by simp [η, hout])
  let γ := pairedDisjointFunction η
  have hγ : ∀ n, ‖γ n‖ ≤ 1 := pairedDisjointFunction_norm_le η hη hηd
  have hγd : Pairwise fun i j => Disjoint (Function.support (γ i)) (Function.support (γ j)) :=
    pairedDisjointFunction_disjoint η hηd
  have hηp (i j : ℕ) : η i (p j) = if j = i then 1 else 0 :=
    pointNeighborhood_indicator_apply p U hU hcU hpU hUd i j
  have heven (i j : ℕ) : γ i (p (2 * j)) = if j = i then 1 else 0 := by
    change η (2 * i) (p (2 * j)) - η (2 * i + 1) (p (2 * j)) = _
    rw [hηp, hηp]
    have hodd : 2 * j ≠ 2 * i + 1 := by omega
    have heq : 2 * j = 2 * i ↔ j = i := by omega
    simp [hodd, heq]
  have hodd (i j : ℕ) : γ i (p (2 * j + 1)) = if j = i then -1 else 0 := by
    change η (2 * i) (p (2 * j + 1)) - η (2 * i + 1) (p (2 * j + 1)) = _
    rw [hηp, hηp]
    have heven : 2 * j + 1 ≠ 2 * i := by omega
    have heq : 2 * j + 1 = 2 * i + 1 ↔ j = i := by omega
    by_cases hji : j = i <;> simp [heven, heq, hji]
  let A := disjointSynthesis γ hγ hγd
  let B := pointDifferenceEvaluation (𝕜 := 𝕜) p x ht
  have hAe (a : cZero 𝕜) (n : ℕ) : A a (p (2 * n)) = a n := by
    change evaluation (p (2 * n)) (∑' i, a i • γ i) = a n
    rw [(evaluation (p (2 * n))).map_tsum (summable_smul_disjoint γ hγ hγd a)]
    simp only [map_smul, evaluation_apply, heven, smul_eq_mul]
    rw [tsum_eq_single n]
    · simp
    · intro i hi
      simp [Ne.symm hi]
  have hAo (a : cZero 𝕜) (n : ℕ) : A a (p (2 * n + 1)) = -a n := by
    change evaluation (p (2 * n + 1)) (∑' i, a i • γ i) = -a n
    rw [(evaluation (p (2 * n + 1))).map_tsum (summable_smul_disjoint γ hγ hγd a)]
    simp only [map_smul, evaluation_apply, hodd, smul_eq_mul]
    rw [tsum_eq_single n]
    · simp
    · intro i hi
      simp [Ne.symm hi]
  refine ⟨A, B, ?_, norm_disjointSynthesis_le γ hγ hγd, norm_pointDifferenceEvaluation_le p x ht⟩
  apply ContinuousLinearMap.ext
  intro a
  ext n
  change ((1 / 2 : ℝ) : 𝕜) * (A a (p (2 * n)) - A a (p (2 * n + 1))) = a n
  rw [hAe, hAo]
  have hhalf : (((1 / 2 : ℝ) : 𝕜)) = (1 / 2 : 𝕜) := by
    simp [RCLike.ofReal_div, RCLike.ofReal_ofNat]
  rw [hhalf]
  ring

/-- Lemma 8.1 for infinite K, with the actual norm-one maps. -/
theorem exists_cZero_retract [Infinite K] (hK : IsScattered K) :
    ∃ A : cZero 𝕜 →L[𝕜] CZero 𝕜 K, ∃ B : CZero 𝕜 K →L[𝕜] cZero 𝕜,
      B.comp A = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧ ‖A‖ = 1 ∧ ‖B‖ = 1 := by
  obtain ⟨p, hp, x, ht⟩ := exists_injective_onePoint_convergent hK
  obtain ⟨s, hs, U, hU, hcU, hpU, hUd⟩ := exists_disjoint_pointNeighborhoods hK p hp x ht
  obtain ⟨A, B, hBA, hA, hB⟩ := exists_cZero_retract_of_pointNeighborhoods (𝕜 := 𝕜) (p ∘ s) x
    (ht.comp hs.tendsto_atTop) U hU hcU hpU hUd
  have hprod : 1 ≤ ‖B‖ * ‖A‖ := by
    have h := essentialNorm_le_norm (ContinuousLinearMap.id 𝕜 (cZero 𝕜))
    rw [essentialNorm_cZero_identity] at h
    exact h.trans (by rw [← hBA]; exact ContinuousLinearMap.opNorm_comp_le B A)
  refine ⟨A, B, hBA, le_antisymm hA ?_, le_antisymm hB ?_⟩ <;>
    nlinarith [norm_nonneg A, norm_nonneg B]

end JLMS
