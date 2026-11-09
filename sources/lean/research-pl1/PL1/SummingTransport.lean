import PL1.ComplementedLatticeSumming
import PL1.EnfloStarbirdProjection
import PL1.ComplementedLatticeBandEstimates

/-!
# Operator-ideal estimates and transfer through an actual complemented copy

The two ambient uniform summing estimates remain explicit hypotheses. These
lemmas prove their elementary transport with the exact embedding/retraction
norm factors; they do not assert Grothendieck's theorem.
-/

noncomputable section
open scoped BigOperators

namespace PL1.ComplementedLattice

section WeakBounds
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Testing the zero functional supplies the nonnegative weak bound, even for an empty family. -/
theorem weak_one_bound_nonneg (n : ℕ) (x : Fin n → E) (M : ℝ)
    (h : ∀ φ : E →L[ℝ] ℝ, ‖φ‖ ≤ 1 → ∑ i, |φ (x i)| ≤ M) : 0 ≤ M := by
  simpa only [zero_apply, abs_zero, Finset.sum_const_zero] using
    h 0 (by simp)

/-- Extension of a unit-dual-ball weak bound to every actual dual functional. -/
theorem weak_one_bound (n : ℕ) (x : Fin n → E) (M : ℝ)
    (h : ∀ φ : E →L[ℝ] ℝ, ‖φ‖ ≤ 1 → ∑ i, |φ (x i)| ≤ M)
    (φ : E →L[ℝ] ℝ) : ∑ i, |φ (x i)| ≤ ‖φ‖ * M := by
  by_cases hφ : φ = 0
  · simp only [hφ, zero_apply, abs_zero, Finset.sum_const_zero,
      norm_zero, zero_mul, le_refl]
  have hn : ‖φ‖ ≠ 0 := norm_ne_zero_iff.mpr hφ
  let ψ : E →L[ℝ] ℝ := ‖φ‖⁻¹ • φ
  have hψ : ‖ψ‖ ≤ 1 := by
    simp only [ψ, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg φ)), inv_mul_cancel₀ hn, le_refl]
  have he (i : Fin n) : ‖φ‖ * ψ (x i) = φ (x i) := by
    simp only [ψ, smul_apply, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hn, one_mul]
  calc
    _ = ∑ i, ‖φ‖ * |ψ (x i)| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← he i, abs_mul, abs_of_nonneg (norm_nonneg φ)]
    _ = ‖φ‖ * ∑ i, |ψ (x i)| := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (h ψ hψ) (norm_nonneg φ)

/-- Squared extension of a unit-dual-ball weak bound. -/
theorem weak_two_bound (n : ℕ) (x : Fin n → E) (M : ℝ)
    (h : ∀ φ : E →L[ℝ] ℝ, ‖φ‖ ≤ 1 → ∑ i, |φ (x i)| ^ 2 ≤ M ^ 2)
    (φ : E →L[ℝ] ℝ) : ∑ i, |φ (x i)| ^ 2 ≤ ‖φ‖ ^ 2 * M ^ 2 := by
  by_cases hφ : φ = 0
  · simp only [hφ, zero_apply, abs_zero, zero_pow (by norm_num : 2 ≠ 0),
      Finset.sum_const_zero, norm_zero, zero_mul, le_refl]
  have hn : ‖φ‖ ≠ 0 := norm_ne_zero_iff.mpr hφ
  let ψ : E →L[ℝ] ℝ := ‖φ‖⁻¹ • φ
  have hψ : ‖ψ‖ ≤ 1 := by
    simp only [ψ, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg φ)), inv_mul_cancel₀ hn, le_refl]
  have he (i : Fin n) : ‖φ‖ * ψ (x i) = φ (x i) := by
    simp only [ψ, smul_apply, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hn, one_mul]
  calc
    _ = ∑ i, ‖φ‖ ^ 2 * |ψ (x i)| ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← he i, abs_mul, abs_of_nonneg (norm_nonneg φ), mul_pow]
    _ = ‖φ‖ ^ 2 * ∑ i, |ψ (x i)| ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (h ψ hψ) (sq_nonneg _)

end WeakBounds

section OperatorIdeal
variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem OneSummingWith.mono {T : E →L[ℝ] F} {C D : ℝ}
    (hT : OneSummingWith T C) (hCD : C ≤ D) : OneSummingWith T D := by
  refine ⟨hT.1.trans hCD, ?_⟩
  intro n x M hM
  exact (hT.2 n x M hM).trans
    (mul_le_mul_of_nonneg_right hCD (weak_one_bound_nonneg n x M hM))

theorem TwoSummingWith.mono {T : E →L[ℝ] F} {C D : ℝ}
    (hT : TwoSummingWith T C) (hCD : C ≤ D) : TwoSummingWith T D := by
  refine ⟨hT.1.trans hCD, ?_⟩
  intro n x M hM hx
  exact (hT.2 n x M hM hx).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT.1 hCD 2) (sq_nonneg M))

/-- Precomposition has exactly its ordinary operator-norm cost. -/
theorem OneSummingWith.precomp {T : E →L[ℝ] F} {C : ℝ}
    (hT : OneSummingWith T C) (A : H →L[ℝ] E) :
    OneSummingWith (T.comp A) (C * ‖A‖) := by
  refine ⟨mul_nonneg hT.1 (norm_nonneg A), ?_⟩
  intro n x M hx
  have hM := weak_one_bound_nonneg n x M hx
  have hweak : ∀ φ : E →L[ℝ] ℝ, ‖φ‖ ≤ 1 → ∑ i, |φ (A (x i))| ≤ ‖A‖ * M := by
    intro φ hφ
    have hc : ‖φ.comp A‖ ≤ ‖A‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hφ (norm_nonneg A))
    exact (weak_one_bound n x M hx (φ.comp A)).trans
      (mul_le_mul_of_nonneg_right hc hM)
  simpa only [ContinuousLinearMap.comp_apply, mul_assoc] using
    hT.2 n (fun i => A (x i)) (‖A‖ * M) hweak

/-- Postcomposition has exactly its ordinary operator-norm cost. -/
theorem OneSummingWith.postcomp {T : E →L[ℝ] F} {C : ℝ}
    (hT : OneSummingWith T C) (B : F →L[ℝ] H) :
    OneSummingWith (B.comp T) (‖B‖ * C) := by
  refine ⟨mul_nonneg (norm_nonneg B) hT.1, ?_⟩
  intro n x M hx
  calc
    _ ≤ ∑ i, ‖B‖ * ‖T (x i)‖ := Finset.sum_le_sum (fun i _ => B.le_opNorm _)
    _ = ‖B‖ * ∑ i, ‖T (x i)‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖B‖ * (C * M) := mul_le_mul_of_nonneg_left (hT.2 n x M hx) (norm_nonneg B)
    _ = _ := (mul_assoc _ _ _).symm

/-- Precomposition for the squared two-summing inequality. -/
theorem TwoSummingWith.precomp {T : E →L[ℝ] F} {C : ℝ}
    (hT : TwoSummingWith T C) (A : H →L[ℝ] E) :
    TwoSummingWith (T.comp A) (C * ‖A‖) := by
  refine ⟨mul_nonneg hT.1 (norm_nonneg A), ?_⟩
  intro n x M hM hx
  have hweak : ∀ φ : E →L[ℝ] ℝ, ‖φ‖ ≤ 1 →
      ∑ i, |φ (A (x i))| ^ 2 ≤ (‖A‖ * M) ^ 2 := by
    intro φ hφ
    have hc : ‖φ.comp A‖ ≤ ‖A‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hφ (norm_nonneg A))
    have h := (weak_two_bound n x M hx (φ.comp A)).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hc 2) (sq_nonneg M))
    simpa only [ContinuousLinearMap.comp_apply, mul_pow] using h
  simpa only [ContinuousLinearMap.comp_apply, mul_pow, mul_assoc] using
    hT.2 n (fun i => A (x i)) (‖A‖ * M) (mul_nonneg (norm_nonneg A) hM) hweak

/-- Postcomposition for the squared two-summing inequality. -/
theorem TwoSummingWith.postcomp {T : E →L[ℝ] F} {C : ℝ}
    (hT : TwoSummingWith T C) (B : F →L[ℝ] H) :
    TwoSummingWith (B.comp T) (‖B‖ * C) := by
  refine ⟨mul_nonneg (norm_nonneg B) hT.1, ?_⟩
  intro n x M hM hx
  calc
    _ ≤ ∑ i, ‖B‖ ^ 2 * ‖T (x i)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_pow, ContinuousLinearMap.comp_apply] using pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm (T (x i))) 2
    _ = ‖B‖ ^ 2 * ∑ i, ‖T (x i)‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖B‖ ^ 2 * (C ^ 2 * M ^ 2) :=
      mul_le_mul_of_nonneg_left (hT.2 n x M hM hx) (sq_nonneg _)
    _ = _ := by ring

end OperatorIdeal

section Complemented
variable {E Y F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- One-summing estimates descend through the actual embedding and retraction. -/
theorem complemented_oneSumming (Q : EnfloStarbird.ComplementedCopy ℝ E Y)
    {G : ℝ} (hG : 0 ≤ G)
    (hY : ∀ S : Y →L[ℝ] F, OneSummingWith S (G * ‖S‖)) (S : E →L[ℝ] F) :
    OneSummingWith S ((G * ‖Q.embedding‖ * ‖Q.retraction‖) * ‖S‖) := by
  have ht := (hY (S.comp Q.retraction)).precomp Q.embedding
  have he : (S.comp Q.retraction).comp Q.embedding = S := by
    ext x
    change S (Q.retraction (Q.embedding x)) = S x
    rw [Q.left_inv x]
  rw [he] at ht
  apply ht.mono
  calc
    _ ≤ (G * (‖S‖ * ‖Q.retraction‖)) * ‖Q.embedding‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hG)
        (norm_nonneg _)
    _ = _ := by ring

/-- Two-summing estimates descend through the actual embedding and retraction. -/
theorem complemented_twoSumming (Q : EnfloStarbird.ComplementedCopy ℝ E Y)
    {G : ℝ} (hG : 0 ≤ G)
    (hY : ∀ T : H →L[ℝ] Y, TwoSummingWith T (G * ‖T‖)) (T : H →L[ℝ] E) :
    TwoSummingWith T ((G * ‖Q.embedding‖ * ‖Q.retraction‖) * ‖T‖) := by
  have ht := (hY (Q.embedding.comp T)).postcomp Q.retraction
  have he : Q.retraction.comp (Q.embedding.comp T) = T := by
    ext x
    exact Q.left_inv (T x)
  rw [he] at ht
  apply ht.mono
  calc
    _ ≤ ‖Q.retraction‖ * (G * (‖Q.embedding‖ * ‖T‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hG)
        (norm_nonneg _)
    _ = _ := by ring

/-- The two finite-dimensional hypotheses used by the lattice band estimate
transfer with the same dimension-independent constant. -/
theorem uniform_finite_summing_estimates (Q : EnfloStarbird.ComplementedCopy ℝ E Y)
    {G : ℝ} (hG : 0 ≤ G)
    (hOne : ∀ (n : ℕ) (S : Y →L[ℝ] EuclideanSpace ℝ (Fin n)), OneSummingWith S (G * ‖S‖))
    (hTwo : ∀ (n : ℕ) (T : (Fin n → ℝ) →L[ℝ] Y), TwoSummingWith T (G * ‖T‖)) :
    let C := G * ‖Q.embedding‖ * ‖Q.retraction‖
    0 ≤ C ∧
      (∀ (n : ℕ) (S : E →L[ℝ] EuclideanSpace ℝ (Fin n)), OneSummingWith S (C * ‖S‖)) ∧
      (∀ (n : ℕ) (T : (Fin n → ℝ) →L[ℝ] E), TwoSummingWith T (C * ‖T‖)) := by
  refine ⟨mul_nonneg (mul_nonneg hG (norm_nonneg _)) (norm_nonneg _), ?_, ?_⟩
  · intro n S
    exact complemented_oneSumming Q hG (hOne n) S
  · intro n T
    exact complemented_twoSumming Q hG (hTwo n) T

end Complemented

section LatticeConsequence
variable {E Y : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E] [HasPrincipalProjectionProperty E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The existing finite-band estimate, directly from an actual complemented
copy and the two ambient summing hypotheses. Principal projections remain
an explicit assumption and are not inferred from the Banach lattice axioms. -/
theorem disjoint_sum_norm_le_of_complemented_ambient_estimates
    (Q : EnfloStarbird.ComplementedCopy ℝ E Y) {G : ℝ} (hG : 0 ≤ G)
    (hOne : ∀ (n : ℕ) (S : Y →L[ℝ] EuclideanSpace ℝ (Fin n)), OneSummingWith S (G * ‖S‖))
    (hTwo : ∀ (n : ℕ) (T : (Fin n → ℝ) →L[ℝ] Y), TwoSummingWith T (G * ‖T‖))
    (n : ℕ) (x : Fin n → E) (hx : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    ∑ i, ‖x i‖ ≤ (G * ‖Q.embedding‖ * ‖Q.retraction‖) ^ 2 * ‖∑ i, x i‖ := by
  obtain ⟨hC, hOneE, hTwoE⟩ := uniform_finite_summing_estimates Q hG hOne hTwo
  exact disjoint_sum_norm_le_of_summing_estimates _ hC hOneE hTwoE n x hx

end LatticeConsequence

#print axioms OneSummingWith.precomp
#print axioms OneSummingWith.postcomp
#print axioms TwoSummingWith.precomp
#print axioms TwoSummingWith.postcomp
#print axioms uniform_finite_summing_estimates
#print axioms disjoint_sum_norm_le_of_complemented_ambient_estimates

end PL1.ComplementedLattice
