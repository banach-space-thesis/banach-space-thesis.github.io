import BanachIsometric.ExactFamilyRigidity

/-!
# The homogeneous powers and the paper's parity obstruction

Every polynomial power furnished by the exact-family theorem is homogeneous
of exactly its asserted degree. In odd ambient dimension an actual nonzero
normal degree would give an odd homogeneous polynomial positive away from
zero. Its value at a vector and its negative yield a contradiction.
This proves the parity remark without imposing symmetry of the gauge.
-/

namespace BanachIsometric

open scoped NNReal

theorem eval_smul_of_isHomogeneous {σ : Type*} (P : MvPolynomial σ ℝ)
    {d : ℕ} (hP : P.IsHomogeneous d) (t : ℝ) (x : σ → ℝ) :
    MvPolynomial.eval (fun i => t * x i) P = t ^ d * MvPolynomial.eval x P := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hdegree : a.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one] using hP (MvPolynomial.mem_support_iff.mp ha)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  change P.coeff a * (t ^ a.degree * a.prod (fun i n => x i ^ n)) = _
  rw [hdegree]
  dsimp only [Finsupp.prod]
  ring

namespace ExactTangentialFamily

variable {m N : ℕ} [NeZero N]
  {g : EuclideanSpace ℝ (Fin N) → ℝ} {p : EuclideanSpace ℝ (Fin m) → ℝ}
  (A : ExactTangentialFamily (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin N)) g p)

theorem exists_homogeneous_polynomial_power_of_nonzero_normalConeSignedIndex
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] PiolaSpace N)
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal)
    (hindex : A.normalConeSignedIndex e ≠ 0) (k : ℕ) :
    ∃ P : MvPolynomial (Fin m) ℝ, P.IsHomogeneous (N + 2 * k) ∧
      ∀ y : EuclideanSpace ℝ (Fin m),
        MvPolynomial.eval (fun j => y j) P = p y ^ (N + 2 * k) := by
  obtain ⟨P, hP⟩ := A.exists_polynomial_power_of_nonzero_normalConeSignedIndex
    μ e hp hg hcont hnormal hindex k
  let c := euclideanCoordinates m
  have hPc (x : Fin m → ℝ) : MvPolynomial.eval x P = p (c.symm x) ^ (N + 2 * k) := by
    have h := hP (c.symm x)
    change MvPolynomial.eval (c (c.symm x)) P = _ at h
    simpa only [c.apply_symm_apply] using h
  refine ⟨P, isHomogeneous_of_eval_two_mul P (N + 2 * k) ?_, hP⟩
  intro x
  rw [hPc, hPc]
  change p (c.symm ((2 : ℝ) • x)) ^ (N + 2 * k) = _
  rw [map_smul, hp.smul_nonneg 2 (by norm_num), mul_pow]

theorem normalConeSignedIndex_eq_zero_of_odd [NeZero m]
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] PiolaSpace N)
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (hOdd : Odd N)
    (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal) : A.normalConeSignedIndex e = 0 := by
  by_contra hindex
  obtain ⟨P, hPhom, hP⟩ := A.exists_homogeneous_polynomial_power_of_nonzero_normalConeSignedIndex
    μ e hp hg hcont hnormal hindex 0
  simp only [mul_zero, add_zero] at hPhom hP
  obtain ⟨y, hy⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin m))
  have hneg : -y ≠ 0 := neg_ne_zero.mpr hy
  have h := eval_smul_of_isHomogeneous P hPhom (-1) (fun i => y i)
  simp only [neg_one_mul] at h
  change MvPolynomial.eval (fun i => (-y) i) P = (-1 : ℝ) ^ N *
    MvPolynomial.eval (fun i => y i) P at h
  rw [hP, hP, hOdd.neg_one_pow, neg_one_mul] at h
  linarith [pow_pos (hp.pos hy) N, pow_pos (hp.pos hneg) N]

end ExactTangentialFamily
end BanachIsometric
