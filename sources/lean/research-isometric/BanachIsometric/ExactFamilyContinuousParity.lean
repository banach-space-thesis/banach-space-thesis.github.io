import BanachIsometric.ExactFamilyTheorem

/-! The paper's odd-dimensional obstruction, including merely continuous
normal maps. Positivity contradicts the sign change of the actual odd
homogeneous polynomial furnished by the signed integral. -/

namespace BanachIsometric.ExactTangentialFamily

theorem continuousNormalDegree_eq_zero_of_odd
    {m N : ℕ} [NeZero m] [NeZero N]
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {p : EuclideanSpace ℝ (Fin m) → ℝ}
    (A : ExactTangentialFamily (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin N)) g p)
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] PiolaSpace N)
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (hOdd : Odd N) : A.continuousNormalDegree e = 0 := by
  by_contra hdegree
  obtain ⟨P, hPhom, hP⟩ := A.exists_polynomial_power_of_nonzero_continuousNormalDegree
    μ e hp hg hcont hdegree 0
  simp only [mul_zero, add_zero] at hPhom hP
  obtain ⟨y, hy⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin m))
  have hneg : -y ≠ 0 := neg_ne_zero.mpr hy
  have h := eval_smul_of_isHomogeneous P hPhom (-1) (fun i => y i)
  simp only [neg_one_mul] at h
  change MvPolynomial.eval (fun i => (-y) i) P = (-1 : ℝ) ^ N *
    MvPolynomial.eval (fun i => y i) P at h
  rw [hP, hP, hOdd.neg_one_pow, neg_one_mul] at h
  linarith [pow_pos (hp.pos hy) N, pow_pos (hp.pos hneg) N]

end BanachIsometric.ExactTangentialFamily
