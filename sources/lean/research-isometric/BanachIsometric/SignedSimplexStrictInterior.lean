import BanachIsometric.SignedSimplexCoordinates

/-! In positive dimension the interior of the affine coordinate simplex is
precisely the set where all barycentric weights are strictly positive. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric

theorem signedSimplexBarycentric_pos_of_interior (n : ℕ) [NeZero n]
    {x : Fin n → ℝ} (hx : x ∈ interior (signedSimplexDomain n)) :
    ∀ i, 0 < signedSimplexBarycentric n x i := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hdom := interior_subset hx
  have hstep (j : Fin n) (a : ℝ) (ha : |a| < ε) : x + Pi.single j a ∈ signedSimplexDomain n := by
    apply hball
    rw [mem_ball]
    have hle : dist (x + Pi.single j a) x ≤ |a| := by
      rw [dist_pi_le_iff (abs_nonneg _)]
      intro k
      by_cases hk : k = j
      · subst k
        simp
      · simp [hk]
    exact hle.trans_lt ha
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [signedSimplexBarycentric_zero]
    have hsum : (∑ j, x j) ≤ 1 := hdom.2
    by_contra hbad
    have heq : (∑ j, x j) = 1 := by linarith
    have hsmall : |ε / 2| < ε := by rw [abs_of_pos (half_pos hε)]; exact half_lt_self hε
    have h := (hstep 0 (ε / 2) hsmall).2
    change (∑ j : Fin n, (x j + (Pi.single (0 : Fin n) (ε / 2) : Fin n → ℝ) j)) ≤ 1 at h
    simp only [Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true, heq] at h
    linarith
  · rw [signedSimplexBarycentric_succ]
    have hnon : 0 ≤ x j := hdom.1 j
    by_contra hbad
    have heq : x j = 0 := by linarith
    have hsmall : |-(ε / 2)| < ε := by
      rw [abs_neg, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have h := (hstep j (-(ε / 2)) hsmall).1 j
    change 0 ≤ x j + (Pi.single j (-(ε / 2)) : Fin n → ℝ) j at h
    simp [heq] at h
    linarith

end BanachIsometric.SingularPrism
