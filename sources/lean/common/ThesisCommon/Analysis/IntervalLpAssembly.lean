import ThesisCommon.Analysis.IntervalUpperDichotomy
import ThesisCommon.Analysis.IntervalInfinityDichotomy
import ThesisCommon.Analysis.CZeroLpUpperTriangular
import ThesisCommon.Analysis.HeterogeneousAssembly
import ThesisCommon.Analysis.EllOneSelfSimilarPreservation
import ThesisCommon.Analysis.SequencePrimariness

/-! LPCK Theorem 1.2's sequence-space assembly. Its two cited base-space
inputs, UPFP of C[0,1] and C[0,1] ≃ c0(C[0,1]), remain explicit hypotheses.
Every exponent, including 1 and infinity, and the primariness conclusion
are covered once those independent inputs have been established. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem interval_lp_cZero_factorization (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    {C : ℝ} (hC : 1 ≤ C) (hX : HasCPFP 𝕜 (IntervalContinuous 𝕜) C)
    (T : lp (fun _ : ℕ => CZeroSum (IntervalContinuous 𝕜)) p →L[𝕜]
      lp (fun _ : ℕ => CZeroSum (IntervalContinuous 𝕜)) p) :
    FactorsIdentityWith T (lp (fun _ : ℕ => IntervalContinuous 𝕜) p) (4*C) ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _-T)
        (lp (fun _ : ℕ => IntervalContinuous 𝕜) p) (4*C) := by
  have h := factorization_dichotomy_of_approximate_retracts (by linarith : 1 ≤ 2*C) T
    (fun U : lp (fun _ : ℕ => IntervalContinuous 𝕜) p →L[𝕜] lp (fun _ : ℕ => IntervalContinuous 𝕜) p =>
      IsLpUpperPart U U)
    (fun U hU => interval_lp_upper_dichotomy (Or.inr hp1) hC hX U hU)
  have hconstant : 2*(2*C) = 4*C := by ring
  rw [hconstant] at h
  apply h
  intro ε hε
  obtain ⟨e, m, U, _, _, hsmall, hU⟩ := lp_cZero_upper_triangular hp T hε
  exact ⟨lpCZeroPointRead p e m, lpCZeroPointInsert p e m, U,
    lpCZeroPointRead_comp_insert p e m, norm_lpCZeroPointRead_le p e m,
    norm_lpCZeroPointInsert_le p e m, hU.self_upperPart, hsmall⟩

theorem HasUPFP.interval_lp_finite (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (hX : HasUPFP 𝕜 (IntervalContinuous 𝕜))
    (e : IntervalContinuous 𝕜 ≃L[𝕜] CZeroSum (IntervalContinuous 𝕜)) :
    HasUPFP 𝕜 (lp (fun _ : ℕ => IntervalContinuous 𝕜) p) := by
  obtain ⟨C, hC, hX⟩ := hX
  let H : lp (fun _ : ℕ => IntervalContinuous 𝕜) p ≃L[𝕜]
      lp (fun _ : ℕ => CZeroSum (IntervalContinuous 𝕜)) p := lpMapEquiv p e
  have hbig : HasUPFP 𝕜 (lp (fun _ : ℕ => CZeroSum (IntervalContinuous 𝕜)) p) := by
    apply hasUPFP_of_approximate_retractions (by linarith : 1 ≤ 2*C) H
      (fun U => IsLpUpperPart U U)
      (fun U hU => interval_lp_upper_dichotomy (Or.inr hp1) hC hX U hU)
    intro T ε hε
    obtain ⟨n, m, U, _, _, hsmall, hU⟩ := lp_cZero_upper_triangular hp T hε
    exact ⟨lpCZeroPointRead p n m, lpCZeroPointInsert p n m, U,
      lpCZeroPointRead_comp_insert p n m, norm_lpCZeroPointRead_le p n m,
      norm_lpCZeroPointInsert_le p n m, hU.self_upperPart, hsmall⟩
  exact hbig.of_equiv H.symm

theorem HasUPFP.interval_lp (hX : HasUPFP 𝕜 (IntervalContinuous 𝕜))
    (e : IntervalContinuous 𝕜 ≃L[𝕜] CZeroSum (IntervalContinuous 𝕜))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    HasUPFP 𝕜 (lp (fun _ : ℕ => IntervalContinuous 𝕜) p) := by
  by_cases hp : p = ∞
  · subst p
    exact hX.interval_infinity
  by_cases hp1 : p = 1
  · subst p
    exact hX.ellOne_of_cZero_equiv e
  have hlt : (1 : ℝ≥0∞) < p := lt_of_le_of_ne (Fact.out : 1 ≤ p) (Ne.symm hp1)
  have hreal : 1 < p.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal (by simp) hp).mpr hlt
  exact hX.interval_lp_finite hp hreal e

theorem interval_lp_upfp_primary (hX : HasUPFP 𝕜 (IntervalContinuous 𝕜))
    (e : IntervalContinuous 𝕜 ≃L[𝕜] CZeroSum (IntervalContinuous 𝕜))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    HasUPFP 𝕜 (lp (fun _ : ℕ => IntervalContinuous 𝕜) p) ∧
      IsPrimary 𝕜 (lp (fun _ : ℕ => IntervalContinuous 𝕜) p) := by
  have h := hX.interval_lp e p
  exact ⟨h, h.lp_isPrimary⟩

end ThesisCommon
