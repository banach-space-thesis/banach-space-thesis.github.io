import JLMS.Adjoint
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Lower comparison for an algebra norm on the operator algebra

Once a competing norm has an upper comparison, two rank-one operators
turn each value T x into a scalar multiple of one fixed nonzero rank-one
operator. Submultiplicativity gives a uniform lower comparison. This proves
the norm-equivalence step without requiring completeness of the competing norm.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem operatorNorm_lower_bound_of_upper (n : (E →L[𝕜] E) → ℝ)
    (hn : IsAlgebraNorm 𝕜 n) {C : ℝ} (hC : 0 < C)
    (hupper : ∀ T, n T ≤ C * ‖T‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ T, c * ‖T‖ ≤ n T := by
  classical
  by_cases hE : Subsingleton E
  · letI := hE
    refine ⟨1, by norm_num, fun T => ?_⟩
    have hT : T = 0 := Subsingleton.elim _ _
    simp only [hT, norm_zero, mul_zero]
    exact hn.1.1 0
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    obtain ⟨y₀, hy₀⟩ := exists_ne (0 : E)
    have hnormy₀ : 0 < ‖y₀‖ := norm_pos_iff.mpr hy₀
    let y := ((‖y₀‖⁻¹ : ℝ) : 𝕜) • y₀
    have hy : ‖y‖ = 1 := by
      simp only [y, norm_smul, RCLike.norm_ofReal, abs_inv,
        abs_of_nonneg (norm_nonneg y₀), inv_mul_cancel₀ hnormy₀.ne']
    obtain ⟨ψ, hψ, hψy⟩ := exists_dual_vector'' 𝕜 y
    rw [hy] at hψy
    have hψy' : ψ y = 1 := by simpa using hψy
    let P := ψ.smulRight y
    have hPne : P ≠ 0 := by
      intro hP
      have hh := congrArg (fun A : E →L[𝕜] E => A y) hP
      have hy0 : y = 0 := by simpa only [P, ContinuousLinearMap.smulRight_apply,
        hψy', one_smul, ContinuousLinearMap.zero_apply] using hh
      simp only [hy0, norm_zero] at hy
      norm_num at hy
    have hPpos : 0 < n P := lt_of_le_of_ne (hn.1.1 P) (by
      intro h
      exact hPne ((hn.1.2.1 P).mp h.symm))
    let K := C ^ 2 / n P
    have hKpos : 0 < K := div_pos (sq_pos_of_pos hC) hPpos
    have hKprod : K * n P = C ^ 2 := div_mul_cancel₀ _ hPpos.ne'
    have hnorm (T : E →L[𝕜] E) : ‖T‖ ≤ K * n T := by
      apply ContinuousLinearMap.opNorm_le_bound T (mul_nonneg hKpos.le (hn.1.1 T))
      intro x
      obtain ⟨φ, hφ, hφTx⟩ := exists_dual_vector'' 𝕜 (T x)
      let R := φ.smulRight y
      let Q := ψ.smulRight x
      have hR : ‖R‖ ≤ 1 := by
        rw [ContinuousLinearMap.norm_smulRight_apply, hy, mul_one]
        exact hφ
      have hQ : ‖Q‖ ≤ ‖x‖ := by
        rw [ContinuousLinearMap.norm_smulRight_apply]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hψ (norm_nonneg x)
      have heq : (R * T) * Q = (‖T x‖ : 𝕜) • P := by
        apply ContinuousLinearMap.ext
        intro z
        simp only [R, Q, P, ContinuousLinearMap.mul_apply,
          ContinuousLinearMap.smulRight_apply, map_smul, ContinuousLinearMap.smul_apply, hφTx,
          smul_smul, mul_comm]
      have hineq := (hn.2 (R * T) Q).trans
        (mul_le_mul_of_nonneg_right (hn.2 R T) (hn.1.1 Q))
      rw [heq, hn.1.2.2.2, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg (T x))] at hineq
      have hnR : n R ≤ C := (hupper R).trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hR hC.le)
      have hnQ : n Q ≤ C * ‖x‖ := (hupper Q).trans (mul_le_mul_of_nonneg_left hQ hC.le)
      have hprod : n R * n T * n Q ≤ C * n T * (C * ‖x‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hnR (hn.1.1 T)) hnQ
          (hn.1.1 Q) (mul_nonneg hC.le (hn.1.1 T))
      apply le_of_mul_le_mul_right _ hPpos
      calc
        ‖T x‖ * n P ≤ C * n T * (C * ‖x‖) := hineq.trans hprod
        _ = C ^ 2 * (n T * ‖x‖) := by ring
        _ = (K * n P) * (n T * ‖x‖) := by rw [hKprod]
        _ = (K * n T * ‖x‖) * n P := by ring
    refine ⟨1 / K, one_div_pos.mpr hKpos, fun T => ?_⟩
    calc
      (1 / K) * ‖T‖ ≤ (1 / K) * (K * n T) :=
        mul_le_mul_of_nonneg_left (hnorm T) (one_div_pos.mpr hKpos).le
      _ = n T := by rw [← mul_assoc, one_div, inv_mul_cancel₀ hKpos.ne', one_mul]

end JLMS
