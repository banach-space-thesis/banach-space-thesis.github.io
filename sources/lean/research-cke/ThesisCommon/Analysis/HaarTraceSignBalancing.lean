import ThesisCommon.Analysis.HaarSignSecondMoment

/-! Simultaneous balancing of finitely many real or complex traces by
choosing one child from each pair. The centre is exactly half the total
trace, and the bound is proved by finite sign second moments. -/

noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem haar_trace_signed_deviation {n : ℕ} (a b : Fin n → 𝕜)
    (θ : Fin n → Bool) :
    (∑ i, if θ i then a i else b i) - (2 : 𝕜)⁻¹ * (∑ i : Fin n, (a i + b i)) =
      (2 : 𝕜)⁻¹ * ∑ i, signedValue (θ i) (a i - b i) := by
  have hterm (i : Fin n) :
      (if θ i then a i else b i) - (2 : 𝕜)⁻¹ * (a i + b i) =
        (2 : 𝕜)⁻¹ * signedValue (θ i) (a i - b i) := by
    cases θ i <;> simp only [Bool.false_eq_true, if_false, if_true, signedValue] <;> ring
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [hterm]
  rw [Finset.mul_sum]

theorem haar_trace_sign_balance {m n : ℕ} (a b : Fin m → Fin n → 𝕜)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : (∑ r, ∑ i, ‖a r i - b r i‖ ^ 2) < (2 * ε) ^ 2) :
    ∃ θ : Fin n → Bool, ∀ r,
      ‖(∑ i, if θ i then a r i else b r i) -
          (2 : 𝕜)⁻¹ * (∑ i : Fin n, (a r i + b r i))‖ < ε ∧
      ‖(∑ i, if θ i then b r i else a r i) -
          (2 : 𝕜)⁻¹ * (∑ i : Fin n, (a r i + b r i))‖ < ε := by
  obtain ⟨θ, hθ⟩ := haar_sign_simultaneous_small (fun r i => a r i - b r i)
    (by linarith : 0 < 2 * ε) hsmall
  refine ⟨θ, fun r => ?_⟩
  have hfirst : ‖(∑ i, if θ i then a r i else b r i) -
      (2 : 𝕜)⁻¹ * (∑ i : Fin n, (a r i + b r i))‖ < ε := by
    rw [haar_trace_signed_deviation, norm_mul, norm_inv]
    have htwo : ‖(2 : 𝕜)‖ = (2 : ℝ) := by norm_num
    rw [htwo]
    nlinarith [hθ r]
  refine ⟨hfirst, ?_⟩
  have hsum : (∑ i, if θ i then a r i else b r i) +
      (∑ i, if θ i then b r i else a r i) = ∑ i : Fin n, (a r i + b r i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases θ i <;> simp [add_comm]
  have heq : (∑ i, if θ i then b r i else a r i) -
      (2 : 𝕜)⁻¹ * (∑ i : Fin n, (a r i + b r i)) =
      -((∑ i, if θ i then a r i else b r i) -
        (2 : 𝕜)⁻¹ * (∑ i : Fin n, (a r i + b r i))) := by
    rw [← hsum]
    ring
  simpa only [heq, norm_neg] using hfirst

end ThesisCommon
