import JLMS.CZeroPositive

/-!
# Decomposing a real functional into positive bounded functionals

Apply Hahn–Banach on the diagonal of C₀(K,ℝ) × C₀(K,ℝ), dominated by
‖φ‖ (‖x⁺‖ + ‖y⁻‖). The two coordinate restrictions give positive functionals
P,Q with φ = P - Q. This supplies the signed input missing from the positive
Riesz–Markov–Kakutani theorem, without an additional representation axiom.
-/

noncomputable section

namespace JLMS

variable {K : Type*} [TopologicalSpace K]

/-- Domination by the norm of the positive part forces positivity and continuity. -/
theorem exists_positiveContinuous_of_positivePart_bound
    (P : CZero ℝ K →ₗ[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hP : ∀ f, P f ≤ M * ‖positivePartCZero f‖) :
    ∃ Ψ : CZero ℝ K →L[ℝ] ℝ, (∀ f, Ψ f = P f) ∧ ‖Ψ‖ ≤ M ∧
      ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ Ψ f := by
  have hbound (f : CZero ℝ K) : ‖P f‖ ≤ M * ‖f‖ := by
    rw [Real.norm_eq_abs]
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hneg := (hP (-f)).trans (mul_le_mul_of_nonneg_left (norm_positivePartCZero_le (-f)) hM)
      rw [P.map_neg, norm_neg] at hneg
      linarith
    · exact (hP f).trans (mul_le_mul_of_nonneg_left (norm_positivePartCZero_le f) hM)
  refine ⟨P.mkContinuous M hbound, fun _ => rfl, P.mkContinuous_norm_le hM hbound, ?_⟩
  intro f hf
  have hz : positivePartCZero (-f) = 0 := positivePartCZero_eq_zero (fun x => by
    change -f x ≤ 0
    exact neg_nonpos.mpr (hf x))
  have h := hP (-f)
  rw [P.map_neg, hz, norm_zero, mul_zero] at h
  change 0 ≤ P f
  linarith

/-- Every bounded real functional on C₀(K) is a difference of two positive
bounded functionals, each with norm at most the original norm. -/
theorem exists_positive_decomposition (φ : CZero ℝ K →L[ℝ] ℝ) :
    ∃ P Q : CZero ℝ K →L[ℝ] ℝ,
      φ = P - Q ∧ ‖P‖ ≤ ‖φ‖ ∧ ‖Q‖ ≤ ‖φ‖ ∧
      (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ P f) ∧
      (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ Q f) := by
  let E := CZero ℝ K
  let S : Submodule ℝ (E × E) :=
    LinearMap.ker ((LinearMap.fst ℝ E E) - (LinearMap.snd ℝ E E))
  let f : S →ₗ[ℝ] ℝ := φ.toLinearMap.comp ((LinearMap.fst ℝ E E).comp S.subtype)
  let N : E × E → ℝ := fun x => ‖φ‖ * (‖positivePartCZero x.1‖ + ‖positivePartCZero (-x.2)‖)
  have hhom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x := by
    intro c hc x
    dsimp [N]
    rw [← smul_neg, positivePartCZero_smul hc.le, positivePartCZero_smul hc.le,
      norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    ring
  have hadd : ∀ x y, N (x + y) ≤ N x + N y := by
    intro x y
    have hp := norm_positivePartCZero_add_le x.1 y.1
    have hn := norm_positivePartCZero_add_le (-x.2) (-y.2)
    rw [← neg_add] at hn
    dsimp [N]
    have h := mul_le_mul_of_nonneg_left (add_le_add hp hn) (norm_nonneg φ)
    nlinarith
  have hf : ∀ x : S, f x ≤ N x := by
    intro x
    have hx : x.val.1 = x.val.2 := by
      have h := x.property
      change x.val.1 - x.val.2 = 0 at h
      exact sub_eq_zero.mp h
    change φ x.val.1 ≤ ‖φ‖ * (‖positivePartCZero x.val.1‖ + ‖positivePartCZero (-x.val.2)‖)
    rw [← hx]
    exact (le_abs_self _).trans ((φ.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_le_positivePartCZero_add_negative x.val.1) (norm_nonneg φ)))
  obtain ⟨g, hdiag, hle⟩ := exists_extension_of_le_sublinear ⟨S, f⟩ N hhom hadd hf
  let p : E →ₗ[ℝ] ℝ := g.comp (LinearMap.inl ℝ E E)
  let q : E →ₗ[ℝ] ℝ := -g.comp (LinearMap.inr ℝ E E)
  have hp (x : E) : p x ≤ ‖φ‖ * ‖positivePartCZero x‖ := by
    have hz : positivePartCZero (0 : E) = 0 := positivePartCZero_eq_zero (fun _ => le_rfl)
    simpa [p, N, hz] using hle (x, 0)
  have hq (x : E) : q x ≤ ‖φ‖ * ‖positivePartCZero x‖ := by
    have hz : positivePartCZero (0 : E) = 0 := positivePartCZero_eq_zero (fun _ => le_rfl)
    have h := hle (-(0, x))
    rw [g.map_neg] at h
    change -g (0, x) ≤ ‖φ‖ * (‖positivePartCZero (-(0 : E))‖ + ‖positivePartCZero (-(-x))‖) at h
    rw [neg_zero, neg_neg, hz, norm_zero, zero_add] at h
    exact h
  obtain ⟨P, hP, hnP, hposP⟩ := exists_positiveContinuous_of_positivePart_bound p (norm_nonneg φ) hp
  obtain ⟨Q, hQ, hnQ, hposQ⟩ := exists_positiveContinuous_of_positivePart_bound q (norm_nonneg φ) hq
  refine ⟨P, Q, ?_, hnP, hnQ, hposP, hposQ⟩
  apply ContinuousLinearMap.ext
  intro x
  change φ x = P x - Q x
  rw [hP, hQ]
  have h := hdiag ⟨(x, x), by change x - x = 0; exact sub_self x⟩
  change g (x, x) = φ x at h
  have hg : g (x, x) = g (x, 0) + g (0, x) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using g.map_add (x, 0) (0, x)
  change φ x = g (x, 0) - -g (0, x)
  linarith

end JLMS
