import BanachIsometric.QuaternionicStatements

/-! Semantic certification of the paper's square-root-of-Hermitian-diagonal
wording. For the nonnegative gauges in A--E, the existing squared-diagonal
predicate means exactly that original function, with the same right action. -/

namespace BanachIsometric.Quaternionic

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X]

theorem hasHermitianSquare_iff_sqrt_diagonal {p : X → ℝ} (hnonneg : ∀ x, 0 ≤ p x) :
    HasHermitianSquare p ↔ ∃ h : HermitianForm X, h.IsPositiveDefinite ∧
      ∀ x, p x = Real.sqrt (h.form x x).re := by
  constructor
  · rintro ⟨h, hdiag, hpos⟩
    refine ⟨h, hpos, ?_⟩
    intro x
    rw [hdiag]
    change p x = Real.sqrt (p x ^ 2)
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hnonneg x)]
  · rintro ⟨h, hpos, hroot⟩
    refine ⟨h, ?_, hpos⟩
    intro x
    change h.form x x = (p x ^ 2 : ℝ)
    have hnonnegH : 0 ≤ (h.form x x).re := by
      by_cases hx : x = 0
      · subst x
        rw [h.zero_right, Quaternion.re_zero]
      · exact (hpos x hx).le
    calc
      h.form x x = ((h.form x x).re : H) := h.self_eq_re x
      _ = (p x ^ 2 : ℝ) := by rw [hroot, Real.sq_sqrt hnonnegH]

end
end BanachIsometric.Quaternionic
