import Sigma.Estimates
import ThesisCommon.Analysis.NormingSequence

/-! Section 6's functional-analytic contradiction. The missing construction and
simple-function density are explicit hypotheses, not hidden fields or axioms. -/
namespace SigmaNonprimarity
open ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A concrete witness to the failure of coordinatewise modulus, supplied the
three levels, simple approximations and the two nonseparation properties.
This is a CONDITIONAL supporting theorem, not a proof of Theorem 1.1. -/
theorem no_modulus_of_three_levels
    (e : ℕ → E →L[ℝ] ℝ) (he : ∀ n, ‖e n‖ ≤ 1)
    (f : E) (H : Submodule ℝ E) (J₀ J₁ J₂ : Set ℕ) (a δ : ℝ)
    (hδ : 0 < δ) (ha : 11*δ < a)
    (hp : ∀ n ∈ J₂, |e n f - 2*a| < 3*δ)
    (hm : ∀ n ∈ J₁ \ J₂, |e n f - (-(2*a))| < 3*δ)
    (hz : ∀ n ∈ J₀ \ J₁, |e n f| < 3*δ)
    (hdense : ∀ g : E, ∃ (r : ℝ) (s : E), s ∈ H ∧ ‖g - (r • f + s)‖ < δ)
    (hsep₁ : ∀ s ∈ H, ¬ UniformGap (fun n => e n s) J₁ (J₀ \ J₁))
    (hsep₂ : ∀ s ∈ H, ¬ UniformGap (fun n => e n s) J₂ (J₁ \ J₂)) :
    ¬ ∃ g : E, ∀ n, e n g = |e n f| := by
  rintro ⟨g, hg⟩
  obtain ⟨r, s, hs, hgs⟩ := hdense g
  have happ (n : ℕ) : abs (|e n f| - (r * e n f + e n s)) < δ := by
    have hbound : ‖e n (g - (r • f + s))‖ ≤ ‖g - (r • f + s)‖ := by
      calc
        _ ≤ ‖e n‖ * ‖g - (r • f + s)‖ := (e n).le_opNorm _
        _ ≤ 1 * ‖g - (r • f + s)‖ :=
          mul_le_mul_of_nonneg_right (he n) (norm_nonneg _)
        _ = _ := one_mul _
    have hlt := hbound.trans_lt hgs
    simpa only [map_sub, map_add, map_smul, hg, Real.norm_eq_abs, smul_eq_mul] using hlt
  rcases three_level_separation (fun n => e n f) (fun n => e n s)
    J₀ J₁ J₂ a δ r hδ ha hp hm hz happ with h | h
  · exact hsep₁ s hs h
  · exact hsep₂ s hs h

end SigmaNonprimarity
