import Sigma.ComplexSeparation
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! The complex finite-span separation step for the final contradiction. -/
namespace SigmaNonprimarity
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem complexFinitelySeparated_of_span_gap (e : D → E →L[ℂ] ℂ)
    (T : Set E) (M N : Set D) (s : E) (hs : s ∈ Submodule.span ℂ T)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ m ∈ M, ∀ n ∈ N, ε ≤ ‖e m s - e n s‖) :
    ComplexFinitelySeparated (fun n t => e n t) T M N := by
  classical
  obtain ⟨c,F,hF,_,hrepr⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hs
  apply complexFinitelySeparated_of_sum_gap (fun n t => e n t) T M N F hF c hε
  intro m hm n hn
  have h := hgap m hm n hn
  rw [← hrepr] at h
  simpa only [map_sum,map_smul,smul_eq_mul] using h

theorem complex_no_gap_on_span (e : ℕ → E →L[ℂ] ℂ) (T : Set E) (M N : Set ℕ)
    (h : ¬ ComplexFinitelySeparated (fun n t => e n t) T M N) :
    ∀ s ∈ Submodule.span ℂ T, ¬ ComplexUniformGap (fun n => e n s) M N := by
  intro s hs hgap
  rcases hgap with ⟨ε,hε,hgap⟩
  exact h (complexFinitelySeparated_of_span_gap e T M N s hs hε hgap)

end SigmaNonprimarity
