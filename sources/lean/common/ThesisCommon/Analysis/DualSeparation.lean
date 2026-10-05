import ThesisCommon.Analysis.FiniteSeparation
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Integration of simple functions as finite linear combinations of test evaluations. -/
namespace ThesisCommon
open scoped BigOperators
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Analytic form of Sigma Lemma 4.2. For the paper, T consists of characteristic
functions from the two Boolean algebras, and e consists of measures acting on them. -/
theorem finitelySeparated_of_span_gap
    (e : D → E →L[ℝ] ℝ) (T : Set E) (M N : Set D)
    (s : E) (hs : s ∈ Submodule.span ℝ T) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ m ∈ M, ∀ n ∈ N, ε ≤ |e m s - e n s|) :
    FinitelySeparated (fun n t => e n t) T M N := by
  classical
  obtain ⟨c, F, hF, _, hrepr⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hs
  apply finitelySeparated_of_sum_gap (fun n t => e n t) T M N F hF c hε
  intro m hm n hn
  have h := hgap m hm n hn
  rw [← hrepr] at h
  simpa only [map_sum, map_smul, smul_eq_mul] using h

end ThesisCommon
