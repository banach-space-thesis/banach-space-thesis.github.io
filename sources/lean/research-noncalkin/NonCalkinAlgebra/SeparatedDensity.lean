import NonCalkinAlgebra.Statements
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u

/-- A uniformly separated family injects into every dense subset of a
metric space by choosing points in disjoint small balls. -/
theorem cardinal_le_dense_of_separated {I E : Type u} [MetricSpace E]
    (f : I → E) (hsep : ∀ i j, i ≠ j → 1 ≤ dist (f i) (f j))
    (S : Set E) (hS : Dense S) : Cardinal.mk I ≤ Cardinal.mk S := by
  classical
  have hex : ∀ i : I, ∃ s : S, dist (f i) (s : E) < (1 / 3 : ℝ) := by
    intro i
    have hcl : f i ∈ closure S := by rw [hS.closure_eq]; exact Set.mem_univ _
    obtain ⟨s, hs, hd⟩ := Metric.mem_closure_iff.mp hcl (1 / 3) (by norm_num)
    exact ⟨⟨s, hs⟩, hd⟩
  choose q hq using hex
  apply Cardinal.mk_le_of_injective (f := q)
  intro i j hij
  by_contra hne
  have hs := hsep i j hne
  have hi := hq i
  have hj := hq j
  have ht := dist_triangle (f i) (q i : E) (f j)
  have he : dist (q i : E) (f j) = dist (f j) (q j : E) := by rw [dist_comm, hij]
  rw [he] at ht
  linarith

end NonCalkinAlgebra
