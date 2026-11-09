import NonCalkinAlgebra.SeparableEllOneQuotient

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open TopologicalSpace Filter Topology
open scoped ENNReal

/-- Separability of the actual ℓ¹ norm topology follows from the dense
linear span of its countably many coordinate vectors. -/
instance complexEllOne_separableSpace : SeparableSpace ComplexEllOne := by
  let e : ℕ → ComplexEllOne := fun n => lp.single 1 n 1
  let S : Submodule ℂ ComplexEllOne := Submodule.span ℂ (Set.range e)
  have hsep : IsSeparable (closure (S : Set ComplexEllOne)) :=
    (Set.countable_range e).isSeparable.span.closure
  have hfull : closure (S : Set ComplexEllOne) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    have hsum := lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) a
    apply isClosed_closure.mem_of_tendsto hsum.tendsto_sum_nat
    apply Eventually.of_forall
    intro N
    apply subset_closure
    apply S.sum_mem
    intro n hn
    have hunit : e n ∈ S := Submodule.subset_span ⟨n, rfl⟩
    have hscalar := S.smul_mem (a n) hunit
    simpa only [e, ← lp.single_smul, smul_eq_mul, mul_one] using hscalar
  rw [hfull] at hsep
  exact isSeparable_univ_iff.mp hsep

end NonCalkinAlgebra
