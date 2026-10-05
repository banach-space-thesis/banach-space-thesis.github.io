import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-! A uniform finite bound on all finite-dimensional transverse subspaces
forces the actual algebraic quotient to be finite-dimensional. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [DivisionRing 𝕜] [AddCommGroup X] [Module 𝕜 X]

theorem finiteDimensional_quotient_of_transverse_finrank_bound
    (P : Submodule 𝕜 X) (d : ℕ)
    (h : ∀ Z : Submodule 𝕜 X, FiniteDimensional 𝕜 Z →
      Disjoint P Z → Module.finrank 𝕜 Z ≤ d) :
    FiniteDimensional 𝕜 (X ⧸ P) ∧ Module.finrank 𝕜 (X ⧸ P) ≤ d := by
  obtain ⟨N,hN⟩ := P.exists_isCompl
  have hfinite : FiniteDimensional 𝕜 N := by
    by_contra hinfinite
    have hrank : Cardinal.aleph0 ≤ Module.rank 𝕜 N :=
      le_of_not_gt (fun hh => hinfinite (Module.rank_lt_aleph0_iff.mp hh))
    have hnrank : ((d+1 : ℕ) : Cardinal) ≤ Module.rank 𝕜 N :=
      (Cardinal.nat_lt_aleph0 (d+1)).le.trans hrank
    obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_rank hnrank
    let w : Fin (d+1) → X := fun i => (v i).val
    have hw : LinearIndependent 𝕜 w := hv.map' N.subtype (Submodule.ker_subtype N)
    let Z : Submodule 𝕜 X := Submodule.span 𝕜 (Set.range w)
    have hZ : FiniteDimensional 𝕜 Z := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range w)
    have hZN : Z ≤ N := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact (v i).property
    have hdim : Module.finrank 𝕜 Z = d+1 := by
      have he := linearIndependent_iff_card_eq_finrank_span.mp hw
      simpa only [Fintype.card_fin, Set.finrank, Z] using he.symm
    have hb := h Z hZ (hN.disjoint.mono_right hZN)
    omega
  letI := hfinite
  have he := P.quotientEquivOfIsCompl N hN
  have hquot : FiniteDimensional 𝕜 (X ⧸ P) := he.symm.finiteDimensional
  refine ⟨hquot, ?_⟩
  rw [he.finrank_eq]
  exact h N hfinite hN.disjoint

end ThesisCommon
