import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! Stone–Weierstrass for the linear span of self-adjoint generators.

The laminar indicator construction supplies the hypotheses below.  This file
isolates the algebraic density argument from the quotient-space construction.
-/

noncomputable section

open Set Topology

namespace Posets

variable {𝕜 Q ι : Type*} [RCLike 𝕜] [TopologicalSpace Q]

/-- Pairwise closure on generators implies multiplicative closure of their span. -/
theorem wolfe_generatorSpan_mul_mem (v : ι → C(Q, 𝕜))
    (hmul : ∀ i j, v i * v j ∈ Submodule.span 𝕜 (Set.range v))
    {f g : C(Q, 𝕜)} (hf : f ∈ Submodule.span 𝕜 (Set.range v))
    (hg : g ∈ Submodule.span 𝕜 (Set.range v)) :
    f * g ∈ Submodule.span 𝕜 (Set.range v) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨j, rfl⟩ := hg
          exact hmul i j
      | zero => simp
      | add g h _ _ ihg ihh =>
          rw [mul_add]
          exact Submodule.add_mem _ ihg ihh
      | smul a g _ ih =>
          rw [mul_smul_comm]
          exact Submodule.smul_mem _ a ih
  | zero => simp
  | add f h _ _ ihf ihh =>
      rw [add_mul]
      exact Submodule.add_mem _ ihf ihh
  | smul a f _ ih =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ a ih

/-- The span of self-adjoint generators is closed under conjugation. -/
theorem wolfe_generatorSpan_star_mem (v : ι → C(Q, 𝕜))
    (hstar : ∀ i, star (v i) = v i)
    {f : C(Q, 𝕜)} (hf : f ∈ Submodule.span 𝕜 (Set.range v)) :
    star f ∈ Submodule.span 𝕜 (Set.range v) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      rw [hstar]
      exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add f g _ _ ihf ihg =>
      rw [star_add]
      exact Submodule.add_mem _ ihf ihg
  | smul a f _ ih =>
      rw [star_smul]
      exact Submodule.smul_mem _ (star a) ih

/-- A unital span satisfying the generator laws is a star subalgebra. -/
def wolfeGeneratorStarSubalgebra (v : ι → C(Q, 𝕜))
    (hone : (1 : C(Q, 𝕜)) ∈ Submodule.span 𝕜 (Set.range v))
    (hstar : ∀ i, star (v i) = v i)
    (hmul : ∀ i j, v i * v j ∈ Submodule.span 𝕜 (Set.range v)) :
    StarSubalgebra 𝕜 C(Q, 𝕜) where
  carrier := Submodule.span 𝕜 (Set.range v)
  zero_mem' := Submodule.zero_mem _
  one_mem' := hone
  add_mem' := Submodule.add_mem _
  mul_mem' := wolfe_generatorSpan_mul_mem v hmul
  algebraMap_mem' a := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ a hone
  star_mem' := wolfe_generatorSpan_star_mem v hstar

/-- The closed span of unital, self-adjoint, product-stable generators that
separate points is all of the continuous functions on a compact space. -/
theorem wolfe_generatorSpan_topologicalClosure_eq_top [CompactSpace Q]
    (v : ι → C(Q, 𝕜)) (hone : ∃ i, v i = 1)
    (hstar : ∀ i, star (v i) = v i)
    (hmul : ∀ i j, v i * v j ∈ Submodule.span 𝕜 (Set.range v))
    (hsep : ∀ x y : Q, x ≠ y → ∃ i, v i x ≠ v i y) :
    (Submodule.span 𝕜 (Set.range v)).topologicalClosure = ⊤ := by
  have h1 : (1 : C(Q, 𝕜)) ∈ Submodule.span 𝕜 (Set.range v) := by
    obtain ⟨i, hi⟩ := hone
    exact Submodule.subset_span ⟨i, hi⟩
  let A := wolfeGeneratorStarSubalgebra v h1 hstar hmul
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := hsep x y hxy
    exact ⟨v i, ⟨v i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩, hi⟩
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  have hc := congrArg (fun B : StarSubalgebra 𝕜 C(Q, 𝕜) => (B : Set C(Q, 𝕜))) h
  apply SetLike.coe_injective
  exact hc

/-- The density formulation of the preceding closed-span theorem. -/
theorem wolfe_generatorSpan_dense [CompactSpace Q]
    (v : ι → C(Q, 𝕜)) (hone : ∃ i, v i = 1)
    (hstar : ∀ i, star (v i) = v i)
    (hmul : ∀ i j, v i * v j ∈ Submodule.span 𝕜 (Set.range v))
    (hsep : ∀ x y : Q, x ≠ y → ∃ i, v i x ≠ v i y) :
    Dense (Submodule.span 𝕜 (Set.range v) : Set C(Q, 𝕜)) := by
  rw [dense_iff_closure_eq]
  exact congrArg (fun S : Submodule 𝕜 C(Q, 𝕜) => (S : Set C(Q, 𝕜)))
    (wolfe_generatorSpan_topologicalClosure_eq_top v hone hstar hmul hsep)

end Posets
