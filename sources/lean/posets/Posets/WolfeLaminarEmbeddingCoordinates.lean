import Posets.WolfeLaminarEmbeddingQuotient

/-! The clopen quotient coordinates form a self-adjoint laminar generating
family. Their multiplication laws are consequences of actual set containment. -/
noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K ι : Type*} [RCLike 𝕜] [TopologicalSpace K]
variable (A : ι → Set K) (hA : ∀ i, IsClopen (A i))

theorem wolfeClopenCoordinate_star (i : ι) :
    star (wolfeClopenCoordinate (𝕜 := 𝕜) A hA i) = wolfeClopenCoordinate A hA i := by
  ext q
  change star (if q.val i = true then (1 : 𝕜) else 0) = _
  split_ifs <;> simp [wolfeClopenCoordinate, *]

theorem wolfeClopenCoordinate_mul_of_subset {i j : ι} (hij : A i ⊆ A j) :
    wolfeClopenCoordinate (𝕜 := 𝕜) A hA i * wolfeClopenCoordinate A hA j =
      wolfeClopenCoordinate A hA i := by
  classical
  ext q
  obtain ⟨x, rfl⟩ := wolfeClopenProjection_surjective A hA q
  simp only [ContinuousMap.mul_apply, wolfeClopenCoordinate_projection]
  by_cases hi : x ∈ A i
  · simp [hi, hij hi]
  · simp [hi]

theorem wolfeClopenCoordinate_mul_of_disjoint {i j : ι} (hij : Disjoint (A i) (A j)) :
    wolfeClopenCoordinate (𝕜 := 𝕜) A hA i * wolfeClopenCoordinate A hA j = 0 := by
  classical
  ext q
  obtain ⟨x, rfl⟩ := wolfeClopenProjection_surjective A hA q
  simp only [ContinuousMap.mul_apply, wolfeClopenCoordinate_projection, ContinuousMap.zero_apply]
  by_cases hi : x ∈ A i
  · simp [hi, show x ∉ A j from fun hj => Set.disjoint_left.mp hij hi hj]
  · simp [hi]

theorem wolfeClopenCoordinate_one {i : ι} (hi : A i = univ) :
    wolfeClopenCoordinate (𝕜 := 𝕜) A hA i = 1 := by
  ext q
  obtain ⟨x, rfl⟩ := wolfeClopenProjection_surjective A hA q
  simp [wolfeClopenCoordinate_projection, hi]

theorem wolfeClopenCoordinate_separates (p q : WolfeClopenQuotient A hA) (hpq : p ≠ q) :
    ∃ i, wolfeClopenCoordinate (𝕜 := 𝕜) A hA i p ≠ wolfeClopenCoordinate A hA i q := by
  have hv : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  obtain ⟨i, hi⟩ : ∃ i, p.val i ≠ q.val i := by
    by_contra! he
    exact hv (funext he)
  refine ⟨i, ?_⟩
  cases hp : p.val i <;> cases hq : q.val i <;>
    simp [wolfeClopenCoordinate, hp, hq] at hi ⊢

theorem wolfeClopenCoordinate_mul_mem_span
    (hlam : ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j)) (i j : ι) :
    wolfeClopenCoordinate (𝕜 := 𝕜) A hA i * wolfeClopenCoordinate A hA j ∈
      Submodule.span 𝕜 (range (wolfeClopenCoordinate A hA)) := by
  rcases hlam i j with h | h | h
  · rw [wolfeClopenCoordinate_mul_of_subset A hA h]
    exact Submodule.subset_span (mem_range_self i)
  · rw [mul_comm, wolfeClopenCoordinate_mul_of_subset A hA h]
    exact Submodule.subset_span (mem_range_self j)
  · rw [wolfeClopenCoordinate_mul_of_disjoint A hA h]
    exact Submodule.zero_mem _

end Posets
