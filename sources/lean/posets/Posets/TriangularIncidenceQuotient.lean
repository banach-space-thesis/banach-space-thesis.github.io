import Posets.TriangularHomomorphism
import Posets.BipartiteOperatorAssembly

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P Q : Type*}

theorem scalarLinearMap_surjective_of_not_continuous
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
    (L : E →ₗ[𝕜] 𝕜) (hL : ¬ Continuous L) : Function.Surjective L := by
  have hn : ∃ x, L x ≠ 0 := by
    by_contra! h
    apply hL
    have heq : (L : E → 𝕜) = fun _ => 0 := funext h
    rw [heq]
    exact continuous_const
  obtain ⟨x, hx⟩ := hn
  intro c
  refine ⟨(c / L x) • x, ?_⟩
  simp [map_smul, div_mul_cancel₀ c hx]

theorem bipartiteTriangularMap_range (U : Ultrafilter P) (V : Ultrafilter Q)
    (L : (CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) →ₗ[𝕜] 𝕜)
    (hL : Function.Surjective L) :
    Set.range (bipartiteTriangularMap U V L) = triangularTwo 𝕜 := by
  apply Set.Subset.antisymm (bipartiteTriangularMap_range_subset U V L)
  intro M hM
  have hz : M 1 0 = 0 := hM
  obtain ⟨T, hT⟩ := hL (M 0 1)
  refine ⟨bipartiteAssemble (M 0 0 • (1 : Discrete P →ᵇ 𝕜)) T
    (M 1 1 • (1 : Discrete Q →ᵇ 𝕜)), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bipartiteTriangularMap, triangularLinearMap, bipartiteLeftDiagonalMap,
      bipartiteRightDiagonalMap, bipartiteUpperBlockMap, hT, hz] <;>
    exact tendsto_const_nhds.limUnder_eq

theorem bipartiteTriangularMap_not_continuous (U : Ultrafilter P) (V : Ultrafilter Q)
    (L : (CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) →ₗ[𝕜] 𝕜)
    (hL : ¬ Continuous L) : ¬ Continuous (bipartiteTriangularMap U V L) := by
  intro hcont
  have hc : Continuous (fun T : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P =>
      bipartiteTriangularMap U V L (bipartiteAssemble 0 T 0) 0 1) :=
    (continuous_apply 1).comp ((continuous_apply 0).comp
      (hcont.comp continuous_bipartite_insert))
  apply hL
  simpa only [bipartiteTriangularMap, triangularLinearMap_zero_one,
    LinearMap.comp_apply, bipartiteUpperBlockMap, LinearMap.coe_mk, AddHom.coe_mk,
    bipartiteUpperBlock_assemble] using hc

/-- The complete bipartite incidence algebra has a discontinuous homomorphism
onto the full algebra of upper triangular two-by-two matrices. -/
theorem exists_discontinuous_triangular_incidence_hom (𝕜 : Type) [RCLike 𝕜] :
    ∃ Φ : BipartiteAlgebra 𝕜 RowDomain ColumnDomain →ₗ[𝕜] Matrix (Fin 2) (Fin 2) 𝕜,
      IsMultiplicative 𝕜 Φ ∧ Set.range Φ = triangularTwo 𝕜 ∧ ¬ Continuous Φ := by
  obtain ⟨U, V, hUV⟩ := lemma_8_1_proof
  obtain ⟨L, hL, hleft, hright⟩ := lemma_8_2_proof 𝕜 U V hUV
  refine ⟨bipartiteTriangularMap U V L,
    bipartiteTriangularMap_multiplicative U V L hleft hright, ?_,
    bipartiteTriangularMap_not_continuous U V L hL⟩
  exact bipartiteTriangularMap_range U V L (scalarLinearMap_surjective_of_not_continuous L hL)

end Posets

