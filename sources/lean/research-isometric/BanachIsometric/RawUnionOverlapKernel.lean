import BanachIsometric.RawUnionOverlap

/-! A zero overlap class lets the two pieces of a subordinate cycle be
adjusted by the same actual overlap filling, with opposite signs. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X : Type*} [TopologicalSpace X]

def rawDegreeHomologyComponentSum (U V : Set X) (n : ℕ) :
    RawDegreeHomology U n × RawDegreeHomology V n →ₗ[ℚ] RawDegreeHomology X n :=
  (rawDegreeHomologyMap (rawSubspaceInclusion U) n).coprod
    (rawDegreeHomologyMap (rawSubspaceInclusion V) n)

theorem rawSubspaceChainInclusion_boundary_of_subset {U V : Set X} (h : U ⊆ V)
    (n : ℕ) (c : RawRationalChains U (n + 1)) :
    rawSubspaceChainInclusion V n (rawBoundary n (rawChainMap (rawSubspaceMapOfSubset h) (n + 1) c)) =
      rawSubspaceChainInclusion U n (rawBoundary n c) := by
  have hc : rawBoundary n (rawChainMap (rawSubspaceMapOfSubset h) (n + 1) c) =
      rawChainMap (rawSubspaceMapOfSubset h) n (rawBoundary n c) :=
    LinearMap.congr_fun (rawChainMap_boundary (rawSubspaceMapOfSubset h) n) c
  rw [hc, rawSubspaceChainInclusion_comp_apply h]

theorem rawUnionPairToHomology_mem_component_range_of_overlap_zero (U V : Set X) (n : ℕ)
    (z : rawUnionPairCycles U V n) (hz : rawUnionPairToOverlapHomology U V n z = 0) :
    rawUnionPairToHomology U V n z ∈
      LinearMap.range (rawDegreeHomologyComponentSum U V (n + 1)) := by
  obtain ⟨w, hw⟩ := rawUnionPairOverlap_fills_of_class_zero U V n z hz
  let hU : (U ∩ V : Set X) ⊆ U := Set.inter_subset_left
  let hV : (U ∩ V : Set X) ⊆ V := Set.inter_subset_right
  let a := z.val.1 - rawChainMap (rawSubspaceMapOfSubset hU) (n + 1) w
  let b := z.val.2 + rawChainMap (rawSubspaceMapOfSubset hV) (n + 1) w
  have ha : rawBoundary n a = 0 := by
    apply rawSubspaceChainInclusion_injective U n
    rw [map_zero]
    simp only [a, map_sub, rawSubspaceChainInclusion_boundary_of_subset hU, hw,
      rawUnionPairOverlap_inclusion, sub_self]
  have hb : rawBoundary n b = 0 := by
    apply rawSubspaceChainInclusion_injective V n
    rw [map_zero]
    simp only [b, map_add, rawSubspaceChainInclusion_boundary_of_subset hV, hw,
      rawUnionPairOverlap_inclusion]
    rw [add_comm]
    exact rawUnionPairBoundary_add_eq_zero U V n z
  have hab : rawSubspaceChainInclusion U (n + 1) a + rawSubspaceChainInclusion V (n + 1) b =
      (rawUnionPairToCycles U V n z).val := by
    change _ = rawSubspaceChainInclusion U (n + 1) z.val.1 +
      rawSubspaceChainInclusion V (n + 1) z.val.2
    simp only [a, b, map_sub, map_add, rawSubspaceChainInclusion_comp_apply hU,
      rawSubspaceChainInclusion_comp_apply hV]
    abel
  let a' : rawCycles U n := ⟨a, ha⟩
  let b' : rawCycles V n := ⟨b, hb⟩
  refine ⟨(Submodule.Quotient.mk a', Submodule.Quotient.mk b'), ?_⟩
  change rawHomologyMap (rawSubspaceInclusion U) n (Submodule.Quotient.mk a') +
      rawHomologyMap (rawSubspaceInclusion V) n (Submodule.Quotient.mk b') =
        Submodule.Quotient.mk (rawUnionPairToCycles U V n z)
  rw [rawHomologyMap_mk, rawHomologyMap_mk, ← Submodule.Quotient.mk_add]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hab)

end BanachIsometric.SingularPrism
