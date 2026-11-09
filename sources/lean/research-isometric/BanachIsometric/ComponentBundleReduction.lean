import BanachIsometric.ExactSectionBundleConstruction
import BanachIsometric.SphereCovering
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The actual component covering of the exact-section atlas

The coordinate changes are the actual principal transition functions reduced
modulo the connected identity component. An open identity component makes the
fiber discrete, so the constructed core's actual projection is a covering
map. The covering lifting theorem then constructs a component section over
a simply connected base. No principal-bundle classifier is assumed.
-/

noncomputable section

namespace BanachIsometric

open Set Bundle
open scoped Topology

attribute [local instance] connectedComponentOfOne_normal

namespace ExactSectionAtlas

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : ExactSectionAtlas S K H)

abbrev ComponentGroup := (bodyAutomorphismGroup S) ⧸
  Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)

/-- The component core is built directly from the actual exact-section
principal transition cocycle. -/
def componentCore : FiberBundleCore P P (ComponentGroup (S := S)) where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := id
  mem_baseSet_at := Z.mem_baseSet
  coordChange i j a q := QuotientGroup.mk (Z.transition i j a) * q
  coordChange_self := by
    intro i a ha q
    rw [Z.transition_self i a ha, QuotientGroup.mk_one, one_mul]
  continuousOn_coordChange := by
    intro i j
    have hT : ContinuousOn
        (fun z : P × ComponentGroup (S := S) =>
          (QuotientGroup.mk (Z.transition i j z.1) : ComponentGroup (S := S)))
        ((Z.baseSet i ∩ Z.baseSet j) ×ˢ univ) :=
      (QuotientGroup.continuous_mk
        (N := Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S))).continuousOn.comp
        ((Z.continuousOn_transition i j).comp continuous_fst.continuousOn (fun _ h => h.1))
        (fun _ _ => mem_univ _)
    exact hT.mul continuous_snd.continuousOn
  coordChange_comp := by
    intro i j k a ha q
    rw [← mul_assoc, ← QuotientGroup.mk_mul,
      Z.transition_cocycle i j k a ha.1.1 ha.1.2 ha.2]

/-- The actual associated component bundle projection is a covering map.
The openness hypothesis is isolated here and discharged geometrically for
the actual body group in the subsequent application. -/
theorem isCoveringMap_componentCore
    (hopen : IsOpen (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) :
      Set (bodyAutomorphismGroup S))) : IsCoveringMap Z.componentCore.proj := by
  letI : DiscreteTopology (ComponentGroup (S := S)) := Subgroup.discreteTopology _ hopen
  intro a
  exact (IsEvenlyCovered.of_trivialization
    (Z.componentCore.mem_localTrivAt_baseSet a)).to_isEvenlyCovered_preimage

/-- A continuous section of the actual associated component covering,
constructed from actual transition maps and covering lifting. -/
theorem exists_componentCore_section [SimplyConnectedSpace P] [LocPathConnectedSpace P]
    (hopen : IsOpen (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) :
      Set (bodyAutomorphismGroup S))) (a₀ : P) :
    ∃ s : C(P, Z.componentCore.TotalSpace), ∀ a, Z.componentCore.proj (s a) = a := by
  let e₀ : Z.componentCore.TotalSpace := ⟨a₀, (1 : ComponentGroup (S := S))⟩
  obtain ⟨s, _, hs⟩ := exists_continuous_covering_section
    (Z.isCoveringMap_componentCore hopen) a₀ e₀ rfl
  exact ⟨s, hs⟩

end ExactSectionAtlas

end BanachIsometric
