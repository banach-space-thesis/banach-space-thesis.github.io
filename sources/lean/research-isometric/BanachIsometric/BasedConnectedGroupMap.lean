import BanachIsometric.ComponentCovering

/-! A continuous map from a connected equator into a topological group can
be normalized at one point to take values in its actual identity component. -/

noncomputable section

namespace BanachIsometric

open Set
open scoped Topology

variable {Q G : Type*} [TopologicalSpace Q] [PreconnectedSpace Q]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def normalizedGroupMap (f : C(Q, G)) (q₀ : Q) : C(Q, G) :=
  ⟨fun q => (f q₀)⁻¹ * f q, continuous_const.mul f.continuous⟩

omit [PreconnectedSpace Q] in
@[simp] theorem normalizedGroupMap_base (f : C(Q, G)) (q₀ : Q) :
    normalizedGroupMap f q₀ q₀ = 1 := inv_mul_cancel _

theorem normalizedGroupMap_mem_identityComponent (f : C(Q, G)) (q₀ q : Q) :
    normalizedGroupMap f q₀ q ∈ Subgroup.connectedComponentOfOne G := by
  have hq : q ∈ connectedComponent q₀ := by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact mem_univ q
  have h := (normalizedGroupMap f q₀).continuous.mapsTo_connectedComponent q₀ hq
  simpa only [normalizedGroupMap_base] using h

def basedIdentityComponentMap (f : C(Q, G)) (q₀ : Q) :
    C(Q, Subgroup.connectedComponentOfOne G) :=
  ⟨fun q => ⟨normalizedGroupMap f q₀ q, normalizedGroupMap_mem_identityComponent f q₀ q⟩,
    (normalizedGroupMap f q₀).continuous.subtype_mk _⟩

@[simp] theorem basedIdentityComponentMap_base (f : C(Q, G)) (q₀ : Q) :
    basedIdentityComponentMap f q₀ q₀ = 1 := Subtype.ext (inv_mul_cancel _)

end BanachIsometric
