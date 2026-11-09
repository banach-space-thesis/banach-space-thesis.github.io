import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.ContinuousMap.Algebra

/-! An actual open normal subgroup is a continuous retract of the original
topological group. Normalized representatives of the actual discrete quotient
provide the retraction; no product decomposition or Lie classification is used.
-/

noncomputable section
namespace BanachIsometric

open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

open Classical in
def normalizedCosetRepresentative (H : Subgroup G) [H.Normal] (q : G ⧸ H) : G :=
  if q = 1 then 1 else Classical.choose (QuotientGroup.mk_surjective q)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem normalizedCosetRepresentative_class (H : Subgroup G) [H.Normal] (q : G ⧸ H) :
    (QuotientGroup.mk (normalizedCosetRepresentative H q) : G ⧸ H) = q := by
  classical
  by_cases hq : q = 1
  · simp [normalizedCosetRepresentative, hq]
  · simp only [normalizedCosetRepresentative, if_neg hq]
    exact Classical.choose_spec (QuotientGroup.mk_surjective q)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem normalizedCosetRepresentative_one (H : Subgroup G) [H.Normal] :
    normalizedCosetRepresentative H 1 = 1 := by
  simp [normalizedCosetRepresentative]

def openNormalSubgroupRetraction (H : Subgroup G) [H.Normal] (hH : IsOpen (H : Set G)) :
    C(G, H) := by
  letI : DiscreteTopology (G ⧸ H) := Subgroup.discreteTopology H hH
  let a : G → G := fun g => (normalizedCosetRepresentative H (QuotientGroup.mk g))⁻¹ * g
  have ha (g : G) : a g ∈ H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk ((normalizedCosetRepresentative H (QuotientGroup.mk g))⁻¹ * g) :
      G ⧸ H) = 1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, normalizedCosetRepresentative_class,
      inv_mul_cancel]
  have hrep : Continuous (normalizedCosetRepresentative H) := continuous_of_discreteTopology
  exact ⟨fun g => ⟨a g, ha g⟩,
    ((hrep.comp QuotientGroup.continuous_mk).inv.mul continuous_id).subtype_mk _⟩

theorem openNormalSubgroupRetraction_fixes (H : Subgroup G) [H.Normal]
    (hH : IsOpen (H : Set G)) (g : H) : openNormalSubgroupRetraction H hH g = g := by
  apply Subtype.ext
  have hq : (QuotientGroup.mk (g : G) : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff _).mpr g.property
  change (normalizedCosetRepresentative H (QuotientGroup.mk (g : G)))⁻¹ * g.val = g.val
  rw [hq, normalizedCosetRepresentative_one, inv_one, one_mul]

end BanachIsometric
