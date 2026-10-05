import ThesisCommon.Analysis.TopologicalDensity
import Mathlib.Topology.Order.Lattice
import Mathlib.Order.Zorn
import Mathlib.Data.Set.Pairwise.Lattice

/-! Actual cardinal-density homogeneity for principal ideals.  Meet with a
smaller element is a continuous retraction, so principal-ideal density is
monotone.  Well-ordering of cardinals then gives homogeneous subelements.
This is the homogeneity reduction, not a classification of homogeneous
probability algebras. -/
noncomputable section
open Set
namespace ThesisCommon
universe u
variable {B : Type u} [SemilatticeInf B] [OrderBot B] [TopologicalSpace B]
  [ContinuousInf B]

/-- Cardinal density of the entire principal ideal with its subspace topology. -/
def principalDensity (a : B) : Cardinal.{u} := topologicalDensity (Iic a)

omit [OrderBot B] in
theorem principalDensity_mono {a b : B} (hba : b ≤ a) :
    principalDensity b ≤ principalDensity a := by
  let f : Iic a → Iic b := fun x => ⟨x.val ⊓ b, inf_le_right⟩
  apply topologicalDensity_le_of_continuous_surjective (f := f)
  · exact (continuous_subtype_val.inf continuous_const).subtype_mk _
  · intro y
    refine ⟨⟨y.val, y.property.trans hba⟩, ?_⟩
    apply Subtype.ext
    exact inf_eq_left.mpr y.property

/-- Every nonzero subelement has the same actual principal-ideal density. -/
def IsDensityHomogeneous (a : B) : Prop :=
  a ≠ ⊥ ∧ ∀ b : B, b ≠ ⊥ → b ≤ a → principalDensity b = principalDensity a

theorem exists_densityHomogeneous_le {a : B} (ha : a ≠ ⊥) :
    ∃ b : B, b ≤ a ∧ IsDensityHomogeneous b := by
  let s : Set Cardinal.{u} := principalDensity '' {b : B | b ≠ ⊥ ∧ b ≤ a}
  have hs : s.Nonempty := ⟨principalDensity a, a, ⟨ha, le_rfl⟩, rfl⟩
  obtain ⟨b, hb, hbcard⟩ := csInf_mem hs
  refine ⟨b, hb.2, hb.1, ?_⟩
  intro c hc hcb
  apply le_antisymm (principalDensity_mono hcb)
  rw [hbcard]
  exact csInf_le' ⟨c, ⟨hc, hcb.trans hb.2⟩, rfl⟩

/-- A Boolean algebra with continuous meet has an actual disjoint family of
density-homogeneous nonzero elements whose least upper bound is top.  No
completeness of the Boolean algebra is needed. -/
theorem exists_disjoint_densityHomogeneous_isLUB_top {C : Type u}
    [BooleanAlgebra C] [TopologicalSpace C] [ContinuousInf C] :
    ∃ s : Set C, (∀ a ∈ s, IsDensityHomogeneous a) ∧
      s.Pairwise Disjoint ∧ IsLUB s ⊤ := by
  classical
  let S : Set (Set C) := {s | (∀ a ∈ s, IsDensityHomogeneous a) ∧ s.Pairwise Disjoint}
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c →
      ∃ t ∈ S, ∀ s ∈ c, s ⊆ t := by
    intro c hc hcc
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
    · rintro a ⟨s, hs, ha⟩
      exact (hc hs).1 a ha
    · exact (pairwise_sUnion hcc.directedOn).mpr (fun s hs => (hc hs).2)
  obtain ⟨s, hs, hmax⟩ := zorn_subset S hchain
  refine ⟨s, hs.1, hs.2, ⟨fun a _ => le_top, ?_⟩⟩
  intro y hy
  by_contra hytop
  have hyne : y ≠ ⊤ := fun h => hytop h.ge
  have hcompl : yᶜ ≠ ⊥ := by simpa using hyne
  obtain ⟨b, hb, hbh⟩ := exists_densityHomogeneous_le hcompl
  have hbs : ∀ a ∈ s, Disjoint b a := fun a ha =>
    (disjoint_compl_left).mono hb (hy ha)
  have hins : insert b s ∈ S := by
    refine ⟨?_, (pairwise_insert_of_symmetric symmetric_disjoint).mpr ⟨hs.2, ?_⟩⟩
    · intro a ha
      rcases ha with rfl | ha
      · exact hbh
      · exact hs.1 a ha
    · intro a ha _
      exact hbs a ha
  have hmem : b ∈ s := hmax hins (subset_insert b s) (mem_insert b s)
  exact hbh.1 (disjoint_self.mp (hbs b hmem))

end ThesisCommon
