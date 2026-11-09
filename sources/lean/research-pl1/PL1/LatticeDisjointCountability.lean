import PL1.SchurLattice
import Mathlib.Topology.DiscreteSubset

/-!
# Countability of disjoint families in separable normed lattices

This is a structural preparation lemma. Atomicity of a Schur Banach lattice
is not assumed or concluded in this file.
-/

noncomputable section
open scoped Topology

namespace PL1.SchurLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

/-- Disjoint vectors are separated by at least the norm of either vector. -/
theorem norm_le_dist_of_isVLDisjoint {x y : E} (h : IsVLDisjoint x y) :
    ‖x‖ ≤ dist x y := by
  rw [dist_eq_norm]
  apply norm_le_norm_of_abs_le_abs
  have hneg : IsVLDisjoint x (-y) := by simpa only [IsVLDisjoint, abs_neg] using h
  rw [sub_eq_add_neg, abs_add_of_isVLDisjoint hneg, abs_neg]
  exact le_add_of_nonneg_right (abs_nonneg y)

/-- A family of pairwise disjoint nonzero vectors is discrete in its inherited
norm topology, without a normalization hypothesis. -/
theorem isDiscrete_of_pairwise_isVLDisjoint (s : Set E)
    (hdisj : s.Pairwise IsVLDisjoint) (hzero : 0 ∉ s) : IsDiscrete s := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  have hx0 : x ≠ 0 := fun h => hzero (h ▸ hx)
  refine ⟨Metric.ball x ‖x‖, Metric.isOpen_ball, ?_⟩
  ext y
  constructor
  · intro hy
    have hyx : y = x := by
      by_contra hne
      have hd := norm_le_dist_of_isVLDisjoint (hdisj hx hy.2 (fun h => hne h.symm))
      have hball := hy.1
      rw [Metric.mem_ball, dist_comm] at hball
      exact (not_lt_of_ge hd) hball
    exact Set.mem_singleton_iff.mpr hyx
  · rintro rfl
    exact ⟨by simpa only [Metric.mem_ball, dist_self] using norm_pos_iff.mpr hx0, hx⟩

/-- In a separable normed lattice every pairwise disjoint family of nonzero
vectors is countable. Positivity and normalization are unnecessary. -/
theorem countable_of_pairwise_isVLDisjoint [TopologicalSpace.SeparableSpace E]
    (s : Set E) (hdisj : s.Pairwise IsVLDisjoint) (hzero : 0 ∉ s) : s.Countable := by
  let : DiscreteTopology s :=
    isDiscrete_iff_discreteTopology.mp (isDiscrete_of_pairwise_isVLDisjoint s hdisj hzero)
  let : Countable s := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact Set.to_countable s

/-- The requested normalized-family specialization. -/
theorem countable_of_pairwise_isVLDisjoint_norm_one [TopologicalSpace.SeparableSpace E]
    (s : Set E) (hdisj : s.Pairwise IsVLDisjoint) (hnorm : ∀ x ∈ s, ‖x‖ = 1) :
    s.Countable := by
  apply countable_of_pairwise_isVLDisjoint s hdisj
  intro hzero
  simpa using hnorm 0 hzero

/-- The index type of a nonvanishing disjoint family is countable as well. -/
theorem countable_index_of_pairwise_isVLDisjoint [TopologicalSpace.SeparableSpace E]
    {ι : Type*} (x : ι → E) (hdisj : Pairwise (fun i j => IsVLDisjoint (x i) (x j)))
    (hne : ∀ i, x i ≠ 0) : Countable ι := by
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hneij
    have hd : IsVLDisjoint (x i) (x j) := hdisj hneij
    rw [hij, IsVLDisjoint, inf_idem] at hd
    exact hne j ((abs_eq_zero_iff_zero _).mp hd)
  have hs : (Set.range x).Countable := countable_of_pairwise_isVLDisjoint _ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hdisj (fun h => hij (congrArg x h))) (by
    rintro ⟨i, hi⟩
    exact hne i hi)
  let : Countable (Set.range x) := hs.to_subtype
  exact (show Function.Injective (fun i => (⟨x i, Set.mem_range_self i⟩ : Set.range x)) from
    fun _ _ h => hinj (congrArg Subtype.val h)).countable

/-- The zero vector contributes at most one point to a set, so it can be
allowed in the set version of the countability theorem. -/
theorem countable_disjointSet [TopologicalSpace.SeparableSpace E]
    (s : Set E) (hdisj : s.Pairwise IsVLDisjoint) : s.Countable := by
  have hs : (s \ {0}).Countable := countable_of_pairwise_isVLDisjoint _
    (fun _ hx _ hy hne => hdisj hx.1 hy.1 hne) (by simp)
  apply (hs.union (Set.countable_singleton 0)).mono
  intro x hx
  by_cases h : x = 0
  · exact Or.inr (Set.mem_singleton_iff.mpr h)
  · exact Or.inl ⟨hx, by simpa using h⟩

/-- Separability makes the existing BanLat maximal positive disjoint family
countable. This theorem does not assert that its vectors are atoms. -/
theorem exists_countable_maximal_disjoint_positive_family
    [TopologicalSpace.SeparableSpace E] :
    ∃ s : Set E, s.Countable ∧ IsMaximalDisjoint s ∧ ∀ x ∈ s, 0 < x := by
  obtain ⟨s, hs, hpos⟩ := exists_isMaximalDisjoint_pos E
  exact ⟨s, countable_of_pairwise_isVLDisjoint s hs.prop.2 hs.prop.1, hs, hpos⟩

end PL1.SchurLattice
