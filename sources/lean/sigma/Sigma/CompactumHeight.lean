import Sigma.ContinuousRepresentation
import Mathlib.Topology.DerivedSet

/-! The concrete Alexandrov--Urysohn compactum has empty third derivative.
For an infinite almost-disjoint family its second derivative is exactly infinity. -/
noncomputable section
open Set Topology
namespace SigmaNonprimarity

/-- The isolated countable base is dense for every infinite almost-disjoint family. -/
theorem compactum_separable {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) : TopologicalSpace.SeparableSpace (AUCompactum B) :=
  (compactumBaseDense hB hInf).separableSpace' _

private theorem not_mem_derivedSet_of_open {X : Type*} [TopologicalSpace X]
    {s U : Set X} {x : X} (hU : IsOpen U) (hx : x ∈ U)
    (h : U ∩ s ⊆ {x}) : x ∉ derivedSet s := by
  intro ha
  obtain ⟨y, hy, hne⟩ := accPt_iff_nhds.mp ha U (hU.mem_nhds hx)
  exact hne (h hy)

theorem compactum_base_not_mem_derivative (B : Set (Set Point)) (p : Point) :
    (↑(Sum.inl p : MrowkaBase B) : AUCompactum B) ∉
      derivedSet (Set.univ : Set (AUCompactum B)) := by
  apply not_mem_derivedSet_of_open
    (OnePoint.isOpen_image_coe.mpr (isOpen_base_singleton B p))
    (Set.mem_image_of_mem _ (Set.mem_singleton _))
  rintro x ⟨⟨y, rfl, rfl⟩, _⟩
  rfl

theorem compactum_family_mem_derivative {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (b : B) :
    (↑(Sum.inr b : MrowkaBase B) : AUCompactum B) ∈
      derivedSet (Set.univ : Set (AUCompactum B)) := by
  apply accPt_iff_nhds.mpr
  intro U hU
  obtain ⟨V, hVU, hV, hbV⟩ := mem_nhds_iff.mp hU
  have hpre : IsOpen (((↑) : MrowkaBase B → AUCompactum B) ⁻¹' V) :=
    hV.preimage OnePoint.continuous_coe
  obtain ⟨F, hF⟩ := tail_subset_of_isOpen hpre b hbV
  obtain ⟨p, hpb, hpF⟩ := (hB.1 b.val b.property).exists_notMem_finset F
  refine ⟨↑(Sum.inl p : MrowkaBase B), ⟨hVU (hF ?_), Set.mem_univ _⟩, ?_⟩
  · exact (inl_mem_tail B b F p).mpr ⟨hpb, hpF⟩
  · simp

theorem compactum_second_derivative_subset (B : Set (Set Point)) :
    derivedSet (derivedSet (Set.univ : Set (AUCompactum B))) ⊆ {OnePoint.infty} := by
  intro x hx
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x =>
      exfalso
      rcases x with p | b
      · exact compactum_base_not_mem_derivative B p
          (derivedSet_mono _ _ (Set.subset_univ _) hx)
      · apply not_mem_derivedSet_of_open
          (OnePoint.isOpen_image_coe.mpr (isOpen_tail B b ∅))
          (Set.mem_image_of_mem _ (by simp : Sum.inr b ∈ tailNeighborhood B b ∅))
          ?_ hx
        rintro y ⟨⟨z, hz, rfl⟩, hy⟩
        rcases z with p | c
        · exact False.elim (compactum_base_not_mem_derivative B p hy)
        · have hc := (inr_mem_tail B b c ∅).mp hz
          subst c
          rfl

/-- The empty third Cantor--Bendixson derivative claimed in Section 3.1. -/
theorem compactum_third_derivative_empty {B : Set (Set Point)}
    (hB : AlmostDisjoint B) :
    derivedSet (derivedSet (derivedSet (Set.univ : Set (AUCompactum B)))) = ∅ := by
  letI := mrowkaT2 hB
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hsingle := derivedSet_mono _ _ (compactum_second_derivative_subset B) hx
  by_cases hxi : x = OnePoint.infty
  · subst x
    exact not_mem_derivedSet_of_open isOpen_univ (Set.mem_univ _) (by simp) hsingle
  · exact not_mem_derivedSet_of_open isClosed_singleton.isOpen_compl hxi
      (by simp) hsingle

/-- Infinitely many family points force infinity to survive the second derivative. -/
theorem compactum_second_derivative_eq {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    derivedSet (derivedSet (Set.univ : Set (AUCompactum B))) = {OnePoint.infty} := by
  apply Set.Subset.antisymm (compactum_second_derivative_subset B)
  have hf : (Set.range (fun b : B =>
      (↑(Sum.inr b : MrowkaBase B) : AUCompactum B))).Infinite := by
    letI : Infinite B := hInf.to_subtype
    exact Set.infinite_range_of_injective
      (OnePoint.coe_injective.comp Sum.inr_injective)
  obtain ⟨x, hx⟩ := hf.exists_accPt_principal
  have hsub : Set.range (fun b : B =>
      (↑(Sum.inr b : MrowkaBase B) : AUCompactum B)) ⊆
      derivedSet (Set.univ : Set (AUCompactum B)) := by
    rintro x ⟨b, rfl⟩
    exact compactum_family_mem_derivative hB b
  have hx' := derivedSet_mono _ _ hsub hx
  have heq : x = OnePoint.infty := compactum_second_derivative_subset B hx'
  exact Set.singleton_subset_iff.mpr (heq ▸ hx')

theorem compactum_first_derivative_eq {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    derivedSet (Set.univ : Set (AUCompactum B)) =
      insert OnePoint.infty
        (Set.range (fun b : B => (↑(Sum.inr b : MrowkaBase B) : AUCompactum B))) := by
  apply Set.Subset.antisymm
  · intro x hx
    induction x using OnePoint.rec with
    | infty => exact Set.mem_insert _ _
    | coe x =>
        rcases x with p | b
        · exact False.elim (compactum_base_not_mem_derivative B p hx)
        · exact Set.mem_insert_of_mem _ ⟨b, rfl⟩
  · intro x hx
    rcases hx with rfl | ⟨b, rfl⟩
    · apply derivedSet_mono _ _ (Set.subset_univ _)
      rw [compactum_second_derivative_eq hB hInf]
      rfl
    · exact compactum_family_mem_derivative hB b

end SigmaNonprimarity
