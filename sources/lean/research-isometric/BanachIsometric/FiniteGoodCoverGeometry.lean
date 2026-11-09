import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

/-! Set and subspace identities for induction over an actual finite open cover. -/

namespace BanachIsometric.SingularPrism

variable {X ι : Type*}

def finiteCoverUnion (U : ι → Set X) (s : Finset ι) : Set X := ⋃ i ∈ s, U i

def finiteCoverIntersection (U : ι → Set X) (s : Finset ι) : Set X := ⋂ i ∈ s, U i

theorem finiteCoverUnion_empty (U : ι → Set X) : finiteCoverUnion U ∅ = ∅ := by
  ext x
  simp [finiteCoverUnion]

theorem finiteCoverUnion_insert [DecidableEq ι] (U : ι → Set X) (a : ι) (s : Finset ι) :
    finiteCoverUnion U (insert a s) = U a ∪ finiteCoverUnion U s := by
  ext x
  simp only [finiteCoverUnion, Set.mem_iUnion, Set.mem_union, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases hi with rfl | hi
    · exact Or.inl hx
    · exact Or.inr ⟨i, hi, hx⟩
  · rintro (hx | ⟨i, hi, hx⟩)
    · exact ⟨a, Or.inl rfl, hx⟩
    · exact ⟨i, Or.inr hi, hx⟩

theorem finiteCoverUnion_inter (A : Set X) (U : ι → Set X) (s : Finset ι) :
    finiteCoverUnion (fun i => A ∩ U i) s = A ∩ finiteCoverUnion U s := by
  ext x
  simp only [finiteCoverUnion, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨i, hi, hx, hy⟩
    exact ⟨hx, i, hi, hy⟩
  · rintro ⟨hx, i, hi, hy⟩
    exact ⟨i, hi, hx, hy⟩

theorem finiteCoverIntersection_singleton (U : ι → Set X) (a : ι) :
    finiteCoverIntersection U {a} = U a := by
  ext x
  simp [finiteCoverIntersection]

theorem finiteCoverIntersection_inter [DecidableEq ι] (U : ι → Set X) (a : ι)
    {t : Finset ι} (ht : t.Nonempty) :
    finiteCoverIntersection (fun i => U a ∩ U i) t = finiteCoverIntersection U (insert a t) := by
  ext x
  simp only [finiteCoverIntersection, Set.mem_iInter, Set.mem_inter_iff, Finset.mem_insert]
  constructor
  · intro h i hi
    rcases hi with rfl | hi
    · obtain ⟨j, hj⟩ := ht
      exact (h j hj).1
    · exact (h i hi).2
  · intro h i hi
    exact ⟨h a (Or.inl rfl), h i (Or.inr hi)⟩

theorem isOpen_finiteCoverUnion [TopologicalSpace X] (U : ι → Set X) (s : Finset ι)
    (hU : ∀ i ∈ s, IsOpen (U i)) : IsOpen (finiteCoverUnion U s) :=
  isOpen_iUnion fun i => isOpen_iUnion (hU i)

def nestedCoverSubtypeHomeomorph [TopologicalSpace X] {A B : Set X} (h : A ⊆ B) :
    (Subtype.val ⁻¹' A : Set B) ≃ₜ A where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

end BanachIsometric.SingularPrism
