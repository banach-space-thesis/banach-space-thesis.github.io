import Mathlib.Data.Set.Countable

/-! Countable vertex covers for a parametrised relation, and their closure properties. -/
noncomputable section
open Set
namespace Posets

variable {X Y Z : Type*}

def CountablyCoordinateCovered (p q : X → Y) (s : Set X) : Prop :=
  ∃ A : Set Y, A.Countable ∧ ∀ x ∈ s, p x ∈ A ∨ q x ∈ A

theorem countablyCoordinateCovered_mono {p q : X → Y} {s t : Set X}
    (hst : s ⊆ t) (ht : CountablyCoordinateCovered p q t) :
    CountablyCoordinateCovered p q s := by
  obtain ⟨A, hAc, hA⟩ := ht
  exact ⟨A, hAc, fun x hx => hA x (hst hx)⟩

theorem countablyCoordinateCovered_sUnion (p q : X → Y) (S : Set (Set X))
    (hS : S.Countable) (hs : ∀ s ∈ S, CountablyCoordinateCovered p q s) :
    CountablyCoordinateCovered p q (⋃₀ S) := by
  classical
  letI : Countable S := hS.to_subtype
  choose A hAc hA using fun s : S => hs s.val s.property
  refine ⟨⋃ s : S, A s, Set.countable_iUnion hAc, ?_⟩
  intro x hx
  obtain ⟨s, hsS, hxs⟩ := Set.mem_sUnion.mp hx
  rcases hA ⟨s, hsS⟩ x hxs with hp | hq
  · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨s, hsS⟩, hp⟩)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨s, hsS⟩, hq⟩)

theorem countablyCoordinateCovered_image_iff (p q : Y → Z) (f : X → Y) (s : Set X) :
    CountablyCoordinateCovered p q (f '' s) ↔
      CountablyCoordinateCovered (p ∘ f) (q ∘ f) s := by
  constructor
  · rintro ⟨A, hAc, hA⟩
    exact ⟨A, hAc, fun x hx => hA (f x) ⟨x, hx, rfl⟩⟩
  · rintro ⟨A, hAc, hA⟩
    refine ⟨A, hAc, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hA x hx

/-- In a set with no countable coordinate cover one can avoid both coordinates
of any given point. Coincidence between the two coordinates of one point is allowed. -/
theorem exists_disjoint_coordinate_pair {p q : X → Y} {s : Set X}
    (hs : ¬ CountablyCoordinateCovered p q s) (x : X) :
    ∃ y ∈ s, Disjoint ({p x, q x} : Set Y) {p y, q y} := by
  classical
  have hex : ∃ y ∈ s, p y ∉ ({p x, q x} : Set Y) ∧ q y ∉ ({p x, q x} : Set Y) := by
    by_contra hn
    push_neg at hn
    apply hs
    refine ⟨{p x, q x}, ((Set.finite_singleton _).insert _).countable, ?_⟩
    intro y hy
    by_cases hp : p y ∈ ({p x, q x} : Set Y)
    · exact Or.inl hp
    · exact Or.inr (hn y hy hp)
  obtain ⟨y, hy, hp, hq⟩ := hex
  refine ⟨y, hy, Set.disjoint_left.mpr ?_⟩
  intro a ha hb
  rcases Set.mem_insert_iff.mp hb with rfl | hb
  · exact hp ha
  · obtain rfl := Set.mem_singleton_iff.mp hb
    exact hq ha

/-- Both coordinate images of a subset of the parameter space. -/
def coordinateImage (p q : X → Y) (s : Set X) : Set Y := p '' s ∪ q '' s

theorem coordinatePair_subset_coordinateImage {p q : X → Y} {s : Set X} {x : X}
    (hx : x ∈ s) : ({p x, q x} : Set Y) ⊆ coordinateImage p q s := by
  intro a ha
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · exact Or.inl ⟨x, hx, rfl⟩
  · obtain rfl := Set.mem_singleton_iff.mp ha
    exact Or.inr ⟨x, hx, rfl⟩

end Posets
