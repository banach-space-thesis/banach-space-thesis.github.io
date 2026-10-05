import Posets.AlspachCounterexampleCompactSpines

/-! Finite closed covers of a graft by its remaining spines and finitely
many completed exceptional spines. These are the topological covers in
the threshold-doubling argument of Alspach's Lemma 3.3. -/

noncomputable section
open Set Topology
open scoped OnePoint
namespace Posets
variable {K I : Type*} [TopologicalSpace K] (anchor : I → K)
  (X : I → Type*) [∀ i, TopologicalSpace (X i)]

def alspachGraftOpenSpine (i : I) : Set (AlspachGraft anchor X) :=
  Set.range (fun x : X i => alspachGraftSpine anchor X ⟨i, x⟩)

theorem alspachGraftOpenSpine_isOpen (i : I) :
    IsOpen (alspachGraftOpenSpine anchor X i) := by
  change IsOpen (Set.range ((alspachGraftSpine anchor X) ∘ Sigma.mk i))
  rw [Set.range_comp]
  exact (alspachGraftSpine_isOpenEmbedding anchor X).isOpenMap _ isOpen_range_sigmaMk

theorem alspachGraftBase_not_mem_openSpine (k : K) (i : I) :
    alspachGraftBase anchor X k ∉ alspachGraftOpenSpine anchor X i := by
  rintro ⟨x, hx⟩
  exact OnePoint.coe_ne_infty (⟨i, x⟩ : Σ i, X i)
    (congrArg (alspachGraftProjection anchor X) hx)

theorem alspachGraftSpine_mem_openSpine_iff (z : Σ i, X i) (i : I) :
    alspachGraftSpine anchor X z ∈ alspachGraftOpenSpine anchor X i ↔ z.1 = i := by
  constructor
  · rintro ⟨x, hx⟩
    exact (congrArg Sigma.fst ((alspachGraftSpine_injective anchor X) hx)).symm
  · rcases z with ⟨j, x⟩
    intro h
    change j = i at h
    subst j
    exact ⟨x, rfl⟩

def alspachGraftOutsideSpines (s : Finset I) : Set (AlspachGraft anchor X) :=
  (⋃ i ∈ s, alspachGraftOpenSpine anchor X i)ᶜ

theorem alspachGraftOutsideSpines_isClosed (s : Finset I) :
    IsClosed (alspachGraftOutsideSpines anchor X s) :=
  (isOpen_iUnion fun i => isOpen_iUnion fun _ => alspachGraftOpenSpine_isOpen anchor X i).isClosed_compl

theorem alspachGraftBase_mem_outsideSpines (s : Finset I) (k : K) :
    alspachGraftBase anchor X k ∈ alspachGraftOutsideSpines anchor X s := by
  intro h
  obtain ⟨i, hi⟩ := mem_iUnion.mp h
  obtain ⟨_, hi⟩ := mem_iUnion.mp hi
  exact alspachGraftBase_not_mem_openSpine anchor X k i hi

theorem alspachGraftSpine_mem_outsideSpines_iff (s : Finset I) (z : Σ i, X i) :
    alspachGraftSpine anchor X z ∈ alspachGraftOutsideSpines anchor X s ↔ z.1 ∉ s := by
  simp only [alspachGraftOutsideSpines, mem_compl_iff, mem_iUnion,
    alspachGraftSpine_mem_openSpine_iff]
  aesop

variable [∀ i, T2Space (X i)] [∀ i, LocallyCompactSpace (X i)]

def alspachGraftFiniteCover (s : Finset I) : Option {i // i ∈ s} → Set (AlspachGraft anchor X)
  | none => alspachGraftOutsideSpines anchor X s
  | some i => Set.range (alspachGraftCompletedSpine anchor X i)

theorem alspachGraftFiniteCover_isClosed [T2Space K] (s : Finset I)
    (j : Option {i // i ∈ s}) : IsClosed (alspachGraftFiniteCover anchor X s j) := by
  cases j with
  | none => exact alspachGraftOutsideSpines_isClosed anchor X s
  | some i => exact (alspachGraftCompletedSpine_isClosedEmbedding anchor X i).isClosed_range

theorem alspachGraftFiniteCover_iUnion (s : Finset I) :
    (⋃ j, alspachGraftFiniteCover anchor X s j) = Set.univ := by
  apply eq_univ_of_forall
  intro x
  rcases alspachGraft_cases anchor X x with ⟨k, rfl⟩ | ⟨⟨i, y⟩, rfl⟩
  · exact mem_iUnion.mpr ⟨none, alspachGraftBase_mem_outsideSpines anchor X s k⟩
  · by_cases hi : i ∈ s
    · exact mem_iUnion.mpr ⟨some ⟨i, hi⟩, ⟨(y : OnePoint (X i)), rfl⟩⟩
    · exact mem_iUnion.mpr ⟨none,
        (alspachGraftSpine_mem_outsideSpines_iff anchor X s ⟨i, y⟩).mpr hi⟩

end Posets
