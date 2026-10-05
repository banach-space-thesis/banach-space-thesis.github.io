import Posets.AlspachCounterexampleGraftEquiv

/-! A compact pointed space supplies a punctured locally compact spine.
Completing that spine and attaching its endpoint recovers an actual closed
embedded copy of the original compact space. -/

noncomputable section
open Set Topology
open scoped OnePoint
namespace Posets

instance alspachPuncturedLocallyCompact {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [T1Space X] (p : X) : LocallyCompactSpace {x : X // x ≠ p} :=
  (isOpen_compl_singleton : IsOpen ({p}ᶜ : Set X)).locallyCompactSpace

def alspachPunctureHomeomorph {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (p : X) : OnePoint {x : X // x ≠ p} ≃ₜ X :=
  OnePoint.equivOfIsEmbeddingOfRangeEq p Subtype.val IsEmbedding.subtypeVal (by
    ext x; simp)

@[simp] theorem alspachPunctureHomeomorph_infty {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (p : X) : alspachPunctureHomeomorph p ∞ = p := rfl

@[simp] theorem alspachPunctureHomeomorph_coe {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (p : X) (x : {x : X // x ≠ p}) :
    alspachPunctureHomeomorph p (x : OnePoint _) = x.val := rfl

@[simp] theorem alspachPunctureHomeomorph_symm_root {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (p : X) : (alspachPunctureHomeomorph p).symm p = ∞ := by
  apply (alspachPunctureHomeomorph p).injective
  simp

@[simp] theorem alspachPunctureHomeomorph_symm_nonroot {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (p x : X) (h : x ≠ p) :
    (alspachPunctureHomeomorph p).symm x = (⟨x, h⟩ : {x : X // x ≠ p}) := by
  apply (alspachPunctureHomeomorph p).injective
  simp

variable {K I : Type*} [TopologicalSpace K] (anchor : I → K)
  (X : I → Type*) [∀ i, TopologicalSpace (X i)]
  [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] (p : ∀ i, X i)

def alspachCompactGraftAttach (i : I) (x : X i) :
    AlspachGraft anchor (fun i => {x : X i // x ≠ p i}) :=
  alspachGraftCompletedSpine anchor _ i ((alspachPunctureHomeomorph (p i)).symm x)

theorem alspachCompactGraftAttach_continuous (i : I) :
    Continuous (alspachCompactGraftAttach anchor X p i) :=
  (alspachGraftCompletedSpine_continuous anchor _ i).comp
    (alspachPunctureHomeomorph (p i)).symm.continuous

@[simp] theorem alspachCompactGraftAttach_root (i : I) :
    alspachCompactGraftAttach anchor X p i (p i) = alspachGraftBase anchor _ (anchor i) := by
  simp [alspachCompactGraftAttach]

@[simp] theorem alspachCompactGraftAttach_nonroot (i : I) (x : X i) (h : x ≠ p i) :
    alspachCompactGraftAttach anchor X p i x = alspachGraftSpine anchor _ ⟨i, ⟨x, h⟩⟩ := by
  simp [alspachCompactGraftAttach, alspachPunctureHomeomorph_symm_nonroot, h]

theorem alspachCompactGraftAttach_isClosedEmbedding [T2Space K] (i : I) :
    IsClosedEmbedding (alspachCompactGraftAttach anchor X p i) :=
  (alspachGraftCompletedSpine_isClosedEmbedding anchor _ i).comp
    (alspachPunctureHomeomorph (p i)).symm.isClosedEmbedding

end Posets
