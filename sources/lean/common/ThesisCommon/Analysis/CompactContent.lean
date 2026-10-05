import ThesisCommon.Analysis.DominatedContent
import Mathlib.Topology.ClopenBox
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! A content on the clopen algebra of a compact space is automatically
sigma-subadditive: every countable clopen cover of a clopen set has a finite
subcover. This gives an actual Borel measure without an integral dominator. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Classical
namespace ThesisCommon
variable {X : Type*} [TopologicalSpace X]

def clopenAlgebra (X : Type*) [TopologicalSpace X] : Set (Set X) := {s | IsClopen s}

theorem clopenAlgebra_isSetAlgebra : IsSetAlgebra (clopenAlgebra X) where
  empty_mem := isClopen_empty
  compl_mem := fun _ hs => hs.compl
  union_mem := fun _ _ hs ht => hs.union ht

theorem clopenContent_sigmaSubadditive [CompactSpace X]
    (c : AddContent (clopenAlgebra X)) : c.IsSigmaSubadditive := by
  intro f hf hUnion
  obtain ⟨I, hI⟩ := hUnion.isClosed.isCompact.elim_finite_subcover f
    (fun n => (hf n).isOpen) (Subset.refl _)
  have hmem : (I.image f : Set (Set X)) ⊆ clopenAlgebra X := by
    rintro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact hf i
  have hcover : (⋃ n, f n) ⊆ ⋃₀ (I.image f : Set (Set X)) := by
    simpa only [Finset.coe_image, sUnion_image, Finset.mem_coe] using hI
  calc
    c (⋃ n, f n) ≤ ∑ s ∈ I.image f, c s :=
      addContent_le_sum_of_subset_sUnion clopenAlgebra_isSetAlgebra.isSetRing.isSetSemiring
        hmem hUnion hcover
    _ ≤ ∑ i ∈ I, c (f i) := Finset.sum_image_le_of_nonneg (fun _ _ => zero_le _)
    _ ≤ ∑' i, c (f i) := ENNReal.sum_le_tsum I

theorem generateFrom_clopenAlgebra [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [SecondCountableTopology X]
    [mX : MeasurableSpace X] [BorelSpace X] :
    mX = MeasurableSpace.generateFrom (clopenAlgebra X) := by
  rw [@BorelSpace.measurable_eq X _ mX _]
  exact isTopologicalBasis_isClopen.borel_eq_generateFrom

def measureOfClopenContent [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (c : AddContent (clopenAlgebra X)) : Measure X :=
  c.measure clopenAlgebra_isSetAlgebra.isSetRing.isSetSemiring
    generateFrom_clopenAlgebra.le (clopenContent_sigmaSubadditive c)

theorem measureOfClopenContent_apply [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (c : AddContent (clopenAlgebra X)) {s : Set X} (hs : IsClopen s) :
    measureOfClopenContent c s = c s :=
  c.measure_eq clopenAlgebra_isSetAlgebra.isSetRing.isSetSemiring
    generateFrom_clopenAlgebra (clopenContent_sigmaSubadditive c) hs

end ThesisCommon
