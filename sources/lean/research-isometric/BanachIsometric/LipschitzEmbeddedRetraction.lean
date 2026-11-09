import BanachIsometric.LipschitzNeighborhoodRetraction
import Mathlib.Topology.MetricSpace.Isometry

/-! A retraction returning a space embedded isometrically in the ambient
normed space yields a neighborhood retraction onto its literal range. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set
open scoped NNReal

variable {E X : Type*} [NormedAddCommGroup E] [MetricSpace X]

def LipschitzNeighborhoodRetraction.of_isometric_embedding
    {i : X → E} (hi : Isometry i) {A : Set E} (r : A → X)
    {L : ℝ≥0} (hL : LipschitzWith L r)
    (hFix : ∀ x : X, ∃ hx : i x ∈ interior A, r ⟨i x, interior_subset hx⟩ = x) :
    LipschitzNeighborhoodRetraction (range i) := by
  let e := hi.isometryEquivOnRange
  have hA : range i ⊆ interior A := by
    rintro _ ⟨x, rfl⟩
    exact (hFix x).choose
  refine LipschitzNeighborhoodRetraction.of_subset_interior (e ∘ r)
    (L := 1 * L) (e.isometry.lipschitz.comp hL) hA ?_
  rintro ⟨_, x, rfl⟩
  change e (r ⟨i x, _⟩) = ⟨i x, _⟩
  rw [(hFix x).choose_spec]
  rfl

end BanachIsometric.SingularPrism
