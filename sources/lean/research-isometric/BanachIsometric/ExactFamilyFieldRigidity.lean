import BanachIsometric.ExactFamilyRigidity
import BanachIsometric.ExactFamilyAmbientQuadratic
import BanachIsometric.ExactFamilySphereDegree

/-!
# Actual nonzero-index exact families force ambient quadraticity

The reference quadratic form is derived by the signed integral and polynomial
argument. The actual signed degree makes the specified normal map surjective.
Every original section is therefore an actual range of the family, and
pair coverage transfers the quadratic conclusion to the ambient gauge.

The remaining global geometric obligation is to construct such a family
from the original section-bundle hypotheses. It is not assumed proved here.
-/

namespace BanachIsometric.ExactTangentialFamily

open MeasureTheory Set
open scoped NNReal

variable {m N : ℕ} [NeZero N]
  {g : EuclideanSpace ℝ (Fin N) → ℝ} {p : EuclideanSpace ℝ (Fin m) → ℝ}
  (A : ExactTangentialFamily (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin N)) g p)

theorem exists_posDef_ambient_quadraticForm_of_nonzero_normalConeSignedIndex
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] PiolaSpace N)
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (hEven : Even N)
    (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal)
    (hindex : A.normalConeSignedIndex e ≠ 0)
    (H : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 → Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (hRange : ∀ z, Set.range (A.maps z) = (H (A.normal z) : Set (EuclideanSpace ℝ (Fin N))))
    (hpair : ∀ x y, ∃ u, x ∈ H u ∧ y ∈ H u) :
    ∃ R : QuadraticForm ℝ (EuclideanSpace ℝ (Fin N)), R.PosDef ∧ ∀ x, R x = g x ^ 2 := by
  obtain ⟨Q, _hQpos, hQ⟩ := A.exists_posDef_quadraticForm_of_nonzero_normalConeSignedIndex
    μ e hp hg hcont hEven hnormal hindex
  apply A.exists_posDef_ambient_quadraticForm_of_pairwise_range hg hcont Q hQ
  intro x y
  obtain ⟨u, hx, hy⟩ := hpair x y
  obtain ⟨z, hz⟩ := A.normal_surjective_of_nonzero_normalConeSignedIndex e hnormal hindex u
  refine ⟨z, ?_, ?_⟩
  · rwa [hRange z, hz]
  · rwa [hRange z, hz]

end BanachIsometric.ExactTangentialFamily
