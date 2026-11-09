import BanachIsometric.ExactFamilyBodyCount
import BanachIsometric.SphereSignedDegreeSurjective

/-! # The exact family's normal index is its actual sphere degree -/

namespace BanachIsometric.ExactTangentialFamily

open scoped NNReal

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {g : V → ℝ} {p : E → ℝ} (A : ExactTangentialFamily E V g p)
  {n : ℕ} [NeZero n]

theorem normalConeSignedIndex_eq_sphereSignedDegree (e : V ≃L[ℝ] PiolaSpace n) :
    A.normalConeSignedIndex e = sphereSignedDegree e A.normal := rfl

theorem normal_surjective_of_nonzero_normalConeSignedIndex
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (e : V ≃L[ℝ] PiolaSpace n) (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal)
    (hindex : A.normalConeSignedIndex e ≠ 0) : Function.Surjective A.normal := by
  obtain ⟨L, hL⟩ := hnormal
  apply sphereSignedDegree_surjective_of_ne_zero e hL
  rwa [← A.normalConeSignedIndex_eq_sphereSignedDegree e]

end BanachIsometric.ExactTangentialFamily
