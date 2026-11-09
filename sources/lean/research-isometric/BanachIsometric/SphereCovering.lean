import BanachIsometric.SphereSimplyConnected
import BanachIsometric.ComponentCovering

/-! Actual covering sections over the actual Euclidean sphere. -/

noncomputable section

namespace BanachIsometric

open Metric
open scoped Topology

theorem locPathConnectedSpace_euclidean_sphere (n : ℕ) :
    LocPathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  exact ChartedSpace.locPathConnectedSpace (H := EuclideanSpace ℝ (Fin n))
    (M := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- A specified point of an actual covering over `Sⁿ`, `n ≥ 2`, extends to
an actual continuous section. Sphere simple connectivity is proved above. -/
theorem exists_continuous_euclidean_sphere_covering_section
    (n : ℕ) (hn : 2 ≤ n) {E : Type*} [TopologicalSpace E]
    {p : E → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}
    (hp : IsCoveringMap p) (b₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (e₀ : E) (he₀ : p e₀ = b₀) :
    ∃ s : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, E),
      s b₀ = e₀ ∧ ∀ b, p (s b) = b := by
  letI := simplyConnectedSpace_euclidean_sphere n hn
  letI := locPathConnectedSpace_euclidean_sphere n
  exact exists_continuous_covering_section hp b₀ e₀ he₀

end BanachIsometric
