import BanachIsometric.PathConnectedZeroHomology
import BanachIsometric.SphereGenerator
import Mathlib.Analysis.NormedSpace.Connected

/-! H0 of the ACTUAL positive-dimensional Euclidean sphere, including S1.
This uses its actual path-connectedness and the explicit path/prism quotient
calculation, without any simplicial comparison premise. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open SphereGenerator

theorem pathConnectedSpace_positive_sphere (n : ℕ) : PathConnectedSpace (Sph (n + 1)) := by
  have hr : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 2))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < n + 2 by omega)
  exact isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hr 0 zero_le_one)

def rawZeroHomologyPositiveSphereEquiv (n : ℕ) : RawZeroHomology (Sph (n + 1)) ≃ₗ[ℚ] ℚ := by
  letI := pathConnectedSpace_positive_sphere n
  exact rawZeroHomologyPathConnectedEquiv (sphereBasepoint (n + 1))

end BanachIsometric.SingularPrism
