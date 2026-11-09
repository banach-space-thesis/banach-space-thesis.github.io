import BanachIsometric.SphereAntipodalDegree
import BanachIsometric.HomogeneousGeometry

/-! The actual hairy-ball obstruction on an even-dimensional real sphere,
obtained by normalizing a nonzero tangent field and comparing signed degrees. -/

namespace BanachIsometric

open Metric NormedSpace
open scoped Topology

theorem no_nonzero_tangent_sphere_field_of_odd_finrank
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {N : ℕ} [NeZero N]
    (e : V ≃L[ℝ] PiolaSpace N) (hOdd : Odd (Module.finrank ℝ V))
    (w : C(sphere (0 : V) 1, V)) (hne : ∀ u, w u ≠ 0)
    (hTangent : ∀ u, inner ℝ u.val (w u) = 0) : False := by
  let w' : C(sphere (0 : V) 1, sphere (0 : V) 1) := by
    refine ⟨fun u => ⟨normalize (w u), ?_⟩, ?_⟩
    · simpa only [mem_sphere, dist_zero_right] using norm_normalize (hne u)
    · apply Continuous.subtype_mk
      exact (w.continuous.norm.inv₀ (fun u => norm_ne_zero_iff.mpr (hne u))).smul w.continuous
  apply no_unit_tangent_sphere_map_of_odd_finrank e hOdd w'
  intro u
  change inner ℝ u.val (‖w u‖⁻¹ • w u) = 0
  rw [inner_smul_right, hTangent, mul_zero]

end BanachIsometric
