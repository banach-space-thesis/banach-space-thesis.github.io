import BanachIsometric.SphereSignedDegreeClose
import BanachIsometric.ContinuousSphereApproximation

/-!
# Invariance under arbitrary continuous sphere homotopies

Only the endpoint maps must be Lipschitz. A genuinely jointly Lipschitz sphere
approximation of the given continuous homotopy supplies Lipschitz slices.
The endpoint errors are removed by the proved close-map comparison.
-/

namespace BanachIsometric

open Metric
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem sphereSignedDegree_eq_of_continuous_homotopy
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    (H : C(unitInterval × sphere (0 : V) 1, sphere (0 : V) 1))
    {C₀ C₁ : ℝ≥0} (h₀ : LipschitzWith C₀ (fun z => H (0, z)))
    (h₁ : LipschitzWith C₁ (fun z => H (1, z))) :
    sphereSignedDegree e (fun z => H (0, z)) = sphereSignedDegree e (fun z => H (1, z)) := by
  obtain ⟨G, L, hL, hclose⟩ := exists_lipschitz_sphere_homotopy_approximation H
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hGs (t : unitInterval) : LipschitzWith (L * 1) (fun z => G (t, z)) :=
    hL.comp (LipschitzWith.prodMk_left t)
  have hleft := sphereSignedDegree_eq_of_close e h₀ (hGs 0) (fun z => by
    have h := hclose (0, z)
    rw [dist_comm] at h
    linarith)
  have hmiddle := sphereSignedDegree_homotopy_eq e (fun t z => G (t, z)) hL.continuous
    (fun t => ⟨L * 1, hGs t⟩) (0 : unitInterval) 1
  have hright := sphereSignedDegree_eq_of_close e (hGs 1) h₁ (fun z => by
    have h := hclose (1, z)
    linarith)
  exact hleft.trans (hmiddle.trans hright)

theorem sphereSignedDegree_eq_of_homotopy
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {f g : C(sphere (0 : V) 1, sphere (0 : V) 1)} {Cf Cg : ℝ≥0}
    (hf : LipschitzWith Cf f) (hg : LipschitzWith Cg g) (H : ContinuousMap.Homotopy f g) :
    sphereSignedDegree e f = sphereSignedDegree e g := by
  let HC : C(unitInterval × sphere (0 : V) 1, sphere (0 : V) 1) := ⟨fun z => H z, H.continuous⟩
  have h₀ : LipschitzWith Cf (fun z => HC (0, z)) := by
    simpa only [HC, ContinuousMap.coe_mk, ContinuousMap.Homotopy.apply_zero] using hf
  have h₁ : LipschitzWith Cg (fun z => HC (1, z)) := by
    simpa only [HC, ContinuousMap.coe_mk, ContinuousMap.Homotopy.apply_one] using hg
  simpa only [HC, ContinuousMap.coe_mk, ContinuousMap.Homotopy.apply_zero,
    ContinuousMap.Homotopy.apply_one] using sphereSignedDegree_eq_of_continuous_homotopy e HC h₀ h₁

end BanachIsometric
