import BanachIsometric.SphereSignedDegreeHomotopy

/-!
# Signed degree of every continuous map of the genuine norm sphere

A Lipschitz sphere approximation within `1/4` defines the degree. Two such
representatives are less than one apart and hence have the same proved actual
signed degree. Arbitrary continuous homotopy invariance follows from a joint
Lipschitz approximation of that actual homotopy and close endpoint comparisons.
No degree axiom or assumed homotopy invariance is introduced.
-/

namespace BanachIsometric

open Metric
open scoped Topology NNReal

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

structure SphereLipschitzRepresentative
    (f : C(sphere (0 : V) 1, sphere (0 : V) 1)) where
  map : sphere (0 : V) 1 → sphere (0 : V) 1
  constant : ℝ≥0
  lipschitz : LipschitzWith constant map
  close : ∀ z, dist (map z) (f z) < (1 / 4 : ℝ)

theorem nonempty_sphereLipschitzRepresentative
    (f : C(sphere (0 : V) 1, sphere (0 : V) 1)) :
    Nonempty (SphereLipschitzRepresentative f) := by
  obtain ⟨g, L, hL, hc⟩ := exists_lipschitz_sphere_approximation_on_compact
    (isCompact_sphere (0 : V) 1) f (by norm_num : (0 : ℝ) < 1 / 4)
  exact ⟨⟨g, L, hL, hc⟩⟩

def chosenSphereLipschitzRepresentative
    (f : C(sphere (0 : V) 1, sphere (0 : V) 1)) : SphereLipschitzRepresentative f :=
  Classical.choice (nonempty_sphereLipschitzRepresentative f)

def continuousSphereSignedDegree {n : ℕ} [NeZero n]
    (e : V ≃L[ℝ] PiolaSpace n) (f : C(sphere (0 : V) 1, sphere (0 : V) 1)) : ℤ :=
  sphereSignedDegree e (chosenSphereLipschitzRepresentative f).map

theorem sphereLipschitzRepresentatives_degree_eq {n : ℕ} [NeZero n]
    (e : V ≃L[ℝ] PiolaSpace n) {f : C(sphere (0 : V) 1, sphere (0 : V) 1)}
    (a b : SphereLipschitzRepresentative f) : sphereSignedDegree e a.map = sphereSignedDegree e b.map := by
  apply sphereSignedDegree_eq_of_close e a.lipschitz b.lipschitz
  intro z
  have ha := a.close z
  have hb := b.close z
  have ht := dist_triangle (a.map z) (f z) (b.map z)
  rw [dist_comm (f z) (b.map z)] at ht
  linarith

/-- Any actual Lipschitz representative within `1/4` computes the degree. -/
theorem continuousSphereSignedDegree_eq_of_lipschitz_approximation
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    (f : C(sphere (0 : V) 1, sphere (0 : V) 1))
    {g : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0}
    (hg : LipschitzWith C g) (hclose : ∀ z, dist (g z) (f z) < (1 / 4 : ℝ)) :
    continuousSphereSignedDegree e f = sphereSignedDegree e g :=
  sphereLipschitzRepresentatives_degree_eq e (chosenSphereLipschitzRepresentative f) ⟨g, C, hg, hclose⟩

theorem continuousSphereSignedDegree_eq_sphereSignedDegree
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    (f : C(sphere (0 : V) 1, sphere (0 : V) 1)) {C : ℝ≥0} (hf : LipschitzWith C f) :
    continuousSphereSignedDegree e f = sphereSignedDegree e f := by
  exact continuousSphereSignedDegree_eq_of_lipschitz_approximation e f hf
    (fun z => by rw [dist_self]; norm_num)

theorem continuousSphereSignedDegree_eq_of_homotopy
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {f g : C(sphere (0 : V) 1, sphere (0 : V) 1)} (H : ContinuousMap.Homotopy f g) :
    continuousSphereSignedDegree e f = continuousSphereSignedDegree e g := by
  let HC : C(unitInterval × sphere (0 : V) 1, sphere (0 : V) 1) :=
    ⟨fun z => H z, H.continuous⟩
  obtain ⟨G, L, hL, hclose⟩ := exists_lipschitz_sphere_homotopy_approximation HC
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hGs (t : unitInterval) : LipschitzWith (L * 1) (fun z => G (t, z)) :=
    hL.comp (LipschitzWith.prodMk_left t)
  have hleft : continuousSphereSignedDegree e f = sphereSignedDegree e (fun z => G (0, z)) := by
    apply continuousSphereSignedDegree_eq_of_lipschitz_approximation e f (hGs 0)
    intro z
    simpa only [HC, ContinuousMap.coe_mk, ContinuousMap.Homotopy.apply_zero] using hclose (0, z)
  have hright : continuousSphereSignedDegree e g = sphereSignedDegree e (fun z => G (1, z)) := by
    apply continuousSphereSignedDegree_eq_of_lipschitz_approximation e g (hGs 1)
    intro z
    simpa only [HC, ContinuousMap.coe_mk, ContinuousMap.Homotopy.apply_one] using hclose (1, z)
  have hmiddle := sphereSignedDegree_homotopy_eq e (fun t z => G (t, z)) hL.continuous
    (fun t => ⟨L * 1, hGs t⟩) (0 : unitInterval) 1
  exact hleft.trans (hmiddle.trans hright.symm)

theorem continuousSphereSignedDegree_eq_of_homotopic
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {f g : C(sphere (0 : V) 1, sphere (0 : V) 1)} (h : ContinuousMap.Homotopic f g) :
    continuousSphereSignedDegree e f = continuousSphereSignedDegree e g := by
  obtain ⟨H⟩ := h
  exact continuousSphereSignedDegree_eq_of_homotopy e H

theorem continuousSphereSignedDegree_id {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n) :
    continuousSphereSignedDegree e (ContinuousMap.id (sphere (0 : V) 1)) = 1 := by
  rw [continuousSphereSignedDegree_eq_sphereSignedDegree e _ (LipschitzWith.id)]
  exact sphereSignedDegree_id e

variable [MeasurableSpace V] [BorelSpace V]

theorem continuousSphereSignedDegree_eq_of_coordinates
    {n m : ℕ} [NeZero n] [NeZero m]
    (e : V ≃L[ℝ] PiolaSpace n) (e' : V ≃L[ℝ] PiolaSpace m)
    (f : C(sphere (0 : V) 1, sphere (0 : V) 1)) :
    continuousSphereSignedDegree e f = continuousSphereSignedDegree e' f :=
  sphereSignedDegree_eq_of_coordinates e e' (chosenSphereLipschitzRepresentative f).lipschitz

end

end BanachIsometric
