import BanachIsometric.ContinuousCompactApproximation
import BanachIsometric.LipschitzNormalization
import BanachIsometric.CloseSphereHomotopy
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Actual smooth sphere approximation with an actual homotopy

The approximation is smooth for Mathlib's genuine sphere manifold structure,
globally Lipschitz for the original sphere metric, and homotopic to the supplied
continuous sphere map. The smoothness order is explicitly C-infinity, rather
than the stronger analytic order. No smooth approximation theorem is assumed
as a premise.
-/

noncomputable section
namespace BanachIsometric

open Set Metric
open scoped Topology NNReal ContDiff Manifold

theorem exists_smooth_lipschitz_approximation_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {s : Set E} (hs : IsCompact s) (f : C(s, F)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ (⊤ : ℕ∞) g ∧ ∃ L : ℝ≥0,
      LipschitzWith L g ∧ ∀ x : s, dist (g x.val) (f x) < ε := by
  obtain ⟨u, _Lu, hu, huclose⟩ := exists_lipschitz_approximation_on_compact hs f (half_pos hε)
  obtain ⟨v, hv, hvclose⟩ := hu.uniformContinuous.exists_contDiff_dist_le (half_pos hε)
  obtain ⟨R, hR, hsR⟩ := hs.isBounded.subset_closedBall_lt (0 : ℝ) (0 : E)
  let χ : ContDiffBump (0 : E) := ⟨R, 2 * R, hR, by linarith⟩
  have hχ (x : s) : χ x.val = 1 := χ.one_of_mem_closedBall (hsR x.property)
  have hcompact : HasCompactSupport (fun x => χ x • v x) := χ.hasCompactSupport.smul_right
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x • v x) := χ.contDiff.smul hv
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hsmooth (by simp)
  refine ⟨fun x => χ x • v x, hsmooth, L, hL, ?_⟩
  intro x
  change dist (χ x.val • v x.val) (f x) < ε
  rw [hχ x, one_smul]
  exact (dist_triangle (v x.val) (u x.val) (f x)).trans_lt
    (by linarith [hvclose x.val, huclose x])

theorem exists_smooth_lipschitz_sphere_map_homotopic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : C(sphere (0 : V) 1, sphere (0 : V) 1),
      ContMDiff (𝓡 n) (𝓡 n) (⊤ : ℕ∞) ψ ∧ ∃ L : ℝ≥0,
      LipschitzWith L ψ ∧ (∀ z, dist (ψ z) (φ z) < ε) ∧
      Nonempty (ContinuousMap.Homotopy φ ψ) := by
  let δ : ℝ := min (ε / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  obtain ⟨u, hu, L, hL, hclose⟩ := exists_smooth_lipschitz_approximation_on_compact
    (isCompact_sphere (0 : V) 1)
    ⟨fun x => (φ x).val, continuous_subtype_val.comp φ.continuous⟩ hδ
  have hnorm (x : sphere (0 : V) 1) : ‖(φ x).val‖ = 1 := norm_eq_of_mem_sphere (φ x)
  have hlower (x : sphere (0 : V) 1) : (1 / 2 : ℝ) ≤ ‖u x.val‖ := by
    have hd := hclose x
    change dist (u x.val) (φ x).val < δ at hd
    have hn := norm_sub_norm_le (φ x).val (u x.val)
    rw [hnorm, ← dist_eq_norm, dist_comm] at hn
    have hδle : δ ≤ 1 / 4 := min_le_right _ _
    linarith
  have hne (x : sphere (0 : V) 1) : u x.val ≠ 0 := by
    intro hz
    have hx := hlower x
    rw [hz, norm_zero] at hx
    norm_num at hx
  have hLip : LipschitzWith L (fun x : sphere (0 : V) 1 => u x.val) := by
    simpa only [mul_one] using hL.comp (LipschitzWith.subtype_val (sphere (0 : V) 1))
  have hnLip := lipschitzWith_normalize_of_lower_bound hLip
    (show (0 : ℝ≥0) < 1 / 2 by norm_num) hlower
  have hmem (x : sphere (0 : V) 1) : NormedSpace.normalize (u x.val) ∈ sphere (0 : V) 1 := by
    simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize (hne x)
  let ψ : C(sphere (0 : V) 1, sphere (0 : V) 1) :=
    ⟨fun x => ⟨NormedSpace.normalize (u x.val), hmem x⟩,
      hnLip.continuous.subtype_mk _⟩
  have hψLip : LipschitzWith _ ψ := LipschitzWith.of_dist_le_mul (fun x y => hnLip.dist_le_mul x y)
  have hψsmooth : ContMDiff (𝓡 n) (𝓡 n) (⊤ : ℕ∞) ψ := by
    have hval : ContMDiff (𝓡 n) 𝓘(ℝ, V) (⊤ : ℕ∞)
        (fun x : sphere (0 : V) 1 => NormedSpace.normalize (u x.val)) := by
      intro x
      have huN := (hu.contDiffAt.norm ℝ (hne x)).inv (norm_ne_zero_iff.mpr (hne x))
      have hambient : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => NormedSpace.normalize (u y)) x.val := by
        simpa only [NormedSpace.normalize] using huN.smul hu.contDiffAt
      exact hambient.contMDiffAt.comp x (contMDiff_coe_sphere.contMDiffAt)
    exact hval.codRestrict_sphere hmem
  have hbound (x : sphere (0 : V) 1) : dist (ψ x) (φ x) < 2 * δ := by
    have hb := norm_mul_normalize_sub_le (φ x).val (u x.val) (hne x)
    rw [hnorm, one_mul, NormedSpace.normalize_eq_self_of_norm_eq_one (hnorm x),
      ← dist_eq_norm, ← dist_eq_norm, dist_comm (φ x).val (u x.val)] at hb
    have hd := hclose x
    change dist (u x.val) (φ x).val < δ at hd
    change dist (NormedSpace.normalize (u x.val)) (φ x).val < 2 * δ
    rw [dist_comm]
    linarith
  refine ⟨ψ, hψsmooth, _, hψLip, ?_, ?_⟩
  · intro x
    have hδε : δ ≤ ε / 4 := min_le_left _ _
    exact (hbound x).trans (by linarith)
  · refine ⟨closeSphereHomotopy φ ψ (fun x => ?_)⟩
    rw [dist_comm]
    have hδle : δ ≤ 1 / 4 := min_le_right _ _
    exact (hbound x).trans (by linarith)

end BanachIsometric
