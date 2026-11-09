import BanachIsometric.ContinuousSphereApproximation
import BanachIsometric.CompactLipschitzOperations
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Actual sphere approximation preserving specified Lipschitz germs

On an actual compact subset where the given continuous sphere map is
Lipschitz, an exact finite-dimensional Lipschitz extension is available.
A metric Lipschitz cutoff blends it with a global close approximation.
Normalization produces a genuine sphere map equal to the original on that
entire compact subset. Choosing the subset to contain neighborhoods of
specified points preserves their actual derivative germs.
-/

namespace BanachIsometric

open Set Metric NormedSpace
open scoped Topology NNReal

theorem exists_lipschitz_sphere_approximation_relative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : C(sphere (0 : V) 1, sphere (0 : V) 1))
    {A : Set (sphere (0 : V) 1)} (hA : IsCompact A) {Cf : ℝ≥0}
    (hfA : LipschitzOnWith Cf f A) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : C(sphere (0 : V) 1, sphere (0 : V) 1), ∃ L : ℝ≥0,
      LipschitzWith L G ∧ (∀ z, dist (G z) (f z) < ε) ∧ EqOn G f A := by
  let S := sphere (0 : V) 1
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  by_cases hAnon : A.Nonempty
  swap
  · obtain ⟨g, L, hL, hc⟩ := exists_lipschitz_sphere_approximation_on_compact
      (isCompact_sphere (0 : V) 1) f hε
    exact ⟨⟨g, hL.continuous⟩, L, hL, hc, fun z hz => (hAnon ⟨z, hz⟩).elim⟩
  let δ : ℝ := min (ε / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hrawA : LipschitzOnWith Cf (fun z : S => (f z).val) A := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Subtype.dist_eq] using hfA.dist_le_mul x hx y hy
  obtain ⟨u, hu, hueq⟩ := hrawA.extend_finite_dimension
  let U : Set S := {z | dist (u z) (f z).val < δ}
  have hU : IsOpen U := isOpen_lt
    (hu.continuous.dist (continuous_subtype_val.comp f.continuous)) continuous_const
  have hAU : A ⊆ U := by
    intro z hz
    change dist (u z) (f z).val < δ
    rw [← hueq hz, dist_self]
    exact hδ
  obtain ⟨r, hr, hnear⟩ := hA.exists_thickening_subset_open hU hAU
  let T : ℝ →L[ℝ] ℝ := r⁻¹ • ContinuousLinearMap.id ℝ ℝ
  have hd : LipschitzWith (‖T‖₊ * 1) (fun z : S => infDist z A / r) := by
    convert T.lipschitz.comp (lipschitz_infDist_pt A) using 1
    funext z
    change infDist z A / r = r⁻¹ * infDist z A
    rw [div_eq_mul_inv, mul_comm]
  let χ : S → ℝ := fun z => max 0 (1 - infDist z A / r)
  have hχ : LipschitzWith _ χ := ((LipschitzWith.const (1 : ℝ)).sub hd).const_max 0
  have hχ0 (z : S) : 0 ≤ χ z := le_max_left _ _
  have hχ1 (z : S) : χ z ≤ 1 := by
    apply max_le (by norm_num)
    have hdiv : 0 ≤ infDist z A / r := div_nonneg infDist_nonneg hr.le
    linarith
  have hχA (z : S) (hz : z ∈ A) : χ z = 1 := by
    simp only [χ, infDist_zero_of_mem hz, zero_div, sub_zero, max_eq_right zero_le_one]
  have hχnear (z : S) (hz : χ z ≠ 0) : z ∈ U := by
    apply hnear
    apply (mem_thickening_iff_infDist_lt hAnon).mpr
    by_contra hdist
    have hdiv : 1 ≤ infDist z A / r := by
      apply (le_div_iff₀ hr).mpr
      simpa only [one_mul] using le_of_not_gt hdist
    exact hz (max_eq_left (by linarith : 1 - infDist z A / r ≤ 0))
  obtain ⟨g, Cg, hg, hgclose⟩ := exists_lipschitz_sphere_approximation_on_compact
    (isCompact_sphere (0 : V) 1) f hδ
  have hgv : LipschitzWith Cg (fun z : S => (g z).val) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Subtype.dist_eq] using hg.dist_le_mul x y
  obtain ⟨C₁, h₁⟩ := exists_lipschitz_smul_of_compact hχ hu
  obtain ⟨C₂, h₂⟩ := exists_lipschitz_smul_of_compact ((LipschitzWith.const (1 : ℝ)).sub hχ) hgv
  let η : S → V := fun z => χ z • u z + (1 - χ z) • (g z).val
  have hη : LipschitzWith (C₁ + C₂) η := h₁.add h₂
  have hηclose (z : S) : dist (η z) (f z).val < δ := by
    by_cases hz : χ z = 0
    · simpa only [η, hz, zero_smul, sub_zero, one_smul, zero_add, Subtype.dist_eq] using hgclose z
    · have huclose : dist (u z) (f z).val < δ := hχnear z hz
      have hgclose' : dist (g z).val (f z).val < δ := hgclose z
      exact mem_ball.mp ((convex_ball (f z).val δ) (mem_ball.mpr huclose)
        (mem_ball.mpr hgclose') (hχ0 z) (sub_nonneg.mpr (hχ1 z)) (by ring))
  have hnorm (z : S) : ‖(f z).val‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using (f z).property
  have hlower (z : S) : (1 / 2 : ℝ) ≤ ‖η z‖ := by
    have hn := norm_sub_norm_le (f z).val (η z)
    rw [hnorm, ← dist_eq_norm, dist_comm] at hn
    have hδle : δ ≤ 1 / 4 := min_le_right _ _
    linarith [hηclose z]
  have hne (z : S) : η z ≠ 0 := by
    intro hz
    have h := hlower z
    rw [hz, norm_zero] at h
    norm_num at h
  have hnLip := lipschitzWith_normalize_of_lower_bound hη
    (show (0 : ℝ≥0) < 1 / 2 by norm_num) hlower
  have hmem (z : S) : normalize (η z) ∈ S := by
    change normalize (η z) ∈ sphere (0 : V) 1
    simpa only [mem_sphere, dist_zero_right] using norm_normalize (hne z)
  let G : C(S, S) :=
    ⟨fun z => ⟨normalize (η z), hmem z⟩, hnLip.continuous.subtype_mk hmem⟩
  refine ⟨G, _, LipschitzWith.of_dist_le_mul (fun x y => hnLip.dist_le_mul x y), ?_, ?_⟩
  · intro z
    have hb := norm_mul_normalize_sub_le (f z).val (η z) (hne z)
    rw [hnorm, one_mul, normalize_eq_self_of_norm_eq_one (hnorm z),
      ← dist_eq_norm, ← dist_eq_norm, dist_comm (f z).val (η z)] at hb
    have hδε : δ ≤ ε / 4 := min_le_left _ _
    change dist (normalize (η z)) (f z).val < ε
    rw [dist_comm]
    linarith [hηclose z]
  · intro z hz
    apply Subtype.ext
    change normalize (η z) = (f z).val
    have hηz : η z = (f z).val := by
      simp only [η, hχA z hz, one_smul, sub_self, zero_smul, add_zero]
      exact (hueq hz).symm
    rw [hηz]
    exact normalize_eq_self_of_norm_eq_one (hnorm z)

end BanachIsometric
