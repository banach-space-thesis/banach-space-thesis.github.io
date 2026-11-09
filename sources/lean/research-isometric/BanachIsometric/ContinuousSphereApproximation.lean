import BanachIsometric.ContinuousCompactApproximation
import BanachIsometric.LipschitzNormalization

/-!
# Actual Lipschitz approximation of continuous sphere families

An ambient Lipschitz approximation stays uniformly away from zero. Normalizing
it gives an actual sphere-valued Lipschitz approximation, in the given norms.
The product version applies to an arbitrary continuous sphere homotopy; it
does not assume any Lipschitz regularity of the original homotopy in time.
Its endpoints are close to the original endpoints, not asserted equal.
-/

namespace BanachIsometric

open Set Metric NormedSpace
open scoped Topology NNReal

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem exists_lipschitz_sphere_approximation_on_compact
    {s : Set W} (hs : IsCompact s) (f : C(s, sphere (0 : V) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : s → sphere (0 : V) 1, ∃ L : ℝ≥0,
      LipschitzWith L g ∧ ∀ x, dist (g x) (f x) < ε := by
  let δ : ℝ := min (ε / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  obtain ⟨u, L, hL, hclose⟩ := exists_lipschitz_approximation_on_compact hs
    ⟨fun x => (f x).val, continuous_subtype_val.comp f.continuous⟩ hδ
  have hnorm (x : s) : ‖(f x).val‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using (f x).property
  have hlower (x : s) : (1 / 2 : ℝ) ≤ ‖u x.val‖ := by
    have hd := hclose x
    change dist (u x.val) (f x).val < δ at hd
    have hn := norm_sub_norm_le (f x).val (u x.val)
    rw [hnorm, ← dist_eq_norm, dist_comm] at hn
    have hδle : δ ≤ 1 / 4 := min_le_right _ _
    linarith
  have hne (x : s) : u x.val ≠ 0 := by
    intro hz
    have hx := hlower x
    rw [hz, norm_zero] at hx
    norm_num at hx
  have hLip : LipschitzWith L (fun x : s => u x.val) :=
    by simpa only [mul_one] using hL.comp (LipschitzWith.subtype_val s)
  have hnLip := lipschitzWith_normalize_of_lower_bound hLip
    (show (0 : ℝ≥0) < 1 / 2 by norm_num) hlower
  let g : s → sphere (0 : V) 1 := fun x =>
    ⟨normalize (u x.val), by
      simpa only [mem_sphere, dist_zero_right] using norm_normalize (hne x)⟩
  refine ⟨g, _, LipschitzWith.of_dist_le_mul (fun x y => hnLip.dist_le_mul x y), ?_⟩
  intro x
  have hb := norm_mul_normalize_sub_le (f x).val (u x.val) (hne x)
  rw [hnorm, one_mul, normalize_eq_self_of_norm_eq_one (hnorm x),
    ← dist_eq_norm, ← dist_eq_norm, dist_comm (f x).val (u x.val)] at hb
  have hd := hclose x
  change dist (u x.val) (f x).val < δ at hd
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  change dist (normalize (u x.val)) (f x).val < ε
  rw [dist_comm]
  linarith

theorem exists_lipschitz_sphere_homotopy_approximation
    (H : C(unitInterval × sphere (0 : V) 1, sphere (0 : V) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : unitInterval × sphere (0 : V) 1 → sphere (0 : V) 1, ∃ L : ℝ≥0,
      LipschitzWith L G ∧ ∀ z, dist (G z) (H z) < ε := by
  let s : Set (ℝ × V) := Icc (0 : ℝ) 1 ×ˢ sphere (0 : V) 1
  have hs : IsCompact s := isCompact_Icc.prod (isCompact_sphere (0 : V) 1)
  let e : unitInterval × sphere (0 : V) 1 → s := fun z =>
    ⟨(z.1.val, z.2.val), z.1.property, z.2.property⟩
  let r : s → unitInterval × sphere (0 : V) 1 := fun z =>
    (⟨z.val.1, z.property.1⟩, ⟨z.val.2, z.property.2⟩)
  have hr : Continuous r :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _ |>.prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  obtain ⟨g, L, hL, hclose⟩ := exists_lipschitz_sphere_approximation_on_compact hs
    ⟨fun z => H (r z), H.continuous.comp hr⟩ hε
  have he : LipschitzWith 1 e := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Subtype.dist_eq, Prod.dist_eq, NNReal.coe_one, one_mul, e]
    exact le_rfl
  exact ⟨g ∘ e, L * 1, hL.comp he, fun z => hclose (e z)⟩

end BanachIsometric
