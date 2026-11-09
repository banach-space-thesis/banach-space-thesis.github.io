import BanachIsometric.SphereSignedDegreeClose
import BanachIsometric.ContinuousSphereApproximation

/-!
# Actual close-map homotopies and Lipschitz sphere representatives

Normalize the nonvanishing affine interpolation between sphere maps less than
one apart. This produces an actual continuous sphere homotopy for the given
norm, and turns uniform Lipschitz approximation into a homotopy-preserving
replacement. No degree statement is needed for this construction.
-/

namespace BanachIsometric

open NormedSpace Metric
open scoped Topology NNReal

noncomputable section

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X]

def closeSphereHomotopy (f g : C(X, sphere (0 : V) 1))
    (hclose : ∀ z, dist (f z) (g z) < 1) : ContinuousMap.Homotopy f g := by
  let v : unitInterval × X → V := fun p => realAffine p.1 (f p.2).val (g p.2).val
  have hnorm (u : sphere (0 : V) 1) : ‖u.val‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using u.property
  have hv : ∀ p, v p ≠ 0 := by
    intro p hz
    have hdist := dist_realAffine_le_add p.1 (f p.2).val (g p.2).val (f p.2).val (f p.2).val
    rw [realAffine_self, dist_self, zero_add] at hdist
    change dist (v p) (f p.2).val ≤ dist (g p.2).val (f p.2).val at hdist
    rw [hz, dist_zero_left, hnorm] at hdist
    have hc : dist (g p.2).val (f p.2).val < 1 := by
      simpa only [Subtype.dist_eq, dist_comm] using hclose p.2
    linarith
  have hvCont : Continuous v := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (f.continuous.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (g.continuous.comp continuous_snd)))
  refine
    { toFun := fun p => ⟨normalize (v p), ?_⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · simpa only [mem_sphere, dist_zero_right] using norm_normalize (hv p)
  · apply Continuous.subtype_mk
    exact (hvCont.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (hv p))).smul hvCont
  · intro z
    apply Subtype.ext
    change normalize (realAffine 0 (f z).val (g z).val) = (f z).val
    change normalize ((1 - (0 : ℝ)) • (f z).val + (0 : ℝ) • (g z).val) = _
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact normalize_eq_self_of_norm_eq_one (hnorm _)
  · intro z
    apply Subtype.ext
    change normalize (realAffine 1 (f z).val (g z).val) = (g z).val
    change normalize ((1 - (1 : ℝ)) • (f z).val + (1 : ℝ) • (g z).val) = _
    simp only [sub_self, zero_smul, one_smul, zero_add]
    exact normalize_eq_self_of_norm_eq_one (hnorm _)

variable [FiniteDimensional ℝ V]

theorem exists_lipschitz_sphere_map_homotopic
    (f : C(sphere (0 : V) 1, sphere (0 : V) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(sphere (0 : V) 1, sphere (0 : V) 1), ∃ L : ℝ≥0,
      LipschitzWith L g ∧ (∀ z, dist (g z) (f z) < ε) ∧
      Nonempty (ContinuousMap.Homotopy f g) := by
  obtain ⟨g, L, hL, hc⟩ := exists_lipschitz_sphere_approximation_on_compact
    (isCompact_sphere (0 : V) 1) f
    (lt_min hε (by norm_num : (0 : ℝ) < 1 / 2))
  let G : C(sphere (0 : V) 1, sphere (0 : V) 1) := ⟨g, hL.continuous⟩
  have hclose : ∀ z, dist (f z) (G z) < 1 := by
    intro z
    have h := (hc z).trans_le (min_le_right ε (1 / 2))
    change dist (f z) (g z) < 1
    rw [dist_comm]
    linarith
  exact ⟨G, L, hL, fun z => (hc z).trans_le (min_le_left _ _), ⟨closeSphereHomotopy f G hclose⟩⟩

end

end BanachIsometric
