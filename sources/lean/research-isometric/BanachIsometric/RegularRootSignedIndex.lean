import BanachIsometric.RegularRootLinearization
import BanachIsometric.AffineSignedIndex
import BanachIsometric.SignedIndexHomotopy

/-!
# The actual local signed index at an ordinary regular root

Ordinary differentiability with invertible derivative isolates the root and
provides a boundary-avoiding homotopy on every sufficiently small coordinate
cube. The proved analytic homotopy theorem and actual affine unique-fiber
normalization identify the index with the derivative sign. Local injectivity
and a local inverse of the original function are never assumed or asserted.
-/

namespace BanachIsometric

open Set Metric
open scoped Topology NNReal

variable {n : ℕ}

theorem centeredCube_lower_le_upper (x : PiolaSpace n) {s : ℝ} (hs : 0 ≤ s) :
    x - s • (1 : PiolaSpace n) ≤ x + s • (1 : PiolaSpace n) := by
  intro i
  change x i - s * 1 ≤ x i + s * 1
  nlinarith

theorem mem_centeredCube_of_norm_sub_le (x z : PiolaSpace n) {s : ℝ} (hz : ‖z - x‖ ≤ s) :
    z ∈ Icc (x - s • (1 : PiolaSpace n)) (x + s • (1 : PiolaSpace n)) := by
  have hcoord (i : Fin n) : |z i - x i| ≤ s := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (f := z - x) i).trans hz
  constructor
  · intro i
    change x i - s * 1 ≤ z i
    have h := (abs_le.mp (hcoord i)).1
    nlinarith
  · intro i
    change z i ≤ x i + s * 1
    have h := (abs_le.mp (hcoord i)).2
    nlinarith

theorem norm_sub_le_of_mem_centeredCube (x z : PiolaSpace n) {s : ℝ} (hs : 0 ≤ s)
    (hz : z ∈ Icc (x - s • (1 : PiolaSpace n)) (x + s • (1 : PiolaSpace n))) : ‖z - x‖ ≤ s := by
  apply (pi_norm_le_iff_of_nonneg hs).mpr
  intro i
  change ‖z i - x i‖ ≤ s
  rw [Real.norm_eq_abs]
  have hlo := hz.1 i
  have hhi := hz.2 i
  change x i - s * 1 ≤ z i at hlo
  change z i ≤ x i + s * 1 at hhi
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem center_mem_interior_centeredCube (x : PiolaSpace n) {s : ℝ} (hs : 0 < s) :
    x ∈ interior (Icc (x - s • (1 : PiolaSpace n)) (x + s • (1 : PiolaSpace n))) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (ball_mem_nhds x hs)
  intro z hz
  apply mem_centeredCube_of_norm_sub_le
  exact (by simpa only [mem_ball, dist_eq_norm] using hz : ‖z - x‖ < s).le

theorem exists_regular_root_cube_signed_index [NeZero n]
    {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0} (hf : LipschitzWith C f)
    {x : PiolaSpace n} {D : PiolaSpace n →L[ℝ] PiolaSpace n}
    (hD : HasFDerivAt f D x) (hdet : D.det ≠ 0) :
    ∃ r > 0, ∀ s : ℝ, 0 < s → s ≤ r →
      localSignedIndex f (x - s • (1 : PiolaSpace n)) (x + s • (1 : PiolaSpace n)) (f x) =
        (SignType.sign D.det : ℤ) := by
  let L := regularLinearEquiv D hdet
  have hfL : HasFDerivAt f (L : PiolaSpace n →L[ℝ] PiolaSpace n) x := by
    simpa only [L, regularLinearEquiv_coe] using hD
  obtain ⟨δ, hδ, havoid⟩ := exists_affine_linearization_avoids_root L hfL
  refine ⟨δ / 2, half_pos hδ, fun s hs hsmall => ?_⟩
  let a := x - s • (1 : PiolaSpace n)
  let b := x + s • (1 : PiolaSpace n)
  have hab : a ≤ b := centeredCube_lower_le_upper x hs.le
  have hxint : x ∈ interior (Icc a b) := center_mem_interior_centeredCube x hs
  let g := affineLinearization L x (f x)
  have hg : LipschitzWith _ g := (LipschitzWith.const (f x)).add
    (L.lipschitz.comp ((LipschitzWith.id).sub (LipschitzWith.const x)))
  let H : unitInterval → PiolaSpace n → PiolaSpace n := fun t z => realAffine t (f z) (g z)
  have hLip : ∀ t, ∃ K : ℝ≥0, LipschitzWith K (H t) := by
    intro t
    let A : PiolaSpace n →L[ℝ] PiolaSpace n := (1 - (t : ℝ)) • ContinuousLinearMap.id ℝ _
    let B : PiolaSpace n →L[ℝ] PiolaSpace n := (t : ℝ) • ContinuousLinearMap.id ℝ _
    exact ⟨_, (A.lipschitz.comp hf).add (B.lipschitz.comp hg)⟩
  have hH : Continuous (fun z : unitInterval × piolaBoxBoundary a b => H z.1 z.2) := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (hf.continuous.comp (continuous_subtype_val.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (hg.continuous.comp (continuous_subtype_val.comp continuous_snd)))
  have hboundary : ∀ t, f x ∉ H t '' piolaBoxBoundary a b := by
    rintro t ⟨z, hz, hzc⟩
    have hzx : z ≠ x := by
      intro heq
      subst z
      rw [piolaBoxBoundary_eq_frontier] at hz
      exact hz.2 hxint
    have hnorm : dist z x < δ := by
      rw [dist_eq_norm]
      exact (norm_sub_le_of_mem_centeredCube x z hs.le hz.1).trans_lt (by linarith)
    exact havoid z hnorm hzx t hzc
  have hindex := localSignedIndex_homotopy_eq_of_lipschitz H hLip a b hab hH (f x)
    hboundary (0 : unitInterval) 1
  have h0 : H 0 = f := by
    funext z
    change (1 - (0 : ℝ)) • f z + (0 : ℝ) • g z = f z
    simp only [sub_zero, one_smul, zero_smul, add_zero]
  have h1 : H 1 = g := by
    funext z
    change (1 - (1 : ℝ)) • f z + (1 : ℝ) • g z = g z
    simp only [sub_self, zero_smul, one_smul, zero_add]
  rw [h0, h1] at hindex
  have hsign := localSignedIndex_affineLinearization L x (f x) a b hab hxint
  simpa only [L, regularLinearEquiv_coe] using hindex.trans hsign

end BanachIsometric
