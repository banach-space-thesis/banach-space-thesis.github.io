import BanachIsometric.DiskCubeHomeomorphism
import BanachIsometric.RadialHomeomorphismLipschitz

/-! Both directions of the actual cube–Euclidean-disk homeomorphism are
globally Lipschitz in their existing metrics. The coordinate sup norm remains
an auxiliary gauge, not an ambient Euclidean norm replacement. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped NNReal unitInterval

theorem lipschitz_coordinateSupGauge (n : ℕ) :
    LipschitzWith ‖(euclideanCoordinates n).toContinuousLinearMap‖₊ (coordinateSupGauge n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (dist_norm_norm_le _ _).trans ((euclideanCoordinates n).lipschitz.dist_le_mul x y)

theorem lipschitz_centeredCube (n : ℕ) : LipschitzWith 2 (centeredCube n) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change |2 * (u i : ℝ) - 1 - (2 * (v i : ℝ) - 1)| ≤ 2 * dist u v
  have hi : |(u i : ℝ) - (v i : ℝ)| ≤ dist u v := by
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq] using (LipschitzWith.eval i).dist_le_mul u v
  rw [show 2 * (u i : ℝ) - 1 - (2 * (v i : ℝ) - 1) =
    2 * ((u i : ℝ) - (v i : ℝ)) by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left hi (by norm_num)

theorem exists_lipschitz_cubeDiskHomeomorph (n : ℕ) :
    ∃ L : ℝ≥0, LipschitzWith L (cubeDiskHomeomorph n) := by
  obtain ⟨R, hR⟩ := exists_lipschitz_radialGaugeMapInv (coordinateSupGauge_homogeneous n)
    (lipschitz_coordinateSupGauge n).lipschitzOnWith
  have h := hR.comp ((euclideanCoordinates n).symm.lipschitz.comp (lipschitz_centeredCube n))
  refine ⟨R * (‖(euclideanCoordinates n).symm.toContinuousLinearMap‖₊ * 2), ?_⟩
  exact h.subtype_mk (fun x => (cubeDiskHomeomorph n x).property)

theorem exists_lipschitz_cubeDiskHomeomorph_symm (n : ℕ) :
    ∃ L : ℝ≥0, LipschitzWith L (cubeDiskHomeomorph n).symm := by
  obtain ⟨R, hR⟩ := exists_lipschitz_radialGaugeMap (coordinateSupGauge_homogeneous n)
    (lipschitz_coordinateSupGauge n).lipschitzOnWith
  let w : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 → (Fin n → ℝ) :=
    fun x => euclideanCoordinates n (radialGaugeMap (coordinateSupGauge n) x.val)
  let L := ‖(euclideanCoordinates n).toContinuousLinearMap‖₊ * (R * 1)
  have hw : LipschitzWith L w :=
    (euclideanCoordinates n).lipschitz.comp (hR.comp (LipschitzWith.subtype_val _))
  refine ⟨L, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  apply (dist_pi_le_iff (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
  intro i
  change |(w x i + 1) / 2 - (w y i + 1) / 2| ≤ (L : ℝ) * dist x y
  have he : (w x i + 1) / 2 - (w y i + 1) / 2 = (w x i - w y i) / 2 := by ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    |w x i - w y i| / 2 ≤ |w x i - w y i| := by linarith [abs_nonneg (w x i - w y i)]
    _ ≤ ‖w x - w y‖ := by simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (w x - w y) i
    _ ≤ (L : ℝ) * dist x y := by simpa only [dist_eq_norm] using hw.dist_le_mul x y

end BanachIsometric
