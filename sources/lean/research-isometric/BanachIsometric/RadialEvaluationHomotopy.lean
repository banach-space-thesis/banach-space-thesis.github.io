import BanachIsometric.LipschitzNormalization
import BanachIsometric.MollifiedBoundary

/-!
# The actual evaluation-to-direction deformation

The evaluated boundary vector and its normalisation are positive multiples of
one another. Their affine interpolation never vanishes and has Lipschitz
slices. Taking cones therefore compares their actual local signed indices
without invoking a radial homeomorphism composition theorem.
-/

namespace BanachIsometric

open NormedSpace
open scoped Topology NNReal

namespace ExactTangentialFamily

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {g : V → ℝ} {p : E → ℝ} (A : ExactTangentialFamily E V g p)

def evaluationMap (y : E) : C(Metric.sphere (0 : V) 1, V) :=
  ⟨fun z => A.maps z y, A.continuous_evaluation y⟩

noncomputable def directionAmbient (hg0 : g 0 = 0) {y : E} (hy : 0 < p y) :
    C(Metric.sphere (0 : V) 1, V) :=
  ⟨fun z => ((A.direction hg0 hy) z).val, continuous_subtype_val.comp (A.direction hg0 hy).continuous⟩

noncomputable def radialDirectionHomotopy (hg0 : g 0 = 0) {y : E} (hy : 0 < p y) :
    ContinuousMap.Homotopy (A.evaluationMap y) (A.directionAmbient hg0 hy) where
  toFun z := realAffine z.1 (A.maps z.2 y) ((A.direction hg0 hy) z.2).val
  continuous_toFun :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      ((A.continuous_evaluation y).comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((A.directionAmbient hg0 hy).continuous.comp continuous_snd))
  map_zero_left z := by simp [realAffine, evaluationMap]
  map_one_left z := by simp [realAffine, directionAmbient]

theorem radialDirectionHomotopy_ne_zero (hg0 : g 0 = 0) {y : E} (hy : 0 < p y)
    (t : unitInterval) (z : Metric.sphere (0 : V) 1) :
    A.radialDirectionHomotopy hg0 hy (t, z) ≠ 0 := by
  have hv := A.evaluation_ne_zero hg0 hy z
  have hn : 0 < ‖A.maps z y‖ := norm_pos_iff.mpr hv
  have hc : 0 < (1 - (t : ℝ)) + (t : ℝ) * ‖A.maps z y‖⁻¹ := by
    by_cases ht : (t : ℝ) = 0
    · simp [ht]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.property.2)
        (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) (inv_pos.mpr hn))
  change (1 - (t : ℝ)) • A.maps z y + (t : ℝ) • (‖A.maps z y‖⁻¹ • A.maps z y) ≠ 0
  rw [smul_smul, ← add_smul]
  exact smul_ne_zero hc.ne' hv

theorem radialDirectionHomotopy_slices_lipschitz [FiniteDimensional ℝ V]
    (hg0 : g 0 = 0) {y : E} (hy : 0 < p y) :
    ∀ t : unitInterval, ∃ L : ℝ≥0,
      LipschitzWith L (fun z => A.radialDirectionHomotopy hg0 hy (t, z)) := by
  obtain ⟨C, hC⟩ := A.maps_lipschitz
  obtain ⟨K, hK⟩ := A.exists_lipschitz_direction hg0 hy
  let L₀ : ℝ≥0 := ‖ContinuousLinearMap.apply ℝ V y‖₊ * C
  have hL₀ : LipschitzWith L₀ (fun z => A.maps z y) :=
    (ContinuousLinearMap.apply ℝ V y).lipschitz.comp hC
  intro t
  refine ⟨L₀ + K, LipschitzWith.of_dist_le_mul (fun u v => ?_)⟩
  calc
    dist (A.radialDirectionHomotopy hg0 hy (t, u)) (A.radialDirectionHomotopy hg0 hy (t, v)) ≤
        dist (A.maps u y) (A.maps v y) +
          dist ((A.direction hg0 hy) u).val ((A.direction hg0 hy) v).val :=
      dist_realAffine_le_add t _ _ _ _
    _ ≤ (L₀ : ℝ) * dist u v + (K : ℝ) * dist u v :=
      add_le_add (hL₀.dist_le_mul u v)
        (by simpa only [Subtype.dist_eq] using hK.dist_le_mul u v)
    _ = ((L₀ + K : ℝ≥0) : ℝ) * dist u v := by push_cast; ring

end ExactTangentialFamily

end BanachIsometric
