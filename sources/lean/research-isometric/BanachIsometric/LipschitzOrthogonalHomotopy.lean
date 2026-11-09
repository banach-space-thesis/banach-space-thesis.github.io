import BanachIsometric.LipschitzNormalization
import BanachIsometric.MollifiedBoundary

/-!
# Actual Lipschitz slices of the orthogonal sphere homotopy

The affine combination of orthogonal unit vectors has norm at least one half.
The proved quantitative normalisation estimate therefore makes every slice
of the actual normalised-affine sphere homotopy Lipschitz. This supplies the
analytic index homotopy hypotheses from the original exact family.
-/

namespace BanachIsometric

open NormedSpace
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem norm_orthogonal_unit_affine_lower {x y : V}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0) (t : unitInterval) :
    (1 / 2 : ℝ) ≤ ‖realAffine t x y‖ := by
  have hxx : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyy : inner ℝ y y = 1 := by rw [real_inner_self_eq_norm_sq, hy]; norm_num
  have hyx : inner ℝ y x = 0 := by
    calc
      inner ℝ y x = inner ℝ x y := real_inner_comm _ _
      _ = 0 := hxy
  have hn : ‖realAffine t x y‖ ^ 2 = (1 - (t : ℝ)) ^ 2 + (t : ℝ) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [realAffine, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hxx, hyy, hxy, hyx, mul_one, mul_zero, add_zero, zero_add]
    ring
  nlinarith [norm_nonneg (realAffine t x y), sq_nonneg ((t : ℝ) - 1 / 2)]

variable {X : Type*} [PseudoMetricSpace X]

theorem exists_lipschitz_orthogonalSphereHomotopy_slices
    (f g : C(X, Metric.sphere (0 : V) 1))
    (hfg : ∀ z, inner ℝ (f z).val (g z).val = 0)
    {Cf Cg : ℝ≥0} (hf : LipschitzWith Cf f) (hg : LipschitzWith Cg g) :
    ∀ t : unitInterval, ∃ L : ℝ≥0,
      LipschitzWith L (fun z => orthogonalSphereHomotopy f g hfg (t, z)) := by
  intro t
  let v : X → V := fun z => realAffine t (f z).val (g z).val
  have hv : LipschitzWith (Cf + Cg) v := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (v x) (v y) ≤ dist (f x).val (f y).val + dist (g x).val (g y).val :=
        dist_realAffine_le_add t _ _ _ _
      _ ≤ (Cf : ℝ) * dist x y + (Cg : ℝ) * dist x y :=
        add_le_add (by simpa only [Subtype.dist_eq] using hf.dist_le_mul x y)
          (by simpa only [Subtype.dist_eq] using hg.dist_le_mul x y)
      _ = ((Cf + Cg : ℝ≥0) : ℝ) * dist x y := by push_cast; ring
  have hlo : ∀ z, (1 / 2 : ℝ) ≤ ‖v z‖ := by
    intro z
    apply norm_orthogonal_unit_affine_lower
    · simpa only [Metric.mem_sphere, dist_zero_right] using (f z).property
    · simpa only [Metric.mem_sphere, dist_zero_right] using (g z).property
    · exact hfg z
  have hnorm := lipschitzWith_normalize_of_lower_bound hv
    (by norm_num : (0 : ℝ≥0) < 1 / 2) hlo
  refine ⟨2 * (Cf + Cg) / (1 / 2), LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  simpa only [Subtype.dist_eq] using hnorm.dist_le_mul x y

end BanachIsometric
