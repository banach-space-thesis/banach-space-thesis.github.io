import BanachIsometric.SignedCountConvolution
import BanachIsometric.LipschitzAffineIntegral
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Local constancy of the actual signed fiber count

Target translation is an actual affine homotopy of Lipschitz maps. If the
translation centers and the bump support are smaller than the distance to the
boundary image, the proved signed-Jacobian integral identity equates the bump
convolutions of the actual count. Lebesgue differentiation then identifies the
count almost everywhere with one integer on a neighborhood.
-/

namespace BanachIsometric

open MeasureTheory Set Filter Metric
open scoped Topology NNReal

variable {n : ℕ} [NeZero n]

theorem eventually_signedCountConvolution_eq_on_ball
    {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0} (hf : LipschitzWith C f)
    (a b : PiolaSpace n) (hab : a ≤ b) (c : PiolaSpace n) {R : ℝ} (hR : 0 < R)
    (hsep : ∀ x ∈ piolaBoxBoundary a b, R ≤ dist (f x) c) :
    ∀ᶠ k in atTop, ∀ y ∈ ball c (R / 2), ∀ z ∈ ball c (R / 2),
      smoothBumpConvolution volume (shrinkingBump (PiolaSpace n) k)
          (fun w => (signedFiberCount f (fderiv ℝ f) (Icc a b) w : ℝ)) y =
        smoothBumpConvolution volume (shrinkingBump (PiolaSpace n) k)
          (fun w => (signedFiberCount f (fderiv ℝ f) (Icc a b) w : ℝ)) z := by
  have hsmall : ∀ᶠ k in atTop, (shrinkingBump (PiolaSpace n) k).rOut < R / 2 :=
    (shrinkingBump_rOut_tendsto (E := PiolaSpace n)).eventually (gt_mem_nhds (half_pos hR))
  filter_upwards [hsmall] with k hk
  intro y hy z hz
  let φ := shrinkingBump (PiolaSpace n) k
  have htrans (w : PiolaSpace n) : LipschitzWith C (fun x => f x - w) := by
    apply LipschitzWith.of_dist_le_mul
    intro x x'
    simpa only [dist_sub_right] using hf.dist_le_mul x x'
  have hboundary : ∀ x ∈ piolaBoxBoundary a b, ∀ t : unitInterval,
      (1 - (t : ℝ)) • (f x - y) + (t : ℝ) • (f x - z) ∉ tsupport (φ.normed volume) := by
    intro x hx t hmem
    rw [φ.tsupport_normed_eq] at hmem
    have hnorm : ‖(1 - (t : ℝ)) • (f x - y) + (t : ℝ) • (f x - z)‖ ≤ φ.rOut := by
      simpa only [mem_closedBall, dist_zero_right] using hmem
    have hw : (1 - (t : ℝ)) • y + (t : ℝ) • z ∈ ball c (R / 2) :=
      convex_ball c (R / 2) hy hz (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
    have he : (1 - (t : ℝ)) • (f x - y) + (t : ℝ) • (f x - z) =
        f x - ((1 - (t : ℝ)) • y + (t : ℝ) • z) := by module
    have hdistbound : dist (f x) ((1 - (t : ℝ)) • y + (t : ℝ) • z) ≤ φ.rOut := by
      rw [dist_eq_norm_sub, ← he]
      exact hnorm
    have htri := dist_triangle (f x) ((1 - (t : ℝ)) • y + (t : ℝ) • z) c
    have hdist := hsep x hx
    have hw' := mem_ball.mp hw
    change φ.rOut < R / 2 at hk
    nlinarith
  have hi := integral_signedJacobian_affine_eq_of_lipschitz
    (htrans y) (htrans z) (φ.contDiff_normed (n := 1)) a b hab hboundary
  rw [smoothBumpConvolution_signedFiberCount_eq_integral volume hf isCompact_Icc,
    smoothBumpConvolution_signedFiberCount_eq_integral volume hf isCompact_Icc]
  simpa only [fderiv_sub_const] using hi

theorem exists_signedFiberCount_ae_eq_on_ball_of_separated_boundary
    {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0} (hf : LipschitzWith C f)
    (a b : PiolaSpace n) (hab : a ≤ b) (c : PiolaSpace n) {R : ℝ} (hR : 0 < R)
    (hsep : ∀ x ∈ piolaBoxBoundary a b, R ≤ dist (f x) c) :
    ∃ D : ℤ, ∀ᵐ y, y ∈ ball c (R / 2) →
      signedFiberCount f (fderiv ℝ f) (Icc a b) y = D := by
  have hnonnull : volume (ball c (R / 2)) ≠ 0 :=
    isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr (half_pos hR))
  obtain ⟨z, _hz, heq⟩ := exists_anchor_ae_eq_of_eventually_eq_on_of_ae_tendsto volume hnonnull
    (ae_tendsto_smoothBumpConvolution_signedFiberCount volume hf isCompact_Icc)
    (eventually_signedCountConvolution_eq_on_ball hf a b hab c hR hsep)
  refine ⟨signedFiberCount f (fderiv ℝ f) (Icc a b) z, ?_⟩
  filter_upwards [heq] with y hy
  intro hymem
  exact_mod_cast hy hymem

/-- Away from the actual image of the source boundary, the actual signed
integer count is almost everywhere equal to a single integer on some ball.
No degree or density-constancy premise is used. -/
theorem exists_signedFiberCount_ae_eq_on_ball
    {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0} (hf : LipschitzWith C f)
    (a b : PiolaSpace n) (hab : a ≤ b) (c : PiolaSpace n)
    (hc : c ∉ f '' piolaBoxBoundary a b) :
    ∃ r > 0, ∃ D : ℤ, ∀ᵐ y, y ∈ ball c r →
      signedFiberCount f (fderiv ℝ f) (Icc a b) y = D := by
  have hopen : IsOpen (f '' piolaBoxBoundary a b)ᶜ :=
    ((isCompact_piolaBoxBoundary a b).image hf.continuous).isClosed.isOpen_compl
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hopen c hc
  have hsep : ∀ x ∈ piolaBoxBoundary a b, R ≤ dist (f x) c := by
    intro x hx
    apply le_of_not_gt
    intro hdist
    exact hball (mem_ball.mpr hdist) ⟨x, hx, rfl⟩
  obtain ⟨D, hD⟩ := exists_signedFiberCount_ae_eq_on_ball_of_separated_boundary
    hf a b hab c hR hsep
  exact ⟨R / 2, half_pos hR, D, hD⟩

end BanachIsometric
