import BanachIsometric.LipschitzRegularValues
import BanachIsometric.SignedFiberCount
import BanachIsometric.SignedCompactIntegral
import BanachIsometric.RegularFiberFiniteness

/-!
# Signed integer fiber-count formula for compact Lipschitz sources

The actual full fibers are regular almost everywhere by Rademacher, Lusin (N),
and equal-dimensional Sard. Their finiteness follows from compactness and
isolation at each actual invertible derivative. Thus the intrinsic regular
multiplicity agrees almost everywhere with the ordinary integer sign count of
the entire fiber. No fiber-finiteness, branch, degree, or integrability premise
remains in the final signed integral identity.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ae_signedRegularMultiplicity_eq_signedFiberCount_of_compact_lipschitz
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : Set E} (hs : IsCompact s) :
    ∀ᵐ y ∂μ, signedRegularMultiplicity f s y =
      (signedFiberCount f (fderiv ℝ f) s y : ℝ) := by
  filter_upwards [lipschitzWith_ae_every_preimage_regular μ hf] with y hy
  have hfin : {x : E | x ∈ s ∧ f x = y}.Finite := by
    have hh := finite_actual_regular_fiber hs hf.continuous.continuousOn
      (fun x _hx hxy => hy x hxy)
    simpa only [Set.inter_def, Set.mem_preimage, Set.mem_singleton_iff] using hh
  calc
    signedRegularMultiplicity f s y = signedFiberSum f (fderiv ℝ f) s y :=
      signedFiberSum_inter_eq_of_fiber_subset f (fderiv ℝ f) s
        (differentiableRegularSet f) y (fun x _hx hxy => hy x hxy)
    _ = (signedFiberCount f (fderiv ℝ f) s y : ℝ) :=
      signedFiberSum_eq_coe_signedFiberCount f (fderiv ℝ f) s y hfin

variable [Nontrivial E]

/-- Genuine signed multiplicity/area identity for a Lipschitz map, a compact
source, and a continuous weight. The integer density is the actual finite
signed count of all preimages almost everywhere. Its identification with a
homotopy-invariant topological degree is a separate remaining theorem. -/
theorem integral_signedFiberCount_of_compact_lipschitz
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : Set E} (hs : IsCompact s)
    {g : E → ℝ} (hg : Continuous g) :
    (∫ y, (signedFiberCount f (fderiv ℝ f) s y : ℝ) * g y ∂μ) =
      ∫ x in s, (fderiv ℝ f x).det * g (f x) ∂μ := by
  calc
    (∫ y, (signedFiberCount f (fderiv ℝ f) s y : ℝ) * g y ∂μ) =
        ∫ y, signedRegularMultiplicity f s y * g y ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_signedRegularMultiplicity_eq_signedFiberCount_of_compact_lipschitz μ hf hs]
        with y hy
      rw [hy]
    _ = ∫ x in s, (fderiv ℝ f x).det * g (f x) ∂μ :=
      integral_signedRegularMultiplicity_of_compact_lipschitz μ hf hs hg

end BanachIsometric
