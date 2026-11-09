import BanachIsometric.SignedCountConnectedConstancy
import BanachIsometric.LocalSignedIndex
import BanachIsometric.AEConstantUniqueness

/-!
# The actual fiber density on a connected target interior

The actual signed count is constant almost everywhere on a preconnected
region avoiding the boundary image. A nonnull overlap with the canonical
index neighborhood identifies that constant with the actual local index.
-/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped NNReal

theorem ae_signedFiberCount_eq_localSignedIndex_on_preconnected
    {n : ℕ} [NeZero n] {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0}
    (hf : LipschitzWith C f) (a b : PiolaSpace n) (hab : a ≤ b)
    {U : Set (PiolaSpace n)} (hUopen : IsOpen U) (hU : IsPreconnected U)
    (havoid : Disjoint U (f '' piolaBoxBoundary a b))
    {c : PiolaSpace n} (hc : c ∈ U) :
    ∀ᵐ y, y ∈ U → signedFiberCount f (fderiv ℝ f) (Icc a b) y = localSignedIndex f a b c := by
  obtain ⟨D, hD⟩ := exists_signedFiberCount_ae_eq_on_preconnected hf a b hab hU havoid
  have hcavoid : c ∉ f '' piolaBoxBoundary a b :=
    fun hmem => Set.disjoint_left.mp havoid hc hmem
  obtain ⟨r, hr, hlocal⟩ := localSignedIndex_spec hf a b hab c hcavoid
  have hnonnull : volume (U ∩ ball c r) ≠ 0 :=
    (hUopen.inter isOpen_ball).measure_ne_zero volume ⟨c, hc, mem_ball_self hr⟩
  have hconstant : D = localSignedIndex f a b c :=
    ae_constants_eq_of_nonnull_inter volume hnonnull hD hlocal
  simpa only [hconstant] using hD

end BanachIsometric
