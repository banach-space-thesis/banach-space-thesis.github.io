import BanachIsometric.LipschitzAffineIntegral
import BanachIsometric.BoundaryHomotopyStability
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Actual signed integral invariance along Lipschitz slices

Only joint continuity on the compact boundary is required in the parameter.
Each slice is a genuine globally Lipschitz map; no common parameter-Lipschitz
constant is assumed. Compact boundary separation reduces nearby slices to the
proved affine invariance theorem, making the actual integral locally constant.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal

theorem integral_signedJacobian_homotopy_eq_of_lipschitz
    {P : Type*} [PseudoMetricSpace P] [CompactSpace P] [PreconnectedSpace P]
    {n : ℕ} (H : P → PiolaSpace n → PiolaSpace n)
    (hLip : ∀ p, ∃ C : ℝ≥0, LipschitzWith C (H p))
    (a b : PiolaSpace n) (hab : a ≤ b)
    (hH : Continuous (fun z : P × piolaBoxBoundary a b => H z.1 z.2))
    {ψ : PiolaSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hboundary : ∀ p, ∀ x ∈ piolaBoxBoundary a b, H p x ∉ tsupport ψ)
    (p q : P) :
    (∫ x in Icc a b, (fderiv ℝ (H p) x).det * ψ (H p x)) =
      ∫ x in Icc a b, (fderiv ℝ (H q) x).det * ψ (H q x) := by
  let J : P → ℝ := fun p => ∫ x in Icc a b, (fderiv ℝ (H p) x).det * ψ (H p x)
  have hJ : IsLocallyConstant J := by
    apply (IsLocallyConstant.iff_eventually_eq J).mpr
    intro p
    have he := eventually_affine_boundary_avoids_closed H
      (isCompact_piolaBoxBoundary a b) hH (isClosed_tsupport ψ) p (hboundary p)
    filter_upwards [he] with q hq
    obtain ⟨Cp, hCp⟩ := hLip p
    obtain ⟨Cq, hCq⟩ := hLip q
    exact integral_signedJacobian_affine_eq_of_lipschitz hCq hCp hψ a b hab hq
  exact hJ.apply_eq_of_preconnectedSpace p q

end BanachIsometric
