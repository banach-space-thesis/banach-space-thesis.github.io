import BanachIsometric.RegularBranches
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Finiteness of actual regular fibers on a compact source

An invertible derivative at a point isolates that point in its own fiber.
This uses differentiability, without asserting a local inverse or local
injectivity. Compactness then makes a fiber finite when all its points are
regular. These are the actual hypotheses needed in the signed count argument.
-/

namespace BanachIsometric

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem eventually_ne_of_invertible_derivative {f : E → E} {x v : E}
    {D : E →L[ℝ] E} (hD : HasFDerivAt f D x) (hdet : D.det ≠ 0) :
    ∀ᶠ z in 𝓝[≠] x, f z ≠ v := by
  let e := regularLinearEquiv D hdet
  apply hD.eventually_ne
  refine ⟨‖(e.symm : E →L[ℝ] E)‖, fun z => ?_⟩
  have hb := (e.symm : E →L[ℝ] E).le_opNorm (e z)
  simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply,
    e, regularLinearEquiv_coe] using hb

theorem discrete_actual_regular_fiber {f : E → E} {s : Set E} {v : E}
    (hreg : ∀ x ∈ s, f x = v →
      DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).det ≠ 0) :
    DiscreteTopology ↥(s ∩ f ⁻¹' {v}) := by
  apply discreteTopology_subtype_iff.mpr
  rintro x ⟨hxs, hxv⟩
  obtain ⟨hdiff, hdet⟩ := hreg x hxs hxv
  apply inf_principal_eq_bot.mpr
  filter_upwards [eventually_ne_of_invertible_derivative hdiff.hasFDerivAt hdet] with z hz
  exact fun hzs => hz hzs.2

theorem finite_actual_regular_fiber {f : E → E} {s : Set E} {v : E}
    (hs : IsCompact s) (hf : ContinuousOn f s)
    (hreg : ∀ x ∈ s, f x = v →
      DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).det ≠ 0) :
    (s ∩ f ⁻¹' {v}).Finite := by
  have hc : IsCompact (s ∩ f ⁻¹' {v}) := hs.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed hs.isClosed isClosed_singleton) inter_subset_left
  exact hc.finite (discrete_actual_regular_fiber hreg)

end BanachIsometric
