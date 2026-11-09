import BanachIsometric.LocalSignedIndex
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Actual local constancy of the canonical signed index

The canonical integer is locally constant off the actual boundary image. This
is proved from its actual almost-everywhere fiber-count characterisation, not
from an axiom characterising a proposed degree function.
-/

namespace BanachIsometric

open MeasureTheory Set Filter Metric
open scoped Topology NNReal

variable {n : ℕ} [NeZero n]

theorem eventually_localSignedIndex_eq
    {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0} (hf : LipschitzWith C f)
    (a b : PiolaSpace n) (hab : a ≤ b) (c : PiolaSpace n)
    (hc : c ∉ f '' piolaBoxBoundary a b) :
    ∀ᶠ z in 𝓝 c, z ∉ f '' piolaBoxBoundary a b →
      localSignedIndex f a b z = localSignedIndex f a b c := by
  obtain ⟨r, hr, hcount⟩ := localSignedIndex_spec hf a b hab c hc
  filter_upwards [ball_mem_nhds c (half_pos hr)] with z hz
  intro hzc
  apply localSignedIndex_eq_of_ae_eq_on_ball hf a b hab z hzc (half_pos hr)
  filter_upwards [hcount] with y hy
  intro hyz
  apply hy
  apply mem_ball.mpr
  have htri := dist_triangle y z c
  have hz' := mem_ball.mp hz
  have hyz' := mem_ball.mp hyz
  linarith

theorem isLocallyConstant_localSignedIndex
    {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0} (hf : LipschitzWith C f)
    (a b : PiolaSpace n) (hab : a ≤ b) :
    IsLocallyConstant
      (fun c : ↥((f '' piolaBoxBoundary a b)ᶜ) => localSignedIndex f a b c.val) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro c
  have he := (continuous_subtype_val.continuousAt.tendsto).eventually
    (eventually_localSignedIndex_eq hf a b hab c.val c.property)
  filter_upwards [he] with z hz
  exact hz z.property

theorem localSignedIndex_eq_on_preconnected
    {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0} (hf : LipschitzWith C f)
    (a b : PiolaSpace n) (hab : a ≤ b) {U : Set (PiolaSpace n)}
    (hU : IsPreconnected U) (hsub : U ⊆ (f '' piolaBoxBoundary a b)ᶜ)
    {c d : PiolaSpace n} (hc : c ∈ U) (hd : d ∈ U) :
    localSignedIndex f a b c = localSignedIndex f a b d := by
  letI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  let inc : U → ↥((f '' piolaBoxBoundary a b)ᶜ) := fun x => ⟨x.val, hsub x.property⟩
  have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
  have hJ := (isLocallyConstant_localSignedIndex hf a b hab).comp_continuous hinc
  exact hJ.apply_eq_of_preconnectedSpace ⟨c, hc⟩ ⟨d, hd⟩

end BanachIsometric
