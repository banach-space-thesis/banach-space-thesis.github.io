import JLMS.OrdinalColumnLocality
import JLMS.OrdinalInteriorTailConstancy

/-!
# Ogden Proposition 3.4(iv): the endpoint column has a constant final tail

The matrix locality argument gives continuity everywhere below a regular
uncountable initial ordinal. The interlaced-sequence argument then gives
constancy on a final tail below the endpoint. In particular the left limit
used to define the Loy--Willis character is provided by actual matrix values.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_constant_initialOrdinalEndpointColumn_tail {c : Cardinal.{u}}
    (hc : c.IsRegular) (huncountable : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    ∃ β < c.ord, ∃ a : 𝕜, ∀ x : OrdinalInterval c.ord,
      β < x.val → x.val < c.ord → ordinalOperatorMatrix c.ord T x
        ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = a := by
  have hcf : Cardinal.aleph0 < c.ord.cof := by simpa only [hc.cof_eq] using huncountable
  let z : OrdinalInterval c.ord := ⟨c.ord, Ordinal.zero_le _, le_rfl⟩
  let f : Ordinal.{u} → 𝕜 := fun y => ordinalOperatorMatrix c.ord T
    (ordinalIntervalClamp c.ord y) z
  have hf : ContinuousOn f (Set.Iio c.ord) := by
    intro y hy
    have hval : (ordinalIntervalClamp c.ord y).val = y := min_eq_left hy.le
    have hh := continuousAt_initialOrdinalEndpointColumn hc huncountable T
      (ordinalIntervalClamp c.ord y) (by simpa only [hval] using hy)
    exact (hh.comp (ordinalIntervalClamp c.ord).continuous.continuousAt).continuousWithinAt
  obtain ⟨β, hβ, hh⟩ := exists_constant_ordinal_interior_tail hcf f hf
  have hlim : Order.IsSuccLimit c.ord := Ordinal.aleph0_le_cof.mp hcf.le
  have hξ : Order.succ β < c.ord := hlim.succ_lt hβ
  let p : OrdinalInterval c.ord := ⟨Order.succ β, Ordinal.zero_le _, hξ.le⟩
  refine ⟨β, hβ, ordinalOperatorMatrix c.ord T p z, fun x hx hxα => ?_⟩
  have h := hh x.val hx hxα (Order.succ β) (Order.lt_succ β) hξ
  change ordinalOperatorMatrix c.ord T (ordinalIntervalClamp c.ord x.val) z =
    ordinalOperatorMatrix c.ord T (ordinalIntervalClamp c.ord (Order.succ β)) z at h
  have hp : ordinalIntervalClamp c.ord (Order.succ β) = p := Subtype.ext (min_eq_left hξ.le)
  simpa only [ordinalIntervalClamp_coe, hp] using h

end JLMS
