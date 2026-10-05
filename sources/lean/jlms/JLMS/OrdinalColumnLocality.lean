import JLMS.OrdinalAtomicMatrix
import JLMS.OrdinalHeadProjection
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Ogden Proposition 3.4(iv): locality of the endpoint column

Below a strip of cardinality smaller than the endpoint cofinality, all rows
have one common support cutoff. Applying T to the characteristic function of
the tail beyond that cutoff recovers its endpoint column on the whole strip.
The column is therefore continuous at every point below a regular initial
ordinal. The small-cardinality condition is retained explicitly here and is
to be supplied by the initial-ordinal cardinal arithmetic.
-/

noncomputable section
namespace JLMS
open Filter Topology
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_ordinalOperator_strip_cutoff {α σ : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (hσα : σ ≤ α) (hσ : σ.card < α.cof)
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) :
    ∃ β < α, ∀ x : OrdinalInterval α, x.val < σ → ∀ y : OrdinalInterval α,
      β < y.val → y.val < α → ordinalOperatorMatrix α T x y = 0 := by
  let a (x : Ordinal.{u}) (hx : x < σ) :=
    ordinalOperatorRow α T ⟨x, Ordinal.zero_le _, hx.le.trans hσα⟩
  obtain ⟨β, hβ, hh⟩ := exists_uniform_ordinal_ellOne_cutoff hα hσ a
  exact ⟨β, hβ, fun x hx y hy hyα => hh x.val hx y hy hyα⟩

theorem exists_ordinalEndpointColumn_representative {α σ : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (hσα : σ ≤ α) (hσ : σ.card < α.cof)
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) :
    ∃ g : OrdinalC 𝕜 α, ∀ x : OrdinalInterval α, x.val < σ →
      T g x = ordinalOperatorMatrix α T x ⟨α, Ordinal.zero_le _, le_rfl⟩ := by
  classical
  obtain ⟨β, hβ, hcut⟩ := exists_ordinalOperator_strip_cutoff hα hσα hσ T
  let g : OrdinalC 𝕜 α := ContinuousMap.const _ 1 - ordinalHeadIndicator α β
  let z : OrdinalInterval α := ⟨α, Ordinal.zero_le _, le_rfl⟩
  have hg : g z = 1 := by simp [g, z, not_le_of_gt hβ]
  refine ⟨g, fun x hx => ?_⟩
  have h := (ordinalOperatorRow_hasSum α T g x).tsum_eq
  have hzero (y : OrdinalInterval α) (hy : y ≠ z) :
      ordinalOperatorMatrix α T x y * g y = 0 := by
    by_cases hyβ : y.val ≤ β
    · simp [g, hyβ]
    · have hyne : y.val ≠ α := by
        intro he
        exact hy (Subtype.ext he)
      have hyα : y.val < α := lt_iff_le_and_ne.mpr ⟨y.property.2, hyne⟩
      rw [hcut x hx y (lt_of_not_ge hyβ) hyα, zero_mul]
  rw [tsum_eq_single z hzero, hg, mul_one] at h
  exact h.symm

theorem continuousAt_ordinalEndpointColumn_below {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (hsmall : ∀ σ < α, σ.card < α.cof)
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (x : OrdinalInterval α) (hx : x.val < α) :
    ContinuousAt (fun y => ordinalOperatorMatrix α T y ⟨α, Ordinal.zero_le _, le_rfl⟩) x := by
  have hlim : Order.IsSuccLimit α := Ordinal.aleph0_le_cof.mp hα.le
  have hσ : Order.succ x.val < α := hlim.succ_lt hx
  obtain ⟨g, hg⟩ := exists_ordinalEndpointColumn_representative hα hσ.le (hsmall _ hσ) T
  apply (T g).continuous.continuousAt.congr_of_eventuallyEq
  have hU : {y : OrdinalInterval α | y.val < Order.succ x.val} ∈ 𝓝 x := by
    have ho : IsOpen {y : OrdinalInterval α | y.val < Order.succ x.val} :=
      isOpen_Iio.preimage (continuous_subtype_val :
        Continuous (Subtype.val : OrdinalInterval α → Ordinal.{u}))
    exact ho.mem_nhds (Order.lt_succ x.val)
  filter_upwards [hU] with y hy
  exact (hg y hy).symm

theorem continuousAt_initialOrdinalEndpointColumn {c : Cardinal.{u}}
    (hc : c.IsRegular) (huncountable : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (x : OrdinalInterval c.ord) (hx : x.val < c.ord) :
    ContinuousAt (fun y => ordinalOperatorMatrix c.ord T y
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩) x := by
  apply continuousAt_ordinalEndpointColumn_below (T := T) (x := x) (hx := hx)
  · simpa only [hc.cof_eq] using huncountable
  · intro σ hσ
    rw [hc.cof_eq]
    exact Cardinal.lt_ord.mp hσ

end JLMS
