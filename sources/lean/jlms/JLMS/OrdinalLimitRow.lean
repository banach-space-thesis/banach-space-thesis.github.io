import JLMS.OrdinalAtomicMatrix
import JLMS.OrdinalHeadProjection
import Mathlib.Topology.Order.IsLUB

/-!
# Ogden Lemma 4.8: a row at a limit between diagonal blocks vanishes

The argument is isolated from the construction of the block map. Below a
limit cutoff, rows have support below the cutoff. At the cutoff, the row has
no support below it. If the preceding row sums vanish, continuity forces
the cutoff row to annihilate every head indicator; transfinite induction
then forces every entry of that row to vanish.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem ordinalC_eq_zero_at_limit {α δ : Ordinal.{u}} (hδα : δ ≤ α)
    (hδ : Order.IsSuccLimit δ) (f : OrdinalC 𝕜 α)
    (hf : ∀ x : OrdinalInterval α, x.val < δ → f x = 0) :
    f ⟨δ, Ordinal.zero_le _, hδα⟩ = 0 := by
  let g : C(Ordinal.{u}, 𝕜) := f.comp (ordinalIntervalClamp α)
  have hs : Set.Iio δ ⊆ {x | g x = 0} := by
    intro x hx
    let y : OrdinalInterval α := ⟨x, Ordinal.zero_le _, hx.le.trans hδα⟩
    have he : ordinalIntervalClamp α x = y := by
      apply Subtype.ext
      exact min_eq_left (hx.le.trans hδα)
    change f (ordinalIntervalClamp α x) = 0
    rw [he]
    exact hf y hx
  have hd : δ ∈ closure (Set.Iio δ) := hδ.isLUB_Iio.mem_closure hδ.nonempty_Iio
  have hz : g δ = 0 := closure_minimal hs (isClosed_eq g.continuous continuous_const) hd
  let y : OrdinalInterval α := ⟨δ, Ordinal.zero_le _, hδα⟩
  have he : ordinalIntervalClamp α δ = y := by
    apply Subtype.ext
    exact min_eq_left hδα
  change f (ordinalIntervalClamp α δ) = 0 at hz
  rwa [he] at hz

theorem ordinalC_eq_zero_at_limit_of_tail {α β δ : Ordinal.{u}} (hδα : δ ≤ α)
    (hδ : Order.IsSuccLimit δ) (hβδ : β < δ) (f : OrdinalC 𝕜 α)
    (hf : ∀ x : OrdinalInterval α, β < x.val → x.val < δ → f x = 0) :
    f ⟨δ, Ordinal.zero_le _, hδα⟩ = 0 := by
  have h := ordinalC_eq_zero_at_limit hδα hδ (f - ordinalHeadProjection α β f)
    (fun x hx => by
      by_cases hβ : x.val ≤ β
      · simp [hβ]
      · simp [hβ, hf x (lt_of_not_ge hβ) hx])
  simpa [not_le_of_gt hβδ] using h

theorem ordinalOperatorRow_eq_zero_of_headIndicators {α : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (x : OrdinalInterval α)
    (hT : ∀ γ ≤ α, T (ordinalHeadIndicator α γ) x = 0) : ordinalOperatorRow α T x = 0 := by
  have hall : ∀ γ : Ordinal.{u}, ∀ hγ : γ ≤ α,
      ordinalOperatorMatrix α T x ⟨γ, Ordinal.zero_le _, hγ⟩ = 0 := by
    intro γ
    induction γ using Ordinal.induction with
    | h γ ih =>
      intro hγ
      let y : OrdinalInterval α := ⟨γ, Ordinal.zero_le _, hγ⟩
      have hs := (ordinalOperatorRow_hasSum α T (ordinalHeadIndicator α γ) x).tsum_eq
      have hzero (z : OrdinalInterval α) (hz : z ≠ y) :
          ordinalOperatorMatrix α T x z * ordinalHeadIndicator (𝕜 := 𝕜) α γ z = 0 := by
        by_cases hzγ : z.val ≤ γ
        · have hlt : z.val < γ := lt_of_le_of_ne hzγ (fun he => hz (Subtype.ext he))
          rw [ih z.val hlt z.property.2, zero_mul]
        · simp only [ordinalHeadIndicator_apply, if_neg hzγ, mul_zero]
      rw [tsum_eq_single y hzero, hT γ hγ] at hs
      simpa [y] using hs
  ext y
  exact hall y.val y.property.2

theorem ordinalOperatorRow_eq_zero_of_separated_limit_tail {α β δ : Ordinal.{u}}
    (hδα : δ ≤ α) (hδ : Order.IsSuccLimit δ) (hβδ : β < δ)
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (hlower : ∀ x z : OrdinalInterval α, β < x.val → x.val < δ → δ ≤ z.val →
      ordinalOperatorMatrix α T x z = 0)
    (hupper : ∀ z : OrdinalInterval α, z.val < δ →
      ordinalOperatorMatrix α T ⟨δ, Ordinal.zero_le _, hδα⟩ z = 0)
    (hsums : ∀ x : OrdinalInterval α, β < x.val → x.val < δ → T (ContinuousMap.const _ 1) x = 0) :
    ordinalOperatorRow α T ⟨δ, Ordinal.zero_le _, hδα⟩ = 0 := by
  apply ordinalOperatorRow_eq_zero_of_headIndicators T
  intro γ _
  by_cases hγ : γ < δ
  · have hs := (ordinalOperatorRow_hasSum α T (ordinalHeadIndicator α γ)
      ⟨δ, Ordinal.zero_le _, hδα⟩).tsum_eq
    have hz (z : OrdinalInterval α) :
        ordinalOperatorMatrix α T ⟨δ, Ordinal.zero_le _, hδα⟩ z *
          ordinalHeadIndicator (𝕜 := 𝕜) α γ z = 0 := by
      by_cases hzγ : z.val ≤ γ
      · rw [hupper z (hzγ.trans_lt hγ), zero_mul]
      · simp only [ordinalHeadIndicator_apply, if_neg hzγ, mul_zero]
    simpa only [hz, tsum_zero] using hs.symm
  · apply ordinalC_eq_zero_at_limit_of_tail hδα hδ hβδ
    intro x hβx hx
    have hhead := (ordinalOperatorRow_hasSum α T (ordinalHeadIndicator α γ) x).tsum_eq
    have hone := (ordinalOperatorRow_hasSum α T (ContinuousMap.const _ 1) x).tsum_eq
    have he : (fun z => ordinalOperatorMatrix α T x z * ordinalHeadIndicator (𝕜 := 𝕜) α γ z) =
        (fun z => ordinalOperatorMatrix α T x z * (ContinuousMap.const _ (1 : 𝕜)) z) := by
      funext z
      by_cases hz : z.val < δ
      · simp only [ordinalHeadIndicator_apply, if_pos (hz.le.trans (le_of_not_gt hγ)),
          ContinuousMap.const_apply]
      · rw [hlower x z hβx hx (le_of_not_gt hz), zero_mul, zero_mul]
    rw [he, hone, hsums x hβx hx] at hhead
    exact hhead.symm

theorem ordinalOperatorRow_eq_zero_of_separated_limit {α δ : Ordinal.{u}}
    (hδα : δ ≤ α) (hδ : Order.IsSuccLimit δ)
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (hlower : ∀ x z : OrdinalInterval α, x.val < δ → δ ≤ z.val →
      ordinalOperatorMatrix α T x z = 0)
    (hupper : ∀ z : OrdinalInterval α, z.val < δ →
      ordinalOperatorMatrix α T ⟨δ, Ordinal.zero_le _, hδα⟩ z = 0)
    (hsums : ∀ x : OrdinalInterval α, x.val < δ → T (ContinuousMap.const _ 1) x = 0) :
    ordinalOperatorRow α T ⟨δ, Ordinal.zero_le _, hδα⟩ = 0 := by
  obtain ⟨β, hβ⟩ := hδ.nonempty_Iio
  exact ordinalOperatorRow_eq_zero_of_separated_limit_tail hδα hδ hβ T
    (fun x z _ hx hz => hlower x z hx hz) hupper (fun x _ hx => hsums x hx)

end JLMS
