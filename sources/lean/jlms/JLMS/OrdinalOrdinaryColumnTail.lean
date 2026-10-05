import JLMS.OrdinalAtomicMatrix
import JLMS.OrdinalHeadProjection
import JLMS.OrdinalConstantTailContinuity

/-!
# Ogden Proposition 3.4(iii): ordinary columns at the endpoint

Transfinite induction follows the paper's proof. After bounding the cutoffs
for all earlier columns, apply T to the clopen indicator of [0,ν]. Its values
are constant on a final tail. The two atomic row sums then differ in only
the ν coordinate, which forces that coordinate to be constant as well.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_ordinalOrdinaryColumn_tail {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof)
    (hsmall : ∀ ν < α, ν.card < α.cof)
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (ν : Ordinal.{u}) (hν : ν < α) :
    ∃ β < α, ∀ x : OrdinalInterval α, β < x.val →
      ordinalOperatorMatrix α T x ⟨ν, Ordinal.zero_le _, hν.le⟩ =
        ordinalOperatorMatrix α T ⟨α, Ordinal.zero_le _, le_rfl⟩
          ⟨ν, Ordinal.zero_le _, hν.le⟩ := by
  have hall : ∀ ν : Ordinal.{u}, ∀ hν : ν < α,
      ∃ β < α, ∀ x : OrdinalInterval α, β < x.val →
        ordinalOperatorMatrix α T x ⟨ν, Ordinal.zero_le _, hν.le⟩ =
          ordinalOperatorMatrix α T ⟨α, Ordinal.zero_le _, le_rfl⟩
            ⟨ν, Ordinal.zero_le _, hν.le⟩ := by
    intro ν
    induction ν using Ordinal.induction with
    | h ν ih =>
      intro hν
      have hearlier (μ : Ordinal.{u}) (hμ : μ < ν) := ih μ hμ (hμ.trans hν)
      choose b hb hcol using hearlier
      let δ := Ordinal.bsup ν b
      have hδ : δ < α := Ordinal.bsup_lt_ord (hsmall ν hν) hb
      let f : OrdinalC 𝕜 α := ordinalHeadIndicator α ν
      obtain ⟨γ, hγ, hf⟩ := exists_constant_ordinalC_tail hα (T f)
      refine ⟨max δ γ, max_lt hδ hγ, fun x hx => ?_⟩
      let κ : OrdinalInterval α := ⟨α, Ordinal.zero_le _, le_rfl⟩
      let y : OrdinalInterval α := ⟨ν, Ordinal.zero_le _, hν.le⟩
      have hs := (ordinalOperatorRow_hasSum α T f x).sub
        (ordinalOperatorRow_hasSum α T f κ)
      have hTf : T f x = T f κ := hf x ((le_max_right δ γ).trans_lt hx)
      rw [hTf, sub_self] at hs
      have hzero (z : OrdinalInterval α) (hz : z ≠ y) :
          ordinalOperatorMatrix α T x z * f z -
            ordinalOperatorMatrix α T κ z * f z = 0 := by
        by_cases hzν : z.val < ν
        · have he := hcol z.val hzν x
            ((Ordinal.le_bsup b z.val hzν).trans_lt
              ((le_max_left δ γ).trans_lt hx))
          have he' : ordinalOperatorMatrix α T x z = ordinalOperatorMatrix α T κ z := by
            convert he using 1
          rw [he', sub_self]
        · have hzgt : ¬ z.val ≤ ν := by
            intro hzle
            apply hz
            apply Subtype.ext
            exact le_antisymm hzle (le_of_not_gt hzν)
          simp only [f, ordinalHeadIndicator_apply, if_neg hzgt, mul_zero, sub_self]
      have ht : (∑' z, (ordinalOperatorMatrix α T x z * f z -
          ordinalOperatorMatrix α T κ z * f z)) =
          ordinalOperatorMatrix α T x y * f y - ordinalOperatorMatrix α T κ y * f y :=
        tsum_eq_single y hzero
      have hentry : ordinalOperatorMatrix α T x y - ordinalOperatorMatrix α T κ y = 0 := by
        have hy : f y = 1 := by simp [f, y]
        rw [hs.tsum_eq] at ht
        simpa only [hy, mul_one] using ht.symm
      exact sub_eq_zero.mp hentry
  exact hall ν hν

theorem exists_initialOrdinalOrdinaryColumn_tail {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (ν : Ordinal.{u}) (hν : ν < c.ord) :
    ∃ β < c.ord, ∀ x : OrdinalInterval c.ord, β < x.val →
      ordinalOperatorMatrix c.ord T x ⟨ν, Ordinal.zero_le _, hν.le⟩ =
        ordinalOperatorMatrix c.ord T ⟨c.ord, Ordinal.zero_le _, le_rfl⟩
          ⟨ν, Ordinal.zero_le _, hν.le⟩ := by
  apply exists_ordinalOrdinaryColumn_tail (by simpa only [hc.cof_eq] using hu)
    (fun σ hσ => ?_) T ν hν
  simpa only [hc.cof_eq] using Cardinal.lt_ord.mp hσ

theorem continuousAt_initialOrdinalOrdinaryColumn {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (ν : Ordinal.{u}) (hν : ν < c.ord) :
    ContinuousAt (fun x => ordinalOperatorMatrix c.ord T x
      ⟨ν, Ordinal.zero_le _, hν.le⟩) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := by
  obtain ⟨β, hβ, ht⟩ := exists_initialOrdinalOrdinaryColumn_tail hc hu T ν hν
  exact continuousAt_of_ordinal_constant_tail hβ _ ht

end JLMS
