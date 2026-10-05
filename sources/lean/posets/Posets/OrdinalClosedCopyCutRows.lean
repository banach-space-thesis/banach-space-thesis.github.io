import JLMS.OrdinalMatrixBlocks
import JLMS.OrdinalLimitRow

/-! A limit matrix cut has no ordinary atomic row entries above the cut.
Thus, on functions with zero initial head and endpoint, that row acts by
its actual diagonal coefficient.  This uses continuity of T applied to
head indicators, not continuity of individual atomic columns. -/

noncomputable section
namespace Posets
open JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem ordinalMatrixCut_headDifference_zero {α τ δ γ : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (hcut : IsOrdinalMatrixCut T τ δ) (hτδ : τ < δ)
    (hδ : Order.IsSuccLimit δ) (hδγ : δ ≤ γ) (hγα : γ < α) :
    T (ordinalHeadIndicator α γ - ordinalHeadIndicator α δ)
      ⟨δ, Ordinal.zero_le _, hδγ.trans hγα.le⟩ = 0 := by
  apply ordinalC_eq_zero_at_limit_of_tail (hδγ.trans hγα.le) hδ hτδ
  intro x hτx hxδ
  have hsum := (ordinalOperatorRow_hasSum α T
    (ordinalHeadIndicator α γ - ordinalHeadIndicator α δ) x).tsum_eq
  have hz (y : OrdinalInterval α) : ordinalOperatorMatrix α T x y *
      (ordinalHeadIndicator (𝕜 := 𝕜) α γ - ordinalHeadIndicator (𝕜 := 𝕜) α δ) y = 0 := by
    by_cases hyδ : y.val < δ
    · simp only [ContinuousMap.sub_apply, ordinalHeadIndicator_apply,
        if_pos hyδ.le, if_pos (hyδ.le.trans hδγ), sub_self, mul_zero]
    · by_cases hyα : y.val < α
      · rw [(hcut.2 x y hτx.le hxδ (le_of_not_gt hyδ) hyα).1, zero_mul]
      · have he : y.val = α := le_antisymm y.property.2 (le_of_not_gt hyα)
        simp only [ContinuousMap.sub_apply, ordinalHeadIndicator_apply, he,
          if_neg (not_le_of_gt hγα), if_neg (not_le_of_gt (hδγ.trans_lt hγα)),
          sub_self, mul_zero]
  simpa only [hz, tsum_zero] using hsum.symm

theorem ordinalMatrixCut_limitRow_above_zero {α τ δ : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (hcut : IsOrdinalMatrixCut T τ δ) (hτδ : τ < δ)
    (hδ : Order.IsSuccLimit δ) (hδα : δ < α) :
    ∀ y : OrdinalInterval α, δ < y.val → y.val < α →
      ordinalOperatorMatrix α T ⟨δ, Ordinal.zero_le _, hδα.le⟩ y = 0 := by
  have hall : ∀ γ : Ordinal.{u}, δ < γ → ∀ hγ : γ < α,
      ordinalOperatorMatrix α T ⟨δ, Ordinal.zero_le _, hδα.le⟩
        ⟨γ, Ordinal.zero_le _, hγ.le⟩ = 0 := by
    intro γ
    induction γ using Ordinal.induction with
    | h γ ih =>
      intro hδγ hγα
      let y : OrdinalInterval α := ⟨γ, Ordinal.zero_le _, hγα.le⟩
      let f : OrdinalC 𝕜 α := ordinalHeadIndicator α γ - ordinalHeadIndicator α δ
      have hsum := (ordinalOperatorRow_hasSum α T f
        ⟨δ, Ordinal.zero_le _, hδα.le⟩).tsum_eq
      have hz (z : OrdinalInterval α) (hzy : z ≠ y) :
          ordinalOperatorMatrix α T ⟨δ, Ordinal.zero_le _, hδα.le⟩ z * f z = 0 := by
        by_cases hzδ : z.val ≤ δ
        · simp only [f, ContinuousMap.sub_apply, ordinalHeadIndicator_apply,
            if_pos hzδ, if_pos (hzδ.trans hδγ.le), sub_self, mul_zero]
        · by_cases hzγ : z.val ≤ γ
          · have hzγlt : z.val < γ := lt_of_le_of_ne hzγ
              (fun he => hzy (Subtype.ext he))
            have hzero := ih z.val hzγlt (lt_of_not_ge hzδ) (hzγ.trans_lt hγα)
            change ordinalOperatorMatrix α T ⟨δ, Ordinal.zero_le _, hδα.le⟩ z = 0 at hzero
            rw [hzero, zero_mul]
          · simp only [f, ContinuousMap.sub_apply, ordinalHeadIndicator_apply,
              if_neg hzδ, if_neg hzγ, sub_self, mul_zero]
      rw [tsum_eq_single y hz] at hsum
      have hf : T f ⟨δ, Ordinal.zero_le _, hδα.le⟩ = 0 :=
        ordinalMatrixCut_headDifference_zero T hcut hτδ hδ hδγ.le hγα
      have hfy : f y = 1 := by
        simp only [f, y, ContinuousMap.sub_apply, ordinalHeadIndicator_apply,
          if_pos le_rfl, if_neg (not_le_of_gt hδγ), sub_zero]
      rw [hfy, mul_one, hf] at hsum
      exact hsum
  intro y hδy hyα
  exact hall y.val hδy hyα

theorem ordinalMatrixCut_limitRow_scalar {α τ δ : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (hcut : IsOrdinalMatrixCut T τ δ) (hτδ : τ < δ)
    (hδ : Order.IsSuccLimit δ) (hδα : δ < α)
    (f : OrdinalC 𝕜 α) (hhead : ∀ y : OrdinalInterval α, y.val ≤ τ → f y = 0)
    (htop : f ⟨α, Ordinal.zero_le _, le_rfl⟩ = 0) :
    T f ⟨δ, Ordinal.zero_le _, hδα.le⟩ =
      ordinalOperatorMatrix α T ⟨δ, Ordinal.zero_le _, hδα.le⟩
        ⟨δ, Ordinal.zero_le _, hδα.le⟩ * f ⟨δ, Ordinal.zero_le _, hδα.le⟩ := by
  let x : OrdinalInterval α := ⟨δ, Ordinal.zero_le _, hδα.le⟩
  have hsum := (ordinalOperatorRow_hasSum α T f x).tsum_eq
  have hz (y : OrdinalInterval α) (hyx : y ≠ x) : ordinalOperatorMatrix α T x y * f y = 0 := by
    by_cases hyτ : y.val ≤ τ
    · rw [hhead y hyτ, mul_zero]
    · rcases lt_or_gt_of_ne (show y.val ≠ δ from fun h => hyx (Subtype.ext h)) with hyδ | hδy
      · rw [(hcut.2 y x (lt_of_not_ge hyτ).le hyδ le_rfl hδα).2, zero_mul]
      · by_cases hyα : y.val < α
        · rw [ordinalMatrixCut_limitRow_above_zero T hcut hτδ hδ hδα y hδy hyα, zero_mul]
        · have he : y = ⟨α, Ordinal.zero_le _, le_rfl⟩ :=
            Subtype.ext (le_antisymm y.property.2 (le_of_not_gt hyα))
          rw [he, htop, mul_zero]
  rw [tsum_eq_single x hz] at hsum
  exact hsum.symm

end Posets
