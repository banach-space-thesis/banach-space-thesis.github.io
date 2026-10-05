import JLMS.OrdinalMatrixBlocks
import JLMS.OrdinalMatrixHead
import JLMS.OrdinalLimitRow
import JLMS.OrdinalCountableTails

/-!
# Vanishing rows at late limit block boundaries

Removing the head columns kills the endpoint row. The resulting row sums
are therefore eventually zero. At a limit block boundary, the separated
matrix argument of Ogden Lemma 4.8 then kills the entire row. Countable
families admit one common cutoff for their row sums.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem ordinalOperator_apply_eq_zero_of_row_eq_zero {α : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (x : OrdinalInterval α)
    (hx : ordinalOperatorRow α T x = 0) (f : OrdinalC 𝕜 α) : T f x = 0 := by
  have hs := (ordinalOperatorRow_hasSum α T f x).tsum_eq
  have hz (y : OrdinalInterval α) : ordinalOperatorMatrix α T x y = 0 := by
    change ordinalOperatorRow α T x y = 0
    rw [hx]
    rfl
  simpa only [hz, zero_mul, tsum_zero] using hs.symm

theorem exists_common_ordinalOperator_zero_row_sums {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof)
    (T : ℕ → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (hzero : ∀ n, ordinalOperatorRow α (T n) ⟨α, Ordinal.zero_le _, le_rfl⟩ = 0) :
    ∃ ρ < α, ∀ n (x : OrdinalInterval α), ρ < x.val → T n (ContinuousMap.const _ 1) x = 0 := by
  obtain ⟨ρ, hρ, hs⟩ := exists_common_ordinal_tail hα
    (fun n => T n (ContinuousMap.const _ 1))
  refine ⟨ρ, hρ, fun n x hx => ?_⟩
  exact (hs n x hx).trans (ordinalOperator_apply_eq_zero_of_row_eq_zero (T n) _
    (hzero n) (ContinuousMap.const _ 1))

/-- The tail version of Ogden 4.8, applied after removing the head columns. -/
theorem ordinalOperatorRow_comp_tail_eq_zero_at_cut {α β ρ δ : Ordinal.{u}}
    (hβρ : β ≤ ρ) (hρδ : ρ < δ) (hδα : δ < α) (hδ : Order.IsSuccLimit δ)
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (hcut : IsOrdinalMatrixCut T (Order.succ β) δ)
    (hcolumn : ∀ x : OrdinalInterval α, ρ < x.val →
      ordinalOperatorMatrix α T x ⟨α, Ordinal.zero_le _, le_rfl⟩ = 0)
    (hsums : ∀ x : OrdinalInterval α, ρ < x.val →
      (T.comp (ContinuousLinearMap.id 𝕜 _ - ordinalHeadProjection α β))
        (ContinuousMap.const _ 1) x = 0) :
    ordinalOperatorRow α (T.comp
      (ContinuousLinearMap.id 𝕜 _ - ordinalHeadProjection α β))
        ⟨δ, Ordinal.zero_le _, hδα.le⟩ = 0 := by
  apply ordinalOperatorRow_eq_zero_of_separated_limit_tail hδα.le hδ hρδ
  · intro x z hρx hx hz
    rw [ordinalOperatorMatrix_comp_tail]
    by_cases hzβ : z.val ≤ β
    · rw [if_pos hzβ]
    · rw [if_neg hzβ]
      by_cases hzα : z.val < α
      · exact (hcut.2 x z (Order.succ_le_of_lt (hβρ.trans_lt hρx)) hx hz hzα).1
      · have hze : z = ⟨α, Ordinal.zero_le _, le_rfl⟩ :=
          Subtype.ext (le_antisymm z.prop.2 (le_of_not_gt hzα))
        rw [hze]
        exact hcolumn x hρx
  · intro z hz
    rw [ordinalOperatorMatrix_comp_tail]
    by_cases hzβ : z.val ≤ β
    · rw [if_pos hzβ]
    · rw [if_neg hzβ]
      exact (hcut.2 z ⟨δ, Ordinal.zero_le _, hδα.le⟩
        (Order.succ_le_of_lt (lt_of_not_ge hzβ)) hz le_rfl hδα).2
  · intro x hx _
    exact hsums x hx

end JLMS
