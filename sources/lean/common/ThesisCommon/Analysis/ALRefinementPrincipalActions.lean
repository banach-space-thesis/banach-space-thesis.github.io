import ThesisCommon.Analysis.ALRefinementPrincipal

/-! Commuting principal-band projections and the actual spectral comparison
cuts required for finite positive-decomposition refinements. -/
noncomputable section
open Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E]
  [IsOrderedModule ℝ E] [HasSolidNorm E]

theorem IsOrderClosedIdeal.bandProjection_commute {I J : Submodule ℝ E}
    (hI : IsOrderClosedIdeal I) (hJ : IsOrderClosedIdeal J) :
    Function.Commute (bandProjection hI) (bandProjection hJ) := by
  intro x
  have hmem : bandProjection hJ (bandProjection hI x) ∈ I :=
    hI.solid (hI.bandProjection_mem x) (hJ.abs_bandProjection_le _)
  have hzero : bandProjection hI (bandProjection hJ (x-bandProjection hI x)) = 0 := by
    apply (hI.bandProjection_eq_zero_iff _).mpr
    intro y hy
    exact le_antisymm
      ((inf_le_inf_right _ (hJ.abs_bandProjection_le _)).trans_eq (hI.residual_disjoint x hy))
      (le_inf (abs_nonneg _) (abs_nonneg _))
  calc
    bandProjection hI (bandProjection hJ x) =
        bandProjection hI (bandProjection hJ (bandProjection hI x) +
          bandProjection hJ (x-bandProjection hI x)) := by
      congr 1
      rw [← map_add]
      congr 1
      abel
    _ = bandProjection hJ (bandProjection hI x) := by
      rw [map_add, hI.bandProjection_eq_self hmem, hzero, add_zero]

theorem principalBandProjection_commute (a b : E) :
    Function.Commute (principalBandProjection a) (principalBandProjection b) :=
  (principalBand_orderClosed a).bandProjection_commute (principalBand_orderClosed b)

theorem principalBandProjection_comp_commute (a b : E) :
    (principalBandProjection a).comp (principalBandProjection b) =
      (principalBandProjection b).comp (principalBandProjection a) := by
  ext x
  exact principalBandProjection_commute a b x

theorem principalBand_mono {a b : E} (hab : |a| ≤ |b|) : principalBand a ≤ principalBand b := by
  intro x hx z hz
  apply hx z
  intro w hw
  have hwa : w = a := hw
  subst w
  exact le_antisymm ((inf_le_inf_left _ hab).trans_eq (hz b (Set.mem_singleton b)))
    (le_inf (abs_nonneg _) (abs_nonneg _))

theorem principalBandProjection_mono {a b : E} (hab : |a| ≤ |b|) :
    principalBandProjection a ≤ principalBandProjection b := by
  intro x hx
  change bandProjection (principalBand_orderClosed a) x ≤
    bandProjection (principalBand_orderClosed b) x
  rw [(principalBand_orderClosed b).bandProjection_apply_of_nonneg x hx]
  apply ((principalBand_orderClosed b).positiveProjection_isLUB x hx).1
  exact ⟨principalBand_mono hab ((principalBand_orderClosed a).bandProjection_mem x),
    principalBandProjection_nonneg a x hx, principalBandProjection_le_id a x hx⟩

/-- The band of the positive part extracts exactly the positive part. -/
theorem principalBandProjection_posPart (d : E) :
    principalBandProjection d⁺ d = d⁺ := by
  have hneg : principalBandProjection d⁺ d⁻ = 0 := by
    apply (principalBandProjection_eq_zero_iff d⁺ d⁻).mpr
    rw [abs_of_nonneg (negPart_nonneg d), abs_of_nonneg (posPart_nonneg d), inf_comm]
    exact posPart_inf_negPart_eq_zero d
  calc
    principalBandProjection d⁺ d = principalBandProjection d⁺ (d⁺-d⁻) :=
      congrArg (principalBandProjection d⁺) (posPart_sub_negPart d).symm
    _ = d⁺ := by rw [map_sub, principalBandProjection_self, hneg, sub_zero]

theorem principalBandProjection_cut_nonneg (u x : E) (t : ℝ) :
    0 ≤ principalBandProjection (u-t • x)⁺ (u-t • x) := by
  rw [principalBandProjection_posPart]
  exact posPart_nonneg _

theorem principalBandProjection_cut_residual_nonpos (u x : E) (t : ℝ) :
    (ContinuousLinearMap.id ℝ E - principalBandProjection (u-t • x)⁺) (u-t • x) ≤ 0 := by
  change (u-t • x) - principalBandProjection (u-t • x)⁺ (u-t • x) ≤ 0
  rw [principalBandProjection_posPart]
  exact sub_nonpos.mpr (le_posPart _)

theorem principalBandProjection_cut_lower (u x : E) (t : ℝ) :
    t • principalBandProjection (u-t • x)⁺ x ≤ principalBandProjection (u-t • x)⁺ u := by
  have h := principalBandProjection_cut_nonneg u x t
  rw [map_sub, map_smul] at h
  exact sub_nonneg.mp h

theorem principalBandProjection_cut_upper (u x : E) (t : ℝ) :
    (ContinuousLinearMap.id ℝ E - principalBandProjection (u-t • x)⁺) u ≤
      t • (ContinuousLinearMap.id ℝ E - principalBandProjection (u-t • x)⁺) x := by
  have h := principalBandProjection_cut_residual_nonpos u x t
  rw [map_sub, map_smul] at h
  exact sub_nonpos.mp h

end ThesisCommon
