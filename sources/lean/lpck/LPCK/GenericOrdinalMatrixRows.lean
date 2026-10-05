/- Universe-polymorphic extension of Posets.OrdinalIdealTransportMatrixRows. Actual maps and bounds retained; paper-specific ideal statements omitted where they are not needed. -/
import LPCK.GenericOrdinalMatrixBounds

/-! Simultaneous diagonal-club rows together with the individual two-sided
cutoffs needed for a full regular-cardinal operator matrix. -/
noncomputable section
universe u
namespace LPCK.GenericOrdinal
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

theorem exists_loyWillis_regular_matrix_rows
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (S : c.ord.toType → c.ord.toType → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hS : ∀ i j, S i j ∈ loyWillisZeroEndpointSubspace hc hu) :
    ∃ β δ τ : c.ord.toType → c.ord.toType → Ordinal.{u},
      (∀ i j, β i j < c.ord) ∧ (∀ i j, δ i j < c.ord) ∧ (∀ i j, τ i j < c.ord) ∧
      (∀ i j f, S i j (ordinalHeadProjection c.ord (β i j) f) ∈ ordinalTailSpace c.ord (δ i j)) ∧
      (∀ i j f, (∀ y : OrdinalInterval c.ord, y.val ≤ τ i j → f y = 0) →
        f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0 →
        ∀ x : OrdinalInterval c.ord, x.val ≤ (ordinalMatrixCode hu (i,j)).val → S i j f x = 0) ∧
      ∃ g : C(OrdinalInterval c.ord, OrdinalInterval c.ord), StrictMono g ∧
        g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ ∧
        ∀ i j f x, (ordinalMatrixCode hu (i,j)).val < (g x).val →
          S i j (f - ordinalHeadProjection c.ord (β i j) f) (g x) = 0 := by
  classical
  let e := ordinalMatrixCode hu
  obtain ⟨b, hb, g, hg, htop, hrows⟩ := exists_loyWillis_diagonal_family_tail_rows hc hu
    (fun k => S (e.symm k).1 (e.symm k).2) (fun k => hS _ _)
  let β (i j : c.ord.toType) := b (e (i,j))
  have hβ (i j : c.ord.toType) : β i j < c.ord := hb _
  have hκ : Cardinal.aleph0 < c.ord.cof := by simpa only [hc.cof_eq] using hu
  have hhead (i j : c.ord.toType) := exists_ordinalOperator_head_image_tail hκ
    (show (β i j).card < c.ord.cof by
      simpa only [hc.cof_eq] using Cardinal.lt_ord.mp (hβ i j)) (hβ i j).le (S i j)
  choose δ hδ hhead using hhead
  have hearly (i j : c.ord.toType) := exists_ordinalOperator_early_rows_cutoff hκ
    (show (e (i,j)).val.card < c.ord.cof by
      simpa only [hc.cof_eq] using Cardinal.lt_ord.mp (e (i,j)).property)
    (e (i,j)).property.le (S i j)
  choose τ hτ hearly using hearly
  refine ⟨β, δ, τ, hβ, hδ, hτ, hhead, hearly, g, hg, htop, ?_⟩
  intro i j f x hx
  have h := hrows (e (i,j)) f x hx
  simpa only [Equiv.symm_apply_apply] using h

end LPCK.GenericOrdinal



