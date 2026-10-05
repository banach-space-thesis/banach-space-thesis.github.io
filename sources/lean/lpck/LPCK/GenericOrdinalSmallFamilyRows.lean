/- Universe-polymorphic extension of Posets.OrdinalIdealTransportSmallFamilyRows. Actual maps and bounds retained; paper-specific ideal statements omitted where they are not needed. -/
import LPCK.GenericOrdinalRegularTail
import LPCK.GenericOrdinalSmallFamilyBlocks

/-! Simultaneous cofinal row annihilation for countably many Loy–Willis operators with zero endpoint
coefficient. This retains the projection witnesses needed for factorisation. -/
noncomputable section
universe u
namespace LPCK.GenericOrdinal
set_option synthInstance.maxHeartbeats 200000
open JLMS
variable {𝕜 : Type} [RCLike 𝕜] {I : Type u} [Nonempty I]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

theorem exists_smallIndex_ordinalOperatorEndpointRows_cutoff {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (hI : Cardinal.mk I < α.cof)
    (T : I → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) :
    ∃ β < α, ∀ n (y : OrdinalInterval α), β < y.val → y.val < α →
      ordinalOperatorMatrix α (T n) ⟨α, Ordinal.zero_le _, le_rfl⟩ y = 0 :=
  exists_smallIndex_ordinal_ellOne_cutoff hα hI
    (fun n => ordinalOperatorRow α (T n) ⟨α, Ordinal.zero_le _, le_rfl⟩)

theorem exists_smallIndex_ordinalOperator_zero_row_sums {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (hI : Cardinal.mk I < α.cof)
    (T : I → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (hzero : ∀ n, ordinalOperatorRow α (T n) ⟨α, Ordinal.zero_le _, le_rfl⟩ = 0) :
    ∃ ρ < α, ∀ n (x : OrdinalInterval α), ρ < x.val → T n (ContinuousMap.const _ 1) x = 0 := by
  obtain ⟨ρ, hρ, hs⟩ := exists_smallIndex_ordinal_tail hα hI
    (fun n => T n (ContinuousMap.const _ 1))
  refine ⟨ρ, hρ, fun n x hx => ?_⟩
  exact (hs n x hx).trans (ordinalOperator_apply_eq_zero_of_row_eq_zero (T n) _
    (hzero n) (ContinuousMap.const _ 1))

theorem exists_loyWillis_zeroEndpoint_smallFamily_tail_rows
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (hI : Cardinal.mk I < c)
    (T : I → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hT : ∀ n, T n ∈ loyWillisZeroEndpointSubspace hc hu) :
    ∃ β : Ordinal.{u}, β < c.ord ∧
      ∃ g : C(OrdinalInterval c.ord, OrdinalInterval c.ord), StrictMono g ∧
        g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ ∧
        (∀ x, β < (g x).val) ∧
        (∀ n f x, T n (f - ordinalHeadProjection c.ord β f) (g x) = 0) := by
  have hcf : Cardinal.aleph0 < c.ord.cof := by simpa only [hc.cof_eq] using hu
  have hIf : Cardinal.mk I < c.ord.cof := by simpa only [hc.cof_eq] using hI
  have hM (n : I) : T n ∈ loyWillisSubspace hc hu := (hT n).1
  have hdiag (n : I) : ordinalOperatorMatrix c.ord (T n)
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0 :=
    (hT n).2
  -- The first cutoff removes all endpoint rows, including their zero diagonal entries.
  obtain ⟨β, hβ, hrowβ⟩ := exists_smallIndex_ordinalOperatorEndpointRows_cutoff hcf hIf T
  have hrow (n : I) (y : OrdinalInterval c.ord) (hy : β < y.val) :
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0 := by
    by_cases hyκ : y.val < c.ord
    · exact hrowβ n y hy hyκ
    · have he : y = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ :=
        Subtype.ext (le_antisymm y.property.2 (le_of_not_gt hyκ))
      rw [he]
      exact hdiag n
  let J : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord := ordinalHeadProjection c.ord β
  let U : I → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
    fun n => (T n).comp (ContinuousLinearMap.id 𝕜 _ - J)
  have hUrow (n : I) : ordinalOperatorRow c.ord (U n)
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0 :=
    ordinalOperatorRow_endpoint_comp_tail_eq_zero (T n) (hrow n)
  -- The continuous endpoint columns vanish beyond one common cutoff.
  let f : I → OrdinalC 𝕜 c.ord := fun n => loyWillisEndpointColumn hc hu (T n) (hM n)
  obtain ⟨γ, hγ, hcolumnγ⟩ := exists_smallIndex_ordinal_tail hcf hIf f
  have hcolumn (n : I) (x : OrdinalInterval c.ord) (hx : γ < x.val) :
      ordinalOperatorMatrix c.ord (T n) x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0 :=
    (hcolumnγ n x hx).trans (hdiag n)
  obtain ⟨δ, hδ, hsumsδ⟩ := exists_smallIndex_ordinalOperator_zero_row_sums hcf hIf U hUrow
  let ρ : Ordinal.{u} := max β (max γ δ)
  have hρ : ρ < c.ord := max_lt hβ (max_lt hγ hδ)
  have hβρ : β ≤ ρ := le_max_left _ _
  have hγρ : γ ≤ ρ := (le_max_left _ _).trans (le_max_right _ _)
  have hδρ : δ ≤ ρ := (le_max_right _ _).trans (le_max_right _ _)
  have hτ : Order.succ β < c.ord := (Cardinal.isSuccLimit_ord hu.le).succ_lt hβ
  have hcutrows (n : I) (y : OrdinalInterval c.ord)
      (hy : Order.succ β ≤ y.val) (_hyκ : y.val < c.ord) :
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0 :=
    hrow n y ((Order.lt_succ β).trans_le hy)
  let φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord) :=
    ordinalMatrixSmallFamilyBlockContinuousMap hc hu hI T (Order.succ β) hτ hcutrows
  have hφ : StrictMono φ :=
    strictMono_ordinalMatrixSmallFamilyBlockContinuousMap hc hu hI T (Order.succ β) hτ hcutrows
  have hφtop : φ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ :=
    ordinalMatrixSmallFamilyBlockContinuousMap_endpoint hc hu hI T (Order.succ β) hτ hcutrows
  -- Ogden 4.8 kills each sufficiently late limit row of every Uₙ.
  have hzero (n : I) (w : OrdinalC 𝕜 c.ord) (x : OrdinalInterval c.ord)
      (hx : Order.IsSuccLimit x.val) (hρx : ρ < (φ x).val) : U n w (φ x) = 0 := by
    by_cases hxκ : (φ x).val < c.ord
    · have hlimit : Order.IsSuccLimit (φ x).val :=
        (isNormal_ordinalMatrixSmallFamilyBlockMap T (Order.succ β)).map_isSuccLimit hx
      have hcut : IsOrdinalMatrixCut (T n) (Order.succ β) (φ x).val :=
        isOrdinalMatrixCut_smallFamilyBlockMap T (Order.succ β) x.val n
      have hzrow : ordinalOperatorRow c.ord (U n) (φ x) = 0 :=
        ordinalOperatorRow_comp_tail_eq_zero_at_cut hβρ hρx hxκ hlimit (T n) hcut
          (fun y hy => hcolumn n y (hγρ.trans_lt hy))
          (fun y hy => hsumsδ n y (hδρ.trans_lt hy))
      exact ordinalOperator_apply_eq_zero_of_row_eq_zero (U n) (φ x) hzrow w
    · have he : φ x = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ :=
        Subtype.ext (le_antisymm (φ x).property.2 (le_of_not_gt hxκ))
      rw [he]
      exact ordinalOperator_apply_eq_zero_of_row_eq_zero (U n) _ (hUrow n) w
  let g := ordinalTailLimitRowsSelector hu hρ φ
  have hg : StrictMono g := ordinalTailLimitRowsSelector_strictMono hu hρ φ hφ
  have hgtop : g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ :=
    ordinalTailLimitRowsSelector_endpoint hu hρ φ hφtop
  refine ⟨β, hβ, g, hg, hgtop, ?_, ?_⟩
  · intro x
    exact hβρ.trans_lt (ordinalTailLimitRowsSelector_above hu hρ φ hφ x)
  · intro n w x
    exact hzero n w (initialOrdinalTailLimitIndices hu hρ x)
      (initialOrdinalTailLimitIndices_isSuccLimit hu hρ x)
      (ordinalTailLimitRowsSelector_above hu hρ φ hφ x)

end LPCK.GenericOrdinal






