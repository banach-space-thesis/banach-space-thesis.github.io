import JLMS.OgdenCommonProjections
import Posets.OrdinalIdealTransportFinitePower

/-! Actual cofinal row annihilation for a Loy–Willis operator with zero endpoint
coefficient. This retains the projection witnesses needed for factorisation. -/
noncomputable section
namespace Posets
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

theorem exists_loyWillis_zeroEndpoint_tail_rows
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (S : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hS : S ∈ loyWillisZeroEndpointSubspace hc hu) :
    ∃ β : Ordinal.{0}, β < c.ord ∧
      ∃ g : C(OrdinalInterval c.ord, OrdinalInterval c.ord), StrictMono g ∧
        g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ ∧
        (∀ x, β < (g x).val) ∧
        (∀ f x, S (f - ordinalHeadProjection c.ord β f) (g x) = 0) := by
  let T : ℕ → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord := fun _ => S
  have hT (n : ℕ) : T n ∈ loyWillisZeroEndpointSubspace hc hu := hS
  have hcf : Cardinal.aleph0 < c.ord.cof := by simpa only [hc.cof_eq] using hu
  have hM (n : ℕ) : T n ∈ loyWillisSubspace hc hu := (hT n).1
  have hdiag (n : ℕ) : ordinalOperatorMatrix c.ord (T n)
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0 :=
    (hT n).2
  -- The first cutoff removes all endpoint rows, including their zero diagonal entries.
  obtain ⟨β, hβ, hrowβ⟩ := exists_ordinalOperatorEndpointRows_cutoff hcf T
  have hrow (n : ℕ) (y : OrdinalInterval c.ord) (hy : β < y.val) :
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0 := by
    by_cases hyκ : y.val < c.ord
    · exact hrowβ n y hy hyκ
    · have he : y = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ :=
        Subtype.ext (le_antisymm y.property.2 (le_of_not_gt hyκ))
      rw [he]
      exact hdiag n
  let J : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord := ordinalHeadProjection c.ord β
  let U : ℕ → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
    fun n => (T n).comp (ContinuousLinearMap.id 𝕜 _ - J)
  have hUrow (n : ℕ) : ordinalOperatorRow c.ord (U n)
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0 :=
    ordinalOperatorRow_endpoint_comp_tail_eq_zero (T n) (hrow n)
  -- The continuous endpoint columns vanish beyond one common cutoff.
  let f : ℕ → OrdinalC 𝕜 c.ord := fun n => loyWillisEndpointColumn hc hu (T n) (hM n)
  obtain ⟨γ, hγ, hcolumnγ⟩ := exists_common_ordinal_tail hcf f
  have hcolumn (n : ℕ) (x : OrdinalInterval c.ord) (hx : γ < x.val) :
      ordinalOperatorMatrix c.ord (T n) x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0 :=
    (hcolumnγ n x hx).trans (hdiag n)
  obtain ⟨δ, hδ, hsumsδ⟩ := exists_common_ordinalOperator_zero_row_sums hcf U hUrow
  let ρ : Ordinal.{0} := max β (max γ δ)
  have hρ : ρ < c.ord := max_lt hβ (max_lt hγ hδ)
  have hβρ : β ≤ ρ := le_max_left _ _
  have hγρ : γ ≤ ρ := (le_max_left _ _).trans (le_max_right _ _)
  have hδρ : δ ≤ ρ := (le_max_right _ _).trans (le_max_right _ _)
  have hτ : Order.succ β < c.ord := (Cardinal.isSuccLimit_ord hu.le).succ_lt hβ
  have hcutrows (n : ℕ) (y : OrdinalInterval c.ord)
      (hy : Order.succ β ≤ y.val) (_hyκ : y.val < c.ord) :
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0 :=
    hrow n y ((Order.lt_succ β).trans_le hy)
  let φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord) :=
    ordinalMatrixFamilyBlockContinuousMap hc hu T (Order.succ β) hτ hcutrows
  have hφ : StrictMono φ :=
    strictMono_ordinalMatrixFamilyBlockContinuousMap hc hu T (Order.succ β) hτ hcutrows
  have hφtop : φ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ :=
    ordinalMatrixFamilyBlockContinuousMap_endpoint hc hu T (Order.succ β) hτ hcutrows
  -- Ogden 4.8 kills each sufficiently late limit row of every Uₙ.
  have hzero (n : ℕ) (w : OrdinalC 𝕜 c.ord) (x : OrdinalInterval c.ord)
      (hx : Order.IsSuccLimit x.val) (hρx : ρ < (φ x).val) : U n w (φ x) = 0 := by
    by_cases hxκ : (φ x).val < c.ord
    · have hlimit : Order.IsSuccLimit (φ x).val :=
        (isNormal_ordinalMatrixFamilyBlockMap T (Order.succ β)).map_isSuccLimit hx
      have hcut : IsOrdinalMatrixCut (T n) (Order.succ β) (φ x).val :=
        isOrdinalMatrixCut_familyBlockMap T (Order.succ β) x.val n
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
  · intro w x
    exact hzero 0 w (initialOrdinalTailLimitIndices hu hρ x)
      (initialOrdinalTailLimitIndices_isSuccLimit hu hρ x)
      (ordinalTailLimitRowsSelector_above hu hρ φ hφ x)

end Posets

