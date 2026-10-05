import Posets.OrdinalIdealTransportMatrixRows
import Posets.OrdinalIdealTransportMatchedSelector

/-! A regular-cardinal matrix of zero-endpoint Loy–Willis operators has
matched coordinate compressions annihilating every matrix entry. -/
noncomputable section
namespace Posets
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 1000000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

theorem exists_loyWillis_regular_matrix_compression
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (S : c.ord.toType → c.ord.toType → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hS : ∀ i j, S i j ∈ loyWillisZeroEndpointSubspace hc hu) :
    ∃ L R : c.ord.toType → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord,
      (∀ i, (L i).comp (R i) = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ i j, (L i).comp ((S i j).comp (R j)) = 0) ∧
      (∀ i f, R i f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0) ∧
      (∀ i, ‖L i‖ ≤ 4) ∧ (∀ i, ‖R i‖ ≤ 2) := by
  classical
  obtain ⟨β, δ, τ, hβ, hδ, hτ, hhead, hearly, g, hg, htop, hrows⟩ :=
    exists_loyWillis_regular_matrix_rows hc hu S hS
  let q (i j : c.ord.toType) := (ordinalMatrixCode hu (i,j)).val
  let b (i j : c.ord.toType) := max (q i j) (max (β i j) (max (δ i j) (τ i j)))
  have hb (i j : c.ord.toType) : b i j < c.ord :=
    max_lt (ordinalMatrixCode hu (i,j)).property (max_lt (hβ i j) (max_lt (hδ i j) (hτ i j)))
  have hqb (i j : c.ord.toType) : q i j ≤ b i j := le_max_left _ _
  have hβb (i j : c.ord.toType) : β i j ≤ b i j := (le_max_left _ _).trans (le_max_right _ _)
  have hδb (i j : c.ord.toType) : δ i j ≤ b i j :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hτb (i j : c.ord.toType) : τ i j ≤ b i j :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  let a := ordinalMatrixPredecessorBound b
  have ha (i : c.ord.toType) : a i < c.ord := ordinalMatrixPredecessorBound_lt hc b hb i
  let G (i : c.ord.toType) := ordinalTailLimitRowsSelector hu (ha i) g
  have hG (i : c.ord.toType) : StrictMono (G i) :=
    ordinalTailLimitRowsSelector_strictMono hu (ha i) g hg
  have hGtop (i : c.ord.toType) : G i ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := ordinalTailLimitRowsSelector_endpoint hu (ha i) g htop
  have hGa (i : c.ord.toType) (x : OrdinalInterval c.ord) : a i < (G i x).val :=
    ordinalTailLimitRowsSelector_above hu (ha i) g hg x
  let L (i : c.ord.toType) := ordinalSelectorLeft (𝕜 := 𝕜) hu (G i)
  let R (i : c.ord.toType) := ordinalSelectorRight (𝕜 := 𝕜) hu (a i) (G i) (hG i) (hGtop i)
  have hRhead (i : c.ord.toType) (f : OrdinalC 𝕜 c.ord) (x : OrdinalInterval c.ord)
      (hx : x.val ≤ a i) : R i f x = 0 :=
    ordinalSelectorRight_head_zero hu (a i) (G i) (hG i) (hGtop i) f x hx
  have hRtop (i : c.ord.toType) (f : OrdinalC 𝕜 c.ord) :
      R i f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0 :=
    ordinalSelectorRight_endpoint_zero hu (a i) (ha i) (G i) (hG i) (hGtop i) f
  refine ⟨L, R, (fun i => ordinalSelectorLeft_right hu (a i) (G i) (hG i) (hGtop i) (hGa i)),
    ?_, hRtop, (fun i => norm_ordinalSelectorLeft_le hu (G i)),
    (fun i => norm_ordinalSelectorRight_le hu (a i) (G i) (hG i) (hGtop i))⟩
  intro i j
  apply ContinuousLinearMap.ext
  intro f
  change L i (S i j (R j f)) = 0
  apply ordinalSelectorLeft_eq_zero_of_read_constant hu (G i)
  rcases le_or_gt j i with hji | hij
  · have hba : b i j ≤ a i := by
      rcases hji.eq_or_lt with h | h
      · subst j
        exact ordinalMatrixPredecessorBound_diag b i
      · exact ordinalMatrixPredecessorBound_outgoing b h
    have hread (x : OrdinalInterval c.ord) : S i j (R j f) (G i x) =
        S i j (ordinalHeadProjection c.ord (β i j) (R j f))
          ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := by
      have hz := hrows i j (R j f) (initialOrdinalTailLimitIndices hu (ha i) x)
        (((hqb i j).trans hba).trans_lt (hGa i x))
      have heq : S i j (R j f) (G i x) =
          S i j (ordinalHeadProjection c.ord (β i j) (R j f)) (G i x) := by
        simpa only [map_sub, ContinuousMap.sub_apply, sub_eq_zero] using hz
      exact heq.trans (hhead i j (R j f) (G i x)
        (((hδb i j).trans hba).trans_lt (hGa i x)))
    intro x
    exact (hread x).trans (hread _).symm
  · have hba : b i j ≤ a j := ordinalMatrixPredecessorBound_incoming b hij
    have hp : ordinalHeadProjection c.ord (β i j) (R j f) = 0 := by
      ext x
      rw [ordinalHeadProjection_apply]
      split_ifs with hx
      · exact hRhead j f x (hx.trans ((hβb i j).trans hba))
      · rfl
    have hz (x : OrdinalInterval c.ord) : S i j (R j f) (G i x) = 0 := by
      by_cases hx : (G i x).val ≤ q i j
      · exact hearly i j (R j f)
          (fun y hy => hRhead j f y (hy.trans ((hτb i j).trans hba))) (hRtop j f) (G i x) hx
      · have hr := hrows i j (R j f) (initialOrdinalTailLimitIndices hu (ha i) x) (lt_of_not_ge hx)
        rw [hp, sub_zero] at hr
        exact hr
    intro x
    rw [hz x, hz _]

end Posets
