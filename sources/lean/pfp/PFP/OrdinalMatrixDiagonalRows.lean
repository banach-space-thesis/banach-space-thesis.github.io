import PFP.OrdinalMatrixDiagonalClubs
import PFP.OrdinalRegularInitialRows
/-! A regular-cardinal family of zero-endpoint Loy–Willis operators admits
one common normal selector which annihilates each member's tail rows after
its own index. The cutoffs remain individual; no common cutoff is asserted. -/
noncomputable section
namespace Posets.UniverseRegularMatrix
universe ordU
open Posets.UniverseRegularInitial
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

theorem exists_loyWillis_diagonal_family_tail_rows
    {c : Cardinal.{ordU}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : Set.Iio c.ord → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hT : ∀ i, T i ∈ loyWillisZeroEndpointSubspace hc hu) :
    ∃ β : Set.Iio c.ord → Ordinal.{ordU}, (∀ i, β i < c.ord) ∧
      ∃ g : C(OrdinalInterval c.ord, OrdinalInterval c.ord), StrictMono g ∧
        g ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ ∧
        ∀ i f x, i.val < (g x).val →
          T i (f - ordinalHeadProjection c.ord (β i) f) (g x) = 0 := by
  classical
  have hsingle (i : Set.Iio c.ord) := exists_loyWillis_zeroEndpoint_tail_rows hc hu (T i) (hT i)
  choose β hβ g hg hgtop hgb hzero using hsingle
  let s (i : Ordinal.{ordU}) : Set Ordinal.{ordU} := if hi : i < c.ord then
    Set.range (fun x : OrdinalInterval c.ord => (g ⟨i, hi⟩ x).val) ∪ Set.Ici c.ord else Set.univ
  have hclosed (i : Ordinal.{ordU}) (hi : i < c.ord) : IsClosed (s i) := by
    simp only [s, dif_pos hi]
    exact (isCompact_range (continuous_subtype_val.comp (g ⟨i,hi⟩).continuous)).isClosed.union isClosed_Ici
  have hcofinal (i : Ordinal.{ordU}) (hi : i < c.ord) (η : Ordinal.{ordU}) (hη : η < c.ord) :
      ∃ δ < c.ord, η < δ ∧ δ ∈ s i := by
    let x : OrdinalInterval c.ord := ⟨Order.succ η, Ordinal.zero_le _,
      ((Cardinal.isSuccLimit_ord hu.le).succ_lt hη).le⟩
    have hx : x < (⟨c.ord, Ordinal.zero_le _, le_rfl⟩ : OrdinalInterval c.ord) :=
      (Cardinal.isSuccLimit_ord hu.le).succ_lt hη
    refine ⟨(g ⟨i,hi⟩ x).val, ?_, ?_, ?_⟩
    · simpa only [hgtop] using hg ⟨i,hi⟩ hx
    · exact (Order.lt_succ η).trans_le (hg ⟨i,hi⟩).le_apply
    · simp only [s, dif_pos hi, Set.mem_union, Set.mem_range]
      exact Or.inl ⟨x, rfl⟩
  let D := ordinalDiagonalIntersection c.ord s
  have hD : IsClosed D := isClosed_ordinalDiagonalIntersection c.ord s hclosed
  have hlarge (δ : Ordinal.{ordU}) (hδ : c.ord ≤ δ) : δ ∈ D := by
    intro i hi _
    simp only [s, dif_pos hi, Set.mem_union, Set.mem_Ici]
    exact Or.inr hδ
  have hunbdd : ¬ BddAbove D := by
    rw [not_bddAbove_iff]
    intro η
    exact ⟨max c.ord (Order.succ η), hlarge _ (le_max_left _ _),
      (Order.lt_succ η).trans_le (le_max_right _ _)⟩
  have hnormal : Ordinal.IsNormal (Ordinal.enumOrd D) :=
    (Ordinal.enumOrd_isNormal_iff_isClosed hunbdd).mpr hD
  have hφlt (ν : Ordinal.{ordU}) (hν : ν < c.ord) : Ordinal.enumOrd D ν < c.ord :=
    enumOrd_lt_of_cofinal_below
      (fun ξ hξ => by simpa only [hc.cof_eq] using Cardinal.lt_ord.mp hξ)
      (exists_regularOrdinal_diagonalIntersection_above hc hu s hclosed hcofinal) ν hν
  have hφtop : Ordinal.enumOrd D c.ord = c.ord := by
    apply le_antisymm _ hnormal.le_apply
    exact Ordinal.enumOrd_le_of_forall_lt (hlarge c.ord le_rfl) hφlt
  let φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord) :=
    { toFun := fun x => ⟨Ordinal.enumOrd D x.val, Ordinal.zero_le _, by
        have h := hnormal.monotone x.property.2
        rwa [hφtop] at h⟩
      continuous_toFun := ((Order.IsNormal.continuous hnormal).comp continuous_subtype_val).subtype_mk _ }
  have hφmono : StrictMono φ := fun x y hxy => hnormal.strictMono hxy
  have hφendpoint : φ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := Subtype.ext hφtop
  refine ⟨β, hβ, φ, hφmono, hφendpoint, ?_⟩
  intro i f x hix
  have hmem := Ordinal.enumOrd_mem hunbdd x.val
  have hsi : (φ x).val ∈ s i.val := hmem i.val i.property hix
  have hsiSet : s i.val = Set.range (fun y : OrdinalInterval c.ord => (g i y).val) ∪ Set.Ici c.ord := by
    have hi : i.val < c.ord := i.property
    simp only [s, dif_pos hi]
  rw [hsiSet] at hsi
  rcases hsi with ⟨y, hy⟩ | htop
  · have he : φ x = g i y := Subtype.ext hy.symm
    rw [he]
    exact hzero i f y
  · have he : φ x = (⟨c.ord, Ordinal.zero_le _, le_rfl⟩ : OrdinalInterval c.ord) :=
      Subtype.ext (le_antisymm (φ x).property.2 htop)
    rw [he, ← hgtop i]
    exact hzero i f _

end Posets.UniverseRegularMatrix


