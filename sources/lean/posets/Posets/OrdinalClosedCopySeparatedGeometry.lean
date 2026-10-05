import Posets.OrdinalClosedCopyBandGeometry

/-! A band geometry in which the rank of the upper cell and the rank retained
by the compact core can differ.  This records the finite loss needed when an
initial cardinal is singular, while the lower coordinate retains the required
ordinal interval by its own ceiling-image estimate. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

structure OrdinalSeparatedBandCoreGeometry
    (F : Set Ordinal.{u}) (θ upper a b : Ordinal.{u}) where
  upperPoint : ordinalTowerLevel θ upper
  upperIsolated : IsOpen ({upperPoint} : Set (ordinalTowerLevel θ upper))
  H : Set Ordinal.{u}
  cell_eq : H = Iic θ ∩ {x | ordinalCeiling (ordinalTowerLevel θ upper) x = upperPoint.val}
  cell_clopen : IsClopen H
  cell_compact : IsCompact H
  core_compact : IsCompact (F ∩ H)
  core_nonempty : (F ∩ H).Nonempty
  modelOrdinal : Ordinal.{u}
  model : OrdinalInterval modelOrdinal ≃ₜ (ordinalCeiling (ordinalTowerLevel θ a) '' (F ∩ H))
  model_increasing : StrictMono (fun x => (model x).val)
  model_large : Ordinal.omega0 ^ b ≤ modelOrdinal
  p : C(H, (ordinalCeiling (ordinalTowerLevel θ a) '' (F ∩ H)))
  q : C((ordinalCeiling (ordinalTowerLevel θ a) '' (F ∩ H)), H)
  section_increasing : StrictMono q
  section_rightInverse : Function.RightInverse q p
  section_core : ∀ y, (q y).val ∈ F ∩ H
  coordinate_constant : ∀ x y : H,
    ordinalCeiling (ordinalTowerLevel θ a) x.val = ordinalCeiling (ordinalTowerLevel θ a) y.val →
      p x = p y

theorem ordinalSeparatedBandCoreGeometry_cell_subset
    {F : Set Ordinal.{u}} {θ upper a b : Ordinal.{u}}
    (G : OrdinalSeparatedBandCoreGeometry F θ upper a b) : G.H ⊆ Iic θ := by
  rw [G.cell_eq]
  exact inter_subset_left

theorem ordinalSeparatedBandCoreGeometry_of_isolated_upper_cell
    {F : Set Ordinal.{u}} {θ upper a b : Ordinal.{u}}
    (hθ : θ ∈ ordinalTowerLevel θ upper)
    (y : ordinalTowerLevel θ upper)
    (hyo : IsOpen ({y} : Set (ordinalTowerLevel θ upper)))
    (hF : IsCompact F) (hFθ : F ⊆ Iic θ)
    (hb : b ≠ 0) (habs : 1 + b = b) (hab : a + b ≤ upper)
    (hrank : (ordinalDerived
      (F ∩ {x | ordinalCeiling (ordinalTowerLevel θ upper) x = y.val}) (a + b)).Nonempty) :
    Nonempty (OrdinalSeparatedBandCoreGeometry F θ upper a b) := by
  let A := ordinalTowerLevel θ upper
  let H : Set Ordinal.{u} := Iic θ ∩ {x | ordinalCeiling A x = y.val}
  have hA : IsCompact A := ordinalTowerLevel_isCompact θ upper
  have hHA : IsClopen {x | ordinalCeiling A x = y.val} := by
    let r := ordinalCompactRetraction hA ⟨θ, hθ⟩
    have he : {x | ordinalCeiling A x = y.val} = r ⁻¹' {y} := by
      ext x
      change ordinalCeiling A x = y.val ↔ r x = y
      constructor
      · exact fun h => Subtype.ext h
      · exact fun h => congrArg Subtype.val h
    rw [he]
    exact ⟨isClosed_singleton.preimage r.continuous, hyo.preimage r.continuous⟩
  have hH : IsClopen H := (ordinal_isClopen_Iic θ).inter hHA
  have hHcompact : IsCompact H := by
    have hi : IsCompact (Iic θ) := by
      have he : Icc (0 : Ordinal.{u}) θ = Iic θ := by ext x; simp
      rw [← he]
      exact isCompact_Icc
    exact hi.inter_right hHA.isClosed
  have hC : IsCompact (F ∩ H) := hF.inter_right hH.isClosed
  have hCe : F ∩ H = F ∩ {x | ordinalCeiling A x = y.val} := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1, hx.2.2⟩
    · exact fun hx => ⟨hx.1, hFθ hx.1, hx.2⟩
  have hCrank : (ordinalDerived (F ∩ H) (a + b)).Nonempty := by
    rwa [hCe]
  have hne : (F ∩ H).Nonempty := by
    have hs := ordinalDerived_antitone hC.isClosed (Ordinal.zero_le (a + b))
    simpa only [ordinalDerived_zero] using hCrank.mono hs
  have hθa : θ ∈ ordinalTowerLevel θ a :=
    ordinalTowerLevel_antitone θ ((Ordinal.le_add_right a b).trans hab) hθ
  obtain ⟨η, e, he, hη⟩ := ordinalTowerCeiling_image_model_rank_of_succ_absorbed
    hθa hC (fun _ hx => hFθ hx.1) hb habs hCrank
  let p := ordinalClosedCoreCoordinate
    (ordinalTowerLevel_isCompact θ a) ⟨θ, hθa⟩ hC hne H
  obtain ⟨q, hqm, hqr, hqc⟩ := exists_ordinalClosedCoreCoordinate_section
    (ordinalTowerLevel_isCompact θ a) ⟨θ, hθa⟩ hC hne (inter_subset_right : F ∩ H ⊆ H)
  exact ⟨{
    upperPoint := y
    upperIsolated := hyo
    H := H
    cell_eq := rfl
    cell_clopen := hH
    cell_compact := hHcompact
    core_compact := hC
    core_nonempty := hne
    modelOrdinal := η
    model := e
    model_increasing := he
    model_large := hη
    p := p
    q := q
    section_increasing := hqm
    section_rightInverse := hqr
    section_core := hqc
    coordinate_constant := ordinalClosedCoreCoordinate_fiber_constant
      (ordinalTowerLevel_isCompact θ a) ⟨θ, hθa⟩ hC hne }⟩

theorem ordinalSeparatedBandCoreGeometry_section_leaf_closure
    {F L : Set Ordinal.{u}} {θ upper a b : Ordinal.{u}}
    (G : OrdinalSeparatedBandCoreGeometry F θ upper a b) (hF : F ⊆ closure L)
    (y : ordinalCeiling (ordinalTowerLevel θ a) '' (F ∩ G.H)) :
    (G.q y).val ∈ closure (L ∩ G.H) :=
  G.cell_clopen.isOpen.closure_inter ⟨hF (G.section_core y).1, (G.section_core y).2⟩

end Posets
