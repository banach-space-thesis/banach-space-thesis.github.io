import Posets.OrdinalClosedCoreSection
import Posets.OrdinalBandInsertion

/-! Actual band coordinates from a closed core. Rounding first to a lower
ordinal level and then to the core's image gives a continuous coordinate
map. Its continuous section stays inside the original core. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

variable {A C H : Set Ordinal.{u}}
    (hA : IsCompact A) (hneA : A.Nonempty) (hC : IsCompact C) (hneC : C.Nonempty)

def ordinalClosedCoreCoordinate (H : Set Ordinal.{u}) :
    C(H, (ordinalCeiling A '' C)) :=
  (ordinalCompactRetraction (hC.image (ordinalCeiling_continuous hA hneA))
    (hneC.image (ordinalCeiling A))).comp
      ⟨fun x => ordinalCeiling A x.val,
        (ordinalCeiling_continuous hA hneA).comp continuous_subtype_val⟩

@[simp] theorem ordinalClosedCoreCoordinate_apply (x : H) :
    (ordinalClosedCoreCoordinate hA hneA hC hneC H x).val =
      ordinalCeiling (ordinalCeiling A '' C) (ordinalCeiling A x.val) := rfl

theorem ordinalClosedCoreCoordinate_fiber_constant (x y : H)
    (hxy : ordinalCeiling A x.val = ordinalCeiling A y.val) :
    ordinalClosedCoreCoordinate hA hneA hC hneC H x =
      ordinalClosedCoreCoordinate hA hneA hC hneC H y := by
  apply Subtype.ext
  simp only [ordinalClosedCoreCoordinate_apply, hxy]

theorem exists_ordinalClosedCoreCoordinate_section (hCH : C ⊆ H) :
    ∃ q : C((ordinalCeiling A '' C), H), StrictMono q ∧
      Function.RightInverse q (ordinalClosedCoreCoordinate hA hneA hC hneC H) ∧
      ∀ y, (q y).val ∈ C := by
  obtain ⟨s, hsm, hsr⟩ := ordinalCeiling_image_continuous_section hA hneA hC hneC
  let q : C((ordinalCeiling A '' C), H) :=
    ⟨fun y => ⟨(s y).val, hCH (s y).property⟩,
      (continuous_subtype_val.comp s.continuous).subtype_mk _⟩
  refine ⟨q, hsm, ?_, fun y => (s y).property⟩
  intro y
  apply Subtype.ext
  change ordinalCeiling (ordinalCeiling A '' C) (ordinalCeiling A (s y).val) = y.val
  rw [hsr y, ordinalCeiling_eq_of_mem y.property]

theorem ordinalClosedCoreCoordinate_insert_constant
    {𝕜 : Type*} [RCLike 𝕜] [CompactSpace H]
    [CompactSpace (ordinalCeiling A '' C)] (hH : IsClopen H)
    (f : C((ordinalCeiling A '' C), 𝕜)) (x y : H)
    (hxy : ordinalCeiling A x.val = ordinalCeiling A y.val) :
    ordinalBandInsert H hH (ordinalClosedCoreCoordinate hA hneA hC hneC H) f x =
      ordinalBandInsert H hH (ordinalClosedCoreCoordinate hA hneA hC hneC H) f y :=
  ordinalBandInsert_constant_on_fiber H hH _ f x y
    (ordinalClosedCoreCoordinate_fiber_constant hA hneA hC hneC x y hxy)

end Posets
