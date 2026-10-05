import Posets.OrdinalMonotoneSection
import ThesisCommon.Analysis.OrdinalCopiesClassification
import ThesisCommon.Analysis.OrdinalRetraction

/-! Continuous sections of monotone surjections between compact ordinal
cores. The map being split need not be continuous. Increasing compact
ordinal models reduce the construction to least fibers on ordinal intervals. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

theorem ordinalCompact_monotone_surjective_section
    {C D : Set Ordinal.{u}} (hC : IsCompact C) (hne : C.Nonempty)
    (hD : IsCompact D) (f : C → D) (hf : Monotone f) (hs : Function.Surjective f) :
    ∃ q : C(D, C), StrictMono q ∧ Function.RightInverse q f := by
  have hDne : D.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨(f ⟨x, hx⟩).val, (f ⟨x, hx⟩).property⟩
  obtain ⟨α, eC, heC, _⟩ := ordinal_compact_order_homeomorph hC hne
  obtain ⟨β, eD, heD, _⟩ := ordinal_compact_order_homeomorph hD hDne
  have hmonoC : Monotone eC := fun _ _ h => heC.monotone h
  have hmonoDinv : Monotone eD.symm := by
    intro x y hxy
    apply heD.le_iff_le.mp
    simpa only [Homeomorph.apply_symm_apply] using hxy
  let g : OrdinalInterval α → OrdinalInterval β := fun x => eD.symm (f (eC x))
  have hg : Monotone g := hmonoDinv.comp (hf.comp hmonoC)
  have hgs : Function.Surjective g := eD.symm.surjective.comp (hs.comp eC.surjective)
  obtain ⟨s, hsm, hsr⟩ := exists_ordinalMonotone_continuous_section g hg hgs
  let q : C(D, C) :=
    ⟨fun y => eC (s (eD.symm y)), eC.continuous.comp (s.continuous.comp eD.symm.continuous)⟩
  refine ⟨q, ?_, ?_⟩
  · intro x y hxy
    apply heC
    apply hsm
    apply heD.lt_iff_lt.mp
    simpa only [Homeomorph.apply_symm_apply] using hxy
  · intro y
    have h := congrArg eD (hsr (eD.symm y))
    simpa only [g, Homeomorph.apply_symm_apply] using h

theorem ordinalCeiling_image_continuous_section
    {A C : Set Ordinal.{u}} (hA : IsCompact A) (hneA : A.Nonempty)
    (hC : IsCompact C) (hneC : C.Nonempty) :
    ∃ q : C((ordinalCeiling A '' C), C), StrictMono q ∧
      ∀ y, ordinalCeiling A (q y).val = y.val := by
  let f : C → (ordinalCeiling A '' C) := fun x =>
    ⟨ordinalCeiling A x, ⟨x.val, x.property, rfl⟩⟩
  have hs : Function.Surjective f := by
    rintro ⟨y, x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  obtain ⟨q, hq, hr⟩ := ordinalCompact_monotone_surjective_section hC hneC
    (hC.image (ordinalCeiling_continuous hA hneA)) f
    (fun _ _ h => ordinalCeiling_mono hA hneA h) hs
  exact ⟨q, hq, fun y => congrArg Subtype.val (hr y)⟩

end Posets
