import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-! A neighborhood retraction carrying an actual Lipschitz bound. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E]

structure LipschitzNeighborhoodRetraction (s : Set E) where
  domain : Set E
  isOpen_domain : IsOpen domain
  subset_domain : s ⊆ domain
  retract : C(domain, s)
  constant : ℝ≥0
  lipschitz : LipschitzWith constant retract
  fixes : ∀ x : s, retract ⟨x.val, subset_domain x.property⟩ = x

def LipschitzNeighborhoodRetraction.of_subset_interior {s A : Set E}
    (r : A → s) {L : ℝ≥0} (hL : LipschitzWith L r)
    (hA : s ⊆ interior A)
    (hFix : ∀ x : s, r ⟨x.val, interior_subset (hA x.property)⟩ = x) :
    LipschitzNeighborhoodRetraction s where
  domain := interior A
  isOpen_domain := isOpen_interior
  subset_domain := hA
  retract := ⟨fun x => r ⟨x.val, interior_subset x.property⟩,
    (hL.comp (LipschitzWith.subtype_val _ |>.subtype_mk
      (fun x => interior_subset x.property))).continuous⟩
  constant := L
  lipschitz := by
    have h := (LipschitzWith.subtype_val (interior A)).subtype_mk
      (fun x => interior_subset x.property)
    simpa only [mul_one] using hL.comp h
  fixes := hFix

end BanachIsometric.SingularPrism
