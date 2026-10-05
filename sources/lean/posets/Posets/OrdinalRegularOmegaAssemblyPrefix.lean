import Posets.OrdinalRegularOmegaAssemblyGeometry
import JLMS.OrdinalTailConstancy

/-! A large compact ordinal coordinate image can be reduced to any prescribed
initial segment. Both maps are actual continuous maps and the section stays
in the original core; all pullback and reading norms remain one. -/
noncomputable section
open Set Topology
namespace Posets
open ThesisCommon
universe u v w
variable {H : Type v} {B : Type w} [TopologicalSpace H] [TopologicalSpace B]
  {η β : Ordinal.{u}}

def ordinalOmegaPrefixInclusion (h : β ≤ η) : C(OrdinalInterval β, OrdinalInterval η) :=
  ⟨fun x => ⟨x.val, x.property.1, x.property.2.trans h⟩,
    continuous_subtype_val.subtype_mk _⟩

def ordinalOmegaPrefixCoordinate (e : OrdinalInterval η ≃ₜ B) (p : C(H, B))
    (β : Ordinal.{u}) : C(H, OrdinalInterval β) :=
  (JLMS.ordinalIntervalClamp β).comp
    ⟨fun x => (e.symm (p x)).val,
      continuous_subtype_val.comp (e.symm.continuous.comp p.continuous)⟩

def ordinalOmegaPrefixSection (e : OrdinalInterval η ≃ₜ B) (q : C(B, H))
    (h : β ≤ η) : C(OrdinalInterval β, H) :=
  q.comp (ContinuousMap.comp ⟨e, e.continuous⟩ (ordinalOmegaPrefixInclusion h))

theorem ordinalOmegaPrefix_section (e : OrdinalInterval η ≃ₜ B) (p : C(H, B))
    (q : C(B, H)) (hq : Function.RightInverse q p) (h : β ≤ η) :
    Function.RightInverse (ordinalOmegaPrefixSection e q h)
      (ordinalOmegaPrefixCoordinate e p β) := by
  intro x
  change JLMS.ordinalIntervalClamp β (e.symm (p (q (e (ordinalOmegaPrefixInclusion h x))))).val = x
  rw [hq, e.symm_apply_apply]
  apply Subtype.ext
  exact min_eq_left x.property.2

theorem ordinalOmegaPrefixCoordinate_constant (e : OrdinalInterval η ≃ₜ B) (p : C(H, B))
    (β : Ordinal.{u}) {x y : H} (hxy : p x = p y) :
    ordinalOmegaPrefixCoordinate e p β x = ordinalOmegaPrefixCoordinate e p β y := by
  change JLMS.ordinalIntervalClamp β (e.symm (p x)).val =
    JLMS.ordinalIntervalClamp β (e.symm (p y)).val
  rw [hxy]

theorem ordinalOmegaPrefixSection_mem (e : OrdinalInterval η ≃ₜ B) (q : C(B, H))
    (h : β ≤ η) {C : Set H} (hq : ∀ x, q x ∈ C) (x : OrdinalInterval β) :
    ordinalOmegaPrefixSection e q h x ∈ C := hq _

theorem ordinalOmegaPrefixSection_range_subset (e : OrdinalInterval η ≃ₜ B) (q : C(B, H))
    (h : β ≤ η) : range (ordinalOmegaPrefixSection e q h) ⊆ range q := by
  rintro _ ⟨x, rfl⟩
  exact mem_range_self _

end Posets

