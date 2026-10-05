import ThesisCommon.Analysis.BooleanDensityHomogeneity
import Mathlib.Order.Hom.Set

/-! Principal-ideal density and density homogeneity are invariant under
actual order isomorphisms that are homeomorphisms. -/
noncomputable section
open Set
namespace ThesisCommon
universe u
variable {A B : Type u} [Lattice A] [Lattice B] [OrderBot A] [OrderBot B]
  [TopologicalSpace A] [TopologicalSpace B] [ContinuousInf A] [ContinuousInf B]

def orderIsoPrincipalHomeomorph (φ : A ≃o B) (hφ : Continuous φ) (hφi : Continuous φ.symm) (a : A) :
    Iic a ≃ₜ Iic (φ a) where
  toEquiv := (φ.Iic a).toEquiv
  continuous_toFun := (hφ.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (hφi.comp continuous_subtype_val).subtype_mk _

theorem principalDensity_orderIso (φ : A ≃o B) (hφ : Continuous φ) (hφi : Continuous φ.symm) (a : A) :
    principalDensity (φ a) = principalDensity a :=
  (topologicalDensity_eq_of_homeomorph (orderIsoPrincipalHomeomorph φ hφ hφi a)).symm

theorem IsDensityHomogeneous.orderIso {a : A} (ha : IsDensityHomogeneous a)
    (φ : A ≃o B) (hφ : Continuous φ) (hφi : Continuous φ.symm) : IsDensityHomogeneous (φ a) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply ha.1
    apply φ.injective
    simpa only [map_bot] using h
  · intro b hb hba
    have hb' : φ.symm b ≠ ⊥ := by
      intro h
      apply hb
      simpa only [OrderIso.apply_symm_apply, map_bot] using congrArg φ h
    have hle : φ.symm b ≤ a := φ.symm_apply_le.mpr hba
    have h := ha.2 (φ.symm b) hb' hle
    rw [← principalDensity_orderIso φ hφ hφi (φ.symm b),
      ← principalDensity_orderIso φ hφ hφi a] at h
    simpa only [OrderIso.apply_symm_apply] using h

theorem isDensityHomogeneous_orderIso_iff (φ : A ≃o B)
    (hφ : Continuous φ) (hφi : Continuous φ.symm) (a : A) :
    IsDensityHomogeneous (φ a) ↔ IsDensityHomogeneous a := by
  constructor
  · intro h
    simpa only [OrderIso.symm_apply_apply] using h.orderIso φ.symm hφi hφ
  · intro h
    exact h.orderIso φ hφ hφi

end ThesisCommon
