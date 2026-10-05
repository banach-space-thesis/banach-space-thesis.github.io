import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Prod

/-! The transverse space to the image of a subspace under an invertible
operator is genuinely isomorphic to the original quotient. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [DivisionRing 𝕜] [AddCommGroup X] [Module 𝕜 X]

def transverseQuotientEquiv (e : X ≃ₗ[𝕜] X) (E Z : Submodule 𝕜 X)
    (h : Function.Bijective ((e.toLinearMap.comp E.subtype).coprod Z.subtype)) :
    Z ≃ₗ[𝕜] (X ⧸ E) := by
  let L : Z →ₗ[𝕜] (X ⧸ E) := E.mkQ.comp (e.symm.toLinearMap.comp Z.subtype)
  apply LinearEquiv.ofBijective L
  constructor
  · have hz : ∀ z, L z = 0 → z = 0 := by
      intro z hz
      have hm : e.symm z.val ∈ E := (Submodule.Quotient.mk_eq_zero E).mp hz
      let x : E := ⟨e.symm z.val,hm⟩
      have he : ((e.toLinearMap.comp E.subtype).coprod Z.subtype) (x,0) =
          ((e.toLinearMap.comp E.subtype).coprod Z.subtype) (0,z) := by
        change e (e.symm z.val) + 0 = e 0 + z.val
        rw [e.apply_symm_apply,map_zero,add_zero,zero_add]
      exact (congrArg Prod.snd (h.1 he)).symm
    intro z w hzw
    exact sub_eq_zero.mp (hz (z-w) (by rw [map_sub,hzw,sub_self]))
  · intro y
    obtain ⟨x,rfl⟩ := E.mkQ_surjective y
    obtain ⟨⟨v,z⟩,hz⟩ := h.2 (e x)
    refine ⟨z,?_⟩
    have he : v.val + e.symm z.val = x := by
      have hh := congrArg e.symm hz
      change e.symm (e v.val + z.val) = e.symm (e x) at hh
      simpa only [map_add,e.symm_apply_apply] using hh
    have hh := congrArg E.mkQ he
    have hv : E.mkQ v.val = 0 := (Submodule.Quotient.mk_eq_zero E).mpr v.property
    rw [map_add, hv, zero_add] at hh
    exact hh

end ThesisCommon
