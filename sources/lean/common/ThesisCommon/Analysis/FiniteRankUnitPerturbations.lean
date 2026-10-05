import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! Scalar perturbations of finite-rank operators are invertible outside
an actual finite set. The proof restricts to the genuine range, and then
solves the ambient equation explicitly; no Fredholm assertion is used. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

def finiteRankRangeEnd (F : X →L[𝕜] X) :
    Module.End 𝕜 (LinearMap.range F.toLinearMap) :=
  F.toLinearMap.rangeRestrict.comp (LinearMap.range F.toLinearMap).subtype

theorem isUnit_smul_id_sub_of_notMem_range_spectrum
    (F : X →L[𝕜] X) (z : 𝕜) (hz : z ≠ 0)
    (hs : z ∉ spectrum 𝕜 (finiteRankRangeEnd F)) :
    IsUnit (z • ContinuousLinearMap.id 𝕜 X-F) := by
  have hu := (Module.End.isUnit_iff _).mp (spectrum.notMem_iff.mp hs)
  let B : Module.End 𝕜 (LinearMap.range F.toLinearMap) :=
    z • LinearMap.id-finiteRankRangeEnd F
  have hB : Function.Bijective B := hu
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  constructor
  · intro x y hxy
    have he : z • (x-y)-F (x-y) = 0 := by
      change (z • ContinuousLinearMap.id 𝕜 X-F) (x-y) = 0
      rw [map_sub,hxy,sub_self]
    have hxyR : x-y ∈ LinearMap.range F.toLinearMap := by
      refine ⟨z⁻¹ • (x-y),?_⟩
      change F (z⁻¹ • (x-y)) = x-y
      rw [map_smul, ← sub_eq_zero.mp he, smul_smul, inv_mul_cancel₀ hz, one_smul]
    have hb : B ⟨x-y,hxyR⟩ = 0 := by
      apply Subtype.ext
      exact he
    have hh := hB.1 (hb.trans (map_zero B).symm)
    have hh' : x-y = 0 := congrArg Subtype.val hh
    exact sub_eq_zero.mp hh'
  · intro y
    obtain ⟨b,hb⟩ := hB.2 (F.toLinearMap.rangeRestrict y)
    have hb' : z • b.val-F b.val = F y := congrArg Subtype.val hb
    have hFy : F (y+b.val) = z • b.val := by
      rw [map_add, ← hb', sub_add_cancel]
    refine ⟨z⁻¹ • (y+b.val),?_⟩
    change z • (z⁻¹ • (y+b.val))-F (z⁻¹ • (y+b.val)) = y
    rw [map_smul, hFy, smul_smul, smul_smul, mul_inv_cancel₀ hz,
      inv_mul_cancel₀ hz, one_smul, one_smul, add_sub_cancel_right]

theorem exists_finite_exceptional_unit_smul_id_sub
    (F : X →L[𝕜] X) [FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap)] :
    ∃ s : Set 𝕜, s.Finite ∧ ∀ z, z ∉ s →
      IsUnit (z • ContinuousLinearMap.id 𝕜 X-F) := by
  refine ⟨insert 0 (spectrum 𝕜 (finiteRankRangeEnd F)),
    (Module.End.finite_spectrum _).insert 0,?_⟩
  intro z hz
  exact isUnit_smul_id_sub_of_notMem_range_spectrum F z
    (fun he => hz (Or.inl he)) (fun he => hz (Or.inr he))

end ThesisCommon
