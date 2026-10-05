import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! A genuine continuous parametrix for an operator with closed range,
finite-dimensional kernel, and finite-dimensional cokernel. Both errors
have actual finite-dimensional ranges. No index or Fredholm structure
is postulated. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

theorem exists_finiteDefect_parametrix
    (T : X →L[𝕜] Y) (hR : IsClosed (LinearMap.range T.toLinearMap : Set Y))
    [FiniteDimensional 𝕜 (LinearMap.ker T.toLinearMap)]
    [FiniteDimensional 𝕜 (Y ⧸ LinearMap.range T.toLinearMap)] :
    ∃ B : Y →L[𝕜] X,
      FiniteDimensional 𝕜 (LinearMap.range (B.comp T - ContinuousLinearMap.id 𝕜 X).toLinearMap) ∧
      FiniteDimensional 𝕜 (LinearMap.range (T.comp B - ContinuousLinearMap.id 𝕜 Y).toLinearMap) := by
  let K := LinearMap.ker T.toLinearMap
  let R := LinearMap.range T.toLinearMap
  have hK : K.ClosedComplemented := Submodule.ClosedComplemented.of_finiteDimensional K
  obtain ⟨P, hP⟩ := hK
  have hRc : R.ClosedComplemented := Submodule.ClosedComplemented.of_quotient_finiteDimensional hR
  obtain ⟨Q, hQ⟩ := hRc
  letI : CompleteSpace R := hR.completeSpace_coe
  let A : X →L[𝕜] R × K := T.rangeRestrict.prod P
  have hAi : Function.Injective A := by
    intro x y hxy
    have ht : T x = T y := congrArg (fun z : R × K => z.1.val) hxy
    have hp : P x = P y := congrArg Prod.snd hxy
    have hk : x - y ∈ K := by change T (x-y) = 0; rw [map_sub, ht, sub_self]
    have hh := hP ⟨x-y, hk⟩
    have hh0 : P (x-y) = 0 := by rw [map_sub, hp, sub_self]
    have : x-y = 0 := by
      have hv := congrArg Subtype.val hh
      simpa only [hh0, ZeroMemClass.coe_zero] using hv.symm
    exact sub_eq_zero.mp this
  have hAs : Function.Surjective A := by
    rintro ⟨y,z⟩
    obtain ⟨x,hx⟩ := y.property
    refine ⟨x - (P x).val + z.val, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change T (x - (P x).val + z.val) = y.val
      have hPx : T (P x).val = 0 := (P x).property
      have hz : T z.val = 0 := z.property
      rw [map_add, map_sub, hPx, hz, sub_zero, add_zero]
      exact hx
    · change P (x - (P x).val + z.val) = z
      rw [map_add, map_sub, hP, hP, sub_self, zero_add]
  let e : X ≃L[𝕜] R × K := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hAi) (LinearMap.range_eq_top.mpr hAs)
  let B : Y →L[𝕜] X := e.symm.toContinuousLinearMap.comp (Q.prod 0)
  have hTB (y : Y) : T (B y) = (Q y).val := by
    have h := congrArg (fun z : R × K => z.1.val) (e.apply_symm_apply (Q y, 0))
    exact h
  refine ⟨B, ?_, ?_⟩
  · apply Submodule.finiteDimensional_of_le (S₂ := K)
    rintro _ ⟨x,rfl⟩
    change T (B (T x) - x) = 0
    rw [map_sub, hTB]
    have h := congrArg Subtype.val (hQ (T.rangeRestrict x))
    change (Q (T x)).val = T x at h
    rw [h, sub_self]
  · letI : FiniteDimensional 𝕜 (LinearMap.ker Q.toLinearMap) :=
      (R.quotientEquivOfIsCompl (LinearMap.ker Q.toLinearMap)
        (LinearMap.isCompl_of_proj hQ)).finiteDimensional
    apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.ker Q.toLinearMap)
    rintro _ ⟨y,rfl⟩
    change Q (T (B y) - y) = 0
    rw [map_sub, hTB, hQ, sub_self]

end ThesisCommon
