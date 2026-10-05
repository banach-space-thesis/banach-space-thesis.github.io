import ThesisCommon.Analysis.StrictlySingularFiniteCoordinates
import Mathlib.Topology.MetricSpace.Closeds

/-! Composition and norm closure for the actual bounded-below-subspace
definition of strict singularity. These proofs do not assume ideal closure. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem IsStrictlySingularOperator.zero :
    IsStrictlySingularOperator (0 : X →L[𝕜] X) := by
  intro E hE
  obtain ⟨c,hc,hb⟩ := hE
  have hz : ∀ x : E, x = 0 := by
    intro x
    apply Subtype.ext
    apply norm_eq_zero.mp
    have hh := hb x
    simp only [ContinuousLinearMap.zero_apply, norm_zero] at hh
    change c * ‖x.val‖ ≤ 0 at hh
    have hn : ‖x.val‖ ≤ 0 := by nlinarith
    exact le_antisymm hn (norm_nonneg _)
  letI : Subsingleton E := ⟨fun x y => (hz x).trans (hz y).symm⟩
  infer_instance

theorem IsStrictlySingularOperator.comp_left
    {T : X →L[𝕜] X} (hT : IsStrictlySingularOperator T) (S : X →L[𝕜] X) :
    IsStrictlySingularOperator (S.comp T) := by
  intro E hE
  obtain ⟨c,hc,hb⟩ := hE
  apply hT E
  have hd : 0 < ‖S‖+1 := by positivity
  refine ⟨c/(‖S‖+1), div_pos hc hd, ?_⟩
  intro x
  change (c/(‖S‖+1)) * ‖x.val‖ ≤ ‖T x.val‖
  have hh := (hb x).trans (S.le_opNorm (T x.val))
  change c * ‖x.val‖ ≤ ‖S‖ * ‖T x.val‖ at hh
  have hm : c * ‖x.val‖ ≤ (‖S‖+1) * ‖T x.val‖ := by nlinarith [norm_nonneg (T x.val)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  nlinarith

theorem IsStrictlySingularOperator.comp_right
    {T : X →L[𝕜] X} (hT : IsStrictlySingularOperator T) (S : X →L[𝕜] X) :
    IsStrictlySingularOperator (T.comp S) := by
  intro E hE
  obtain ⟨c,hc,hb⟩ := hE
  let f : E →ₗ[𝕜] E.map S.toLinearMap :=
    (S.toLinearMap.comp E.subtype).codRestrict _ (fun x => ⟨x.val,x.property,rfl⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    have hs : S (x.val-y.val) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    have hh := hb (x-y)
    change c * ‖x.val-y.val‖ ≤ ‖T (S (x.val-y.val))‖ at hh
    rw [hs, map_zero, norm_zero] at hh
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (by nlinarith) (norm_nonneg _)
  have hF : FiniteDimensional 𝕜 (E.map S.toLinearMap) := by
    apply hT
    have hd : 0 < ‖S‖+1 := by positivity
    refine ⟨c/(‖S‖+1), div_pos hc hd, ?_⟩
    intro y
    change (c/(‖S‖+1)) * ‖y.val‖ ≤ ‖T y.val‖
    obtain ⟨x,hx,hxy⟩ := y.property
    have hh := hb ⟨x,hx⟩
    have hop := S.le_opNorm x
    change S x = y.val at hxy
    change c * ‖x‖ ≤ ‖T (S x)‖ at hh
    rw [hxy] at hh hop
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith [norm_nonneg x, norm_nonneg (T y.val)]
  letI := hF
  exact FiniteDimensional.of_injective f hf

theorem IsStrictlySingularOperator.smul
    {T : X →L[𝕜] X} (hT : IsStrictlySingularOperator T) (a : 𝕜) :
    IsStrictlySingularOperator (a • T) := by
  convert hT.comp_left (a • ContinuousLinearMap.id 𝕜 X) using 1

theorem IsStrictlySingularOperator.neg
    {T : X →L[𝕜] X} (hT : IsStrictlySingularOperator T) :
    IsStrictlySingularOperator (-T) := by
  simpa only [neg_one_smul] using hT.smul (-1)

theorem isClosed_setOf_isStrictlySingularOperator :
    IsClosed {T : X →L[𝕜] X | IsStrictlySingularOperator T} := by
  rw [← closure_subset_iff_isClosed]
  intro T hT E hE
  obtain ⟨c,hc,hb⟩ := hE
  obtain ⟨S,hS,hST⟩ := Metric.mem_closure_iff.mp hT (c/2) (by positivity)
  apply hS E
  refine ⟨c/2, by positivity, ?_⟩
  intro x
  change (c/2) * ‖x.val‖ ≤ ‖S x.val‖
  have he := (T-S).le_opNorm x.val
  simp only [ContinuousLinearMap.sub_apply] at he
  have ht := norm_le_insert' (T x.val) (S x.val)
  rw [dist_eq_norm] at hST
  have hm := mul_le_mul_of_nonneg_right hST.le (norm_nonneg x.val)
  have hh := hb x
  change c * ‖x.val‖ ≤ ‖T x.val‖ at hh
  nlinarith

theorem not_strictlySingular_of_norm_sub_smul_id_lt
    (hX : ¬ FiniteDimensional 𝕜 X) (T : X →L[𝕜] X) (a : 𝕜)
    (h : ‖T-a • ContinuousLinearMap.id 𝕜 X‖ < ‖a‖) :
    ¬ IsStrictlySingularOperator T := by
  intro hT
  have hfin := hT ⊤ ⟨‖a‖-‖T-a • ContinuousLinearMap.id 𝕜 X‖, sub_pos.mpr h, by
    intro x
    change (‖a‖-‖T-a • ContinuousLinearMap.id 𝕜 X‖) * ‖x.val‖ ≤ ‖T x.val‖
    have he := (T-a • ContinuousLinearMap.id 𝕜 X).le_opNorm x.val
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply] at he
    have ht := norm_le_insert' (a • x.val) (T x.val)
    rw [norm_smul, norm_sub_rev] at ht
    nlinarith⟩
  letI := hfin
  exact hX (FiniteDimensional.of_injective (Submodule.topEquiv.symm :
    X ≃ₗ[𝕜] (⊤ : Submodule 𝕜 X)).toLinearMap Submodule.topEquiv.symm.injective)

theorem not_strictlySingular_id (hX : ¬ FiniteDimensional 𝕜 X) :
    ¬ IsStrictlySingularOperator (ContinuousLinearMap.id 𝕜 X) := by
  apply not_strictlySingular_of_norm_sub_smul_id_lt hX _ (1 : 𝕜)
  simp

end ThesisCommon
