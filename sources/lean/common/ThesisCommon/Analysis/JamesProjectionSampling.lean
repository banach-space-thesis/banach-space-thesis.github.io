import ThesisCommon.Analysis.JamesAndrewFactorization
import ThesisCommon.Analysis.ProjectionDecomposition

/-! A non-weakly-compact projection has a James copy whose reading map is
an actual invertible correction of coordinate sampling. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ⊤)
  (hpl : 1 < p.val.toReal)

theorem james_projection_scalar_eq_one
    (P : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
    (hP : P.comp P = P) (hnot : ¬ IsWeaklyCompactOperator P) :
    jamesOperatorScalar p hp hpl P = 1 := by
  have hn : jamesOperatorScalar p hp hpl P ≠ 0 :=
    fun h => hnot ((james_weaklyCompact_iff_scalar_eq_zero p hp hpl P).mpr h)
  have he := congrArg (jamesOperatorScalar p hp hpl) hP
  rw [jamesOperatorScalar_comp] at he
  have hz : jamesOperatorScalar p hp hpl P * (jamesOperatorScalar p hp hpl P - 1) = 0 := by
    rw [mul_sub, mul_one, he, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hn)

include hpl in
theorem james_nonweaklyCompact_projection_sampling_split
    (P : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
    (hP : P.comp P = P) (hnot : ¬ IsWeaklyCompactOperator P) :
    ∃ (α : ℕ → ℕ) (hα : StrictMono α)
      (V : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
      (E : JamesSequenceSpace 𝕜 p ≃L[𝕜] JamesSequenceSpace 𝕜 p),
      (E.toContinuousLinearMap.comp (jamesSample (𝕜 := 𝕜) p hp α hα)).comp (P.comp V) =
        ContinuousLinearMap.id 𝕜 _ ∧ ‖V‖ ≤ 1 ∧ ‖E.toContinuousLinearMap‖ ≤ 2 := by
  obtain ⟨α, β, hα, hβ, E, heq, hnorm⟩ := james_scalar_one_factors_with_sampling p hp hpl P
    (james_projection_scalar_eq_one p hp hpl P hP hnot)
  exact ⟨α, hα, jamesPrefixRepeat (𝕜 := 𝕜) p hp β hβ, E,
    by simpa only [ContinuousLinearMap.comp_assoc] using heq,
    jamesPrefixRepeat_norm_le p hp β hβ, hnorm⟩

theorem james_corrected_sampling_ker (α : ℕ → ℕ) (hα : StrictMono α)
    (E : JamesSequenceSpace 𝕜 p ≃L[𝕜] JamesSequenceSpace 𝕜 p) :
    LinearMap.ker (E.toContinuousLinearMap.comp (jamesSample (𝕜 := 𝕜) p hp α hα)).toLinearMap =
      LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp α hα).toLinearMap := by
  ext x
  change E (jamesSample (𝕜 := 𝕜) p hp α hα x) = 0 ↔
    jamesSample (𝕜 := 𝕜) p hp α hα x = 0
  exact E.map_eq_zero_iff

end ThesisCommon
