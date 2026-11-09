import ThesisCommon.Analysis.MilutinCantorEmbedding
import ThesisCommon.Analysis.MilutinCantorExtension
import ThesisCommon.Analysis.MilutinCantorAveraging
import ThesisCommon.Analysis.IntervalCZeroEquiv
import ThesisCommon.Analysis.MutualRetractDecomposition

/-! Milutin's isomorphism theorem for every uncountable compact metric space,
over real or complex scalars. The two complemented embeddings are composed
from actual Cantor embeddings, contractive extensions, and regular averaging
operators. The checked Pełczyński decomposition argument then supplies the
bounded linear isomorphism with C[0,1]. -/

noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

/-- If a compact Hausdorff space Y contains Cantor space, every nonempty
compact metric C(K) is a contractively complemented subspace of C(Y). -/
theorem milutin_compactMetric_contractive_retract
    (K : Type*) [MetricSpace K] [CompactSpace K] [Nonempty K]
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (e : C((ℕ → Bool), Y)) (he : Function.Injective e) :
    ∃ P : C(Y, 𝕜) →L[𝕜] C(K, 𝕜), ∃ J : C(K, 𝕜) →L[𝕜] C(Y, 𝕜),
      ‖P‖ ≤ 1 ∧ ‖J‖ ≤ 1 ∧ P.comp J = ContinuousLinearMap.id 𝕜 C(K, 𝕜) := by
  obtain ⟨q, _, A, hA, hAJ⟩ := milutin_binary_cantor_regular_averaging (𝕜 := 𝕜) K
  let P : C(Y, 𝕜) →L[𝕜] C(K, 𝕜) := A.comp (continuousMapPullback e)
  let J : C(K, 𝕜) →L[𝕜] C(Y, 𝕜) :=
    (milutinCantorExtend (𝕜 := 𝕜) e he).comp (continuousMapPullback q)
  refine ⟨P, J, ?_, ?_, ?_⟩
  · change ‖A.comp (continuousMapPullback e)‖ ≤ 1
    calc
      ‖A.comp (continuousMapPullback e)‖ ≤ ‖A‖ * ‖continuousMapPullback (𝕜 := 𝕜) e‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 := by rw [hA, one_mul]; exact norm_continuousMapPullback_le e
  · change ‖(milutinCantorExtend (𝕜 := 𝕜) e he).comp (continuousMapPullback q)‖ ≤ 1
    calc
      _ ≤ ‖milutinCantorExtend (𝕜 := 𝕜) e he‖ * ‖continuousMapPullback (𝕜 := 𝕜) q‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_milutinCantorExtend_le (𝕜 := 𝕜) e he)
        (norm_continuousMapPullback_le (𝕜 := 𝕜) q) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  · apply ContinuousLinearMap.ext
    intro f
    change A (continuousMapPullback e (milutinCantorExtend e he
      (continuousMapPullback q f))) = f
    have hE := DFunLike.congr_fun (milutinCantorExtend_right_inverse (𝕜 := 𝕜) e he)
      (continuousMapPullback q f)
    change continuousMapPullback e (milutinCantorExtend e he
      (continuousMapPullback q f)) = continuousMapPullback q f at hE
    rw [hE]
    exact DFunLike.congr_fun hAJ f

/-- The uncountable compact metric case of Milutin's theorem, with no
isomorphism or extension hypothesis left over. -/
theorem milutin_compactMetric_equiv_interval (K : Type*)
    [MetricSpace K] [CompactSpace K] [Uncountable K] :
    Nonempty (C(K, 𝕜) ≃L[𝕜] IntervalContinuous 𝕜) := by
  obtain ⟨eI, heI⟩ := milutin_exists_interval_cantor_embedding
  obtain ⟨eK, heK⟩ := milutin_exists_cantor_embedding K
  obtain ⟨PI, JI, _, _, hI⟩ :=
    milutin_compactMetric_contractive_retract (𝕜 := 𝕜) K eI heI
  obtain ⟨PK, JK, _, _, hK⟩ :=
    milutin_compactMetric_contractive_retract (𝕜 := 𝕜) UnitInterval eK heK
  exact equiv_of_cZero_selfSimilar_mutual_retracts (𝕜 := 𝕜)
    (X := IntervalContinuous 𝕜) (Y := C(K, 𝕜))
    (intervalCZeroEquiv (𝕜 := 𝕜)) PI JI PK JK hI hK

/-- A chosen bounded linear Milutin isomorphism on actual continuous maps. -/
def milutinCompactMetricEquivInterval (K : Type*)
    [MetricSpace K] [CompactSpace K] [Uncountable K] :
    C(K, 𝕜) ≃L[𝕜] IntervalContinuous 𝕜 :=
  Classical.choice (milutin_compactMetric_equiv_interval (𝕜 := 𝕜) K)

end ThesisCommon
