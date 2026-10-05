import ThesisCommon.Analysis.JamesShrinkingBasis
import ThesisCommon.Analysis.JamesRawLimits
import Mathlib.Analysis.Normed.Module.Dual

/-! The coordinate sequence of an actual continuous bidual functional has
bounded James variation and hence a scalar limit. The finite coordinate
sections are bounded using Hahn–Banach and the contractive initial maps.
-/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

def jamesBidualCoordinate (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) (n : ℕ) : 𝕜 :=
  ξ (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n)

theorem jamesBidualFinite_pairing
    (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    (φ : JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) (N : ℕ) :
    φ (jamesFiniteSequence p hp (jamesBidualCoordinate p ξ) N) =
      ξ (φ.comp (JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) N)) := by
  rw [james_functional_initial_eq_sum p hp]
  simp only [jamesFiniteSequence, map_sum, map_smul, smul_eq_mul, jamesBidualCoordinate]
  apply Finset.sum_congr rfl
  intro n _
  exact mul_comm _ _

theorem jamesBidualFinite_norm_le
    (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) (N : ℕ) :
    ‖jamesFiniteSequence p hp (jamesBidualCoordinate p ξ) N‖ ≤ ‖ξ‖ := by
  refine NormedSpace.norm_le_dual_bound 𝕜
    (jamesFiniteSequence p hp (jamesBidualCoordinate p ξ) N) (M := ‖ξ‖) (norm_nonneg ξ) ?_
  intro φ
  rw [jamesBidualFinite_pairing p hp]
  apply (ξ.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left
      (JamesSequenceSpace.norm_initial_le (𝕜 := 𝕜) (p := p) N) (norm_nonneg φ)).trans_eq
        (mul_one _))

include hp in
theorem jamesBidual_path_norm_le
    (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) (s : JamesPath) :
    ‖jamesRawPath p s (jamesBidualCoordinate p ξ)‖ ≤ ‖ξ‖ := by
  rw [jamesRawPath_eq_finite p hp s _ (s.index (Fin.last s.length)) le_rfl]
  exact (JamesSequenceSpace.path_norm_le _ s).trans (jamesBidualFinite_norm_le p hp ξ _)

include hp in
theorem jamesBidualCoordinate_exists_limit
    (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    ∃ L : 𝕜, Tendsto (jamesBidualCoordinate p ξ) atTop (𝓝 L) :=
  jamesRawPath_exists_limit p hp _ (jamesBidual_path_norm_le p hp ξ)

def jamesBidualLimit (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) : 𝕜 :=
  (jamesBidualCoordinate_exists_limit p hp ξ).choose

theorem jamesBidualCoordinate_tendsto
    (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    Tendsto (jamesBidualCoordinate p ξ) atTop (𝓝 (jamesBidualLimit p hp ξ)) :=
  (jamesBidualCoordinate_exists_limit p hp ξ).choose_spec

def jamesBidualNullPart (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    JamesSequenceSpace 𝕜 p :=
  jamesOfConvergentVariation p (jamesBidualCoordinate p ξ) (jamesBidualLimit p hp ξ)
    (jamesBidualCoordinate_tendsto p hp ξ) (jamesBidual_path_norm_le p hp ξ)

@[simp] theorem jamesBidualNullPart_apply
    (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) (n : ℕ) :
    jamesBidualNullPart p hp ξ n = jamesBidualCoordinate p ξ n - jamesBidualLimit p hp ξ := rfl

theorem jamesBidualNullPart_norm_le
    (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) : ‖jamesBidualNullPart p hp ξ‖ ≤ ‖ξ‖ :=
  jamesOfConvergentVariation_norm_le p _ _ _ _

end ThesisCommon
