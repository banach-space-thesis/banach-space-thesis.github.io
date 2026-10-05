import JFA.CompactIdeal
import Mathlib.Analysis.Normed.Module.Dual

/-! Every nonzero two-sided operator ideal contains every rank-one operator.
The two multipliers are constructed using a Hahn–Banach functional normalised
at a nonzero value of the given operator. -/

noncomputable section
open TopologicalSpace Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem smulRight_mem_ideal_of_ne_zero {I : Set (E →L[𝕜] E)}
    (hI : IsClosedOperatorIdeal 𝕜 E I) {T : E →L[𝕜] E} (hTI : T ∈ I) (hT : T ≠ 0)
    (η : E →L[𝕜] 𝕜) (v : E) : η.smulRight v ∈ I := by
  have hex : ∃ x, T x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hT (ContinuousLinearMap.ext h)
  obtain ⟨x, hx⟩ := hex
  obtain ⟨ψ, _, hψ⟩ := exists_dual_vector 𝕜 (T x) hx
  have hψne : ψ (T x) ≠ 0 := by
    rw [hψ]
    simpa only [RCLike.ofReal_ne_zero] using norm_ne_zero_iff.mpr hx
  let φ : E →L[𝕜] 𝕜 := (ψ (T x))⁻¹ • ψ
  have hφ : φ (T x) = 1 := by
    change (ψ (T x))⁻¹ * ψ (T x) = 1
    exact inv_mul_cancel₀ hψne
  have hin := (hI.2.2.2.2 (η.smulRight x) T hTI).2
  have hout := (hI.2.2.2.2 (φ.smulRight v) (T.comp (η.smulRight x)) hin).1
  have heq : (φ.smulRight v).comp (T.comp (η.smulRight x)) = η.smulRight v := by
    apply ContinuousLinearMap.ext
    intro y
    change φ (T (η y • x)) • v = η y • v
    rw [map_smul, map_smul, hφ, smul_eq_mul, mul_one]
  exact heq ▸ hout

end JFA
