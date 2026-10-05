import Posets.ScalarUniqueness
import Mathlib.Topology.MetricSpace.Antilipschitz

noncomputable section
open TopologicalSpace
namespace Posets
variable {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The scalar coefficient is contractive also between different spaces.
If the perturbation had smaller norm than the scalar, the separable remainder
would be bounded below, embedding the nonseparable domain in a separable range. -/
theorem scalar_norm_le_between (hE : ¬ SeparableSpace E)
    (ι : E →L[𝕜] F) (hι : Isometry ι) {T S : E →L[𝕜] F} {a : 𝕜}
    (hS : HasSeparableRange 𝕜 E F S) (hT : T = a • ι + S) : ‖a‖ ≤ ‖T‖ := by
  by_contra h
  have hpos : 0 < ‖a‖ - ‖T‖ := sub_pos.mpr (lt_of_not_ge h)
  have hιnorm (x : E) : ‖ι x‖ = ‖x‖ := by
    simpa [dist_eq_norm] using hι.dist_eq x 0
  have hlower (x : E) : (‖a‖ - ‖T‖) * ‖x‖ ≤ ‖S x‖ := by
    have heq : a • ι x = T x - S x := by
      rw [hT]
      simp
    have hnorm := norm_sub_le (T x) (S x)
    rw [← heq, norm_smul, hιnorm] at hnorm
    have hupper := T.le_opNorm x
    nlinarith
  have hanti : AntilipschitzWith ⟨(‖a‖ - ‖T‖)⁻¹, inv_nonneg.mpr hpos.le⟩ S := by
    apply S.antilipschitz_of_bound
    intro x
    change ‖x‖ ≤ (‖a‖ - ‖T‖)⁻¹ * ‖S x‖
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm] using hlower x)
  have hsep := (hanti.isUniformEmbedding S.uniformContinuous).isEmbedding.isSeparable_preimage hS
  have heq : S ⁻¹' Set.range S = Set.univ := Set.eq_univ_of_forall (fun x => ⟨x, rfl⟩)
  rw [heq] at hsep
  exact hE (isSeparable_univ_iff.mp hsep)

/-- The ordered-pair decomposition hypothesis with the remainder written
canonically. This is obtained from FewOperators below, not an extra axiom. -/
def ScalarDecompositions (ι : E →L[𝕜] F) : Prop :=
  ∀ T : E →L[𝕜] F, ∃ a : 𝕜, HasSeparableRange 𝕜 E F (T - a • ι)

variable {ι : E →L[𝕜] F}

def scalarBetween (H : ScalarDecompositions ι) (T : E →L[𝕜] F) : 𝕜 :=
  Classical.choose (H T)

theorem scalarBetween_remainder (H : ScalarDecompositions ι) (T : E →L[𝕜] F) :
    HasSeparableRange 𝕜 E F (T - scalarBetween H T • ι) := Classical.choose_spec (H T)

theorem scalarBetween_eq (hE : ¬ SeparableSpace E) (hι : Isometry ι)
    (H : ScalarDecompositions ι) (T : E →L[𝕜] F) (a : 𝕜)
    (hrem : HasSeparableRange 𝕜 E F (T - a • ι)) : scalarBetween H T = a :=
  (scalar_decomposition_unique_between (T := T) hE ι hι (scalarBetween_remainder H T) hrem
    (by abel) (by abel)).1

theorem scalarBetween_add (hE : ¬ SeparableSpace E) (hι : Isometry ι)
    (H : ScalarDecompositions ι) (S T : E →L[𝕜] F) :
    scalarBetween H (S + T) = scalarBetween H S + scalarBetween H T := by
  apply scalarBetween_eq hE hι H
  convert (scalarBetween_remainder H S).add (scalarBetween_remainder H T) using 1
  rw [add_smul]
  abel

theorem scalarBetween_smul (hE : ¬ SeparableSpace E) (hι : Isometry ι)
    (H : ScalarDecompositions ι) (a : 𝕜) (T : E →L[𝕜] F) :
    scalarBetween H (a • T) = a • scalarBetween H T := by
  apply scalarBetween_eq hE hι H
  convert (scalarBetween_remainder H T).smul a using 1
  simp [smul_sub, smul_smul, smul_eq_mul]

theorem scalarBetween_norm_le (hE : ¬ SeparableSpace E) (hι : Isometry ι)
    (H : ScalarDecompositions ι) (T : E →L[𝕜] F) : ‖scalarBetween H T‖ ≤ ‖T‖ :=
  scalar_norm_le_between hE ι hι (scalarBetween_remainder H T) (by abel)

/-- The actual bounded scalar extraction functional for an ordered pair. -/
def scalarBetweenL (hE : ¬ SeparableSpace E) (hι : Isometry ι)
    (H : ScalarDecompositions ι) : (E →L[𝕜] F) →L[𝕜] 𝕜 :=
  ({toFun := scalarBetween H
    map_add' := scalarBetween_add hE hι H
    map_smul' := scalarBetween_smul hE hι H} : (E →L[𝕜] F) →ₗ[𝕜] 𝕜).mkContinuous
      1 (fun T => by simpa using scalarBetween_norm_le hE hι H T)

theorem scalarBetween_eq_zero_iff (hE : ¬ SeparableSpace E) (hι : Isometry ι)
    (H : ScalarDecompositions ι) (T : E →L[𝕜] F) :
    scalarBetween H T = 0 ↔ HasSeparableRange 𝕜 E F T := by
  constructor
  · intro h
    simpa [h] using scalarBetween_remainder H T
  · intro h
    exact scalarBetween_eq hE hι H T 0 (by simpa using h)

theorem scalarBetween_embedding (hE : ¬ SeparableSpace E) (hι : Isometry ι)
    (H : ScalarDecompositions ι) : scalarBetween H ι = 1 :=
  scalarBetween_eq hE hι H ι 1 (by simpa using JFA.hasSeparableRange_zero (𝕜 := 𝕜) (E := E) (F := F))

theorem norm_scalarBetweenL (hE : ¬ SeparableSpace E) (hι : Isometry ι)
    (H : ScalarDecompositions ι) : ‖scalarBetweenL hE hι H‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun T => by simpa [scalarBetweenL] using scalarBetween_norm_le hE hι H T)
  · have hi : ‖ι‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simpa [dist_eq_norm] using (hι.dist_eq x 0).le
    have h := (scalarBetweenL hE hι H).le_opNorm ι
    change ‖scalarBetween H ι‖ ≤ _ at h
    rw [scalarBetween_embedding hE hι H, norm_one] at h
    exact h.trans (by simpa using mul_le_mul_of_nonneg_left hi (norm_nonneg (scalarBetweenL hE hι H)))

theorem fewOperators_scalarDecompositions {P : Type*} [PartialOrder P] {X : P → Type*}
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι)
    {s t : P} (hst : s ≤ t) : ScalarDecompositions (ι s t) := by
  intro T
  obtain ⟨a, S, hS, hT⟩ := h.2.2.2.2.1 s t hst T
  refine ⟨a, ?_⟩
  simpa [hT] using hS

/-- The scalar functional supplied by the paper's original FewOperators hypothesis. -/
def fewOperatorCoefficient {P : Type*} [PartialOrder P] {X : P → Type*}
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι)
    {s t : P} (hst : s ≤ t) : (X s →L[𝕜] X t) →L[𝕜] 𝕜 :=
  scalarBetweenL (h.1 s) (h.2.1 s t hst) (fewOperators_scalarDecompositions h hst)

end Posets
