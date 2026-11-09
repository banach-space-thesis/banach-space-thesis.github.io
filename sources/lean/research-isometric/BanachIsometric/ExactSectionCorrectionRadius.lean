import BanachIsometric.ExactSectionCorrection
import Mathlib.Topology.MetricSpace.Thickening

/-! Compactness of the actual body group gives a single correction radius
for a finite exact-section atlas, in the original operator norm. -/

namespace BanachIsometric

open Set
open scoped NNReal

noncomputable section

namespace ExactSectionAtlas

variable {P E F : Type*} [PseudoMetricSpace P] [CompactSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    [CompactSpace (bodyAutomorphismGroup S)]
    (Z : ExactSectionAtlas S K H) (D : AmbientBodyRetraction S)

theorem exists_uniform_correction_radius (A : P → E →L[ℝ] F)
    (hA : ∀ a, Function.Injective (A a) ∧ LinearMap.range (A a).toLinearMap = H a ∧
      A a '' S = K ∩ (H a : Set F)) (I : Finset P) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : P → E →L[ℝ] F,
      (∀ a, dist (Y a) (A a) < δ) →
        ∀ i ∈ I, ∀ a ∈ Z.baseSet i, (Z.inverse i a).comp (Y a) ∈ D.domain := by
  classical
  let G : Set (E →L[ℝ] E) := (fun g : bodyAutomorphismGroup S => g.val.val) '' univ
  have hCont : Continuous (fun g : bodyAutomorphismGroup S => g.val.val) :=
    Units.isOpenEmbedding_val.continuous.comp continuous_subtype_val
  have hG : IsCompact G := isCompact_univ.image hCont
  have hGU : G ⊆ D.domain := by
    rintro _ ⟨g, _, rfl⟩
    exact D.contains g
  obtain ⟨ε, hε, hεU⟩ := hG.exists_thickening_subset_open D.isOpen_domain hGU
  have hbounds : ∀ i : P, ∃ M : ℝ≥0, ∀ a ∈ Z.baseSet i, ‖Z.inverse i a‖ ≤ M := by
    intro i
    obtain ⟨L, hL⟩ := Z.inverse_lipschitz i
    exact exists_norm_bound_of_lipschitzOn_compact_base hL i (Z.mem_baseSet i)
  choose B hB using hbounds
  let M := I.sup B
  let δ := ε / ((M : ℝ) + 1)
  have hMpos : 0 < (M : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hMpos
  refine ⟨δ, hδ, ?_⟩
  intro Y hY i hi a ha
  let t : ExactSectionSpace S K H := ⟨(a, A a), hA a⟩
  let g := (Z.actualTrivialization i t).2
  have hg : g.val.val = (Z.inverse i a).comp (A a) :=
    Z.actualTrivialization_snd_val i t ha
  have hmem : (Z.inverse i a).comp (A a) ∈ G := by
    rw [← hg]
    exact mem_image_of_mem _ (mem_univ g)
  have hBinv : ‖Z.inverse i a‖ ≤ M :=
    (hB i a ha).trans (by exact_mod_cast (Finset.le_sup (f := B) hi))
  apply hεU
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(Z.inverse i a).comp (A a), hmem, ?_⟩
  have hdist : dist ((Z.inverse i a).comp (Y a)) ((Z.inverse i a).comp (A a)) ≤
      ‖Z.inverse i a‖ * dist (Y a) (A a) := by
    rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  calc
    _ ≤ ‖Z.inverse i a‖ * dist (Y a) (A a) := hdist
    _ ≤ (M : ℝ) * δ := mul_le_mul hBinv (hY a).le (dist_nonneg) M.coe_nonneg
    _ < ((M : ℝ) + 1) * δ := by nlinarith
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hMpos)

end ExactSectionAtlas

end
end BanachIsometric
