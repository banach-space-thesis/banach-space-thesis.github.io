import ThesisCommon.Analysis.SeparableTotalDual
import ThesisCommon.WeakCompact
import Mathlib.Topology.Sequences

/-! A countable total family in the actual continuous dual metrizes each
weakly compact set sufficiently to extract convergent subsequences.
Separable normed spaces supply such a family by Hahn–Banach. -/
noncomputable section
open Set Filter Topology TopologicalSpace
namespace ThesisCommon
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem weakCompact_firstCountable_of_countableTotalDual
    (hdual : HasCountableTotalDual 𝕜 E)
    {K : Set (WeakSpace 𝕜 E)} (hK : IsCompact K) : FirstCountableTopology K := by
  obtain ⟨D, hD, htotal⟩ := hdual
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : Countable D := hD.to_subtype
  let c : K → (D → 𝕜) := fun x φ => φ.val ((toWeakSpace 𝕜 E).symm x.val)
  have hc : Continuous c := by
    apply continuous_pi
    intro φ
    exact (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip φ.val).comp continuous_subtype_val
  have hinj : Function.Injective c := by
    intro x y hxy
    apply Subtype.ext
    apply (toWeakSpace 𝕜 E).symm.injective
    apply sub_eq_zero.mp
    apply htotal
    intro φ hφ
    have h := congrFun hxy ⟨φ, hφ⟩
    simpa only [c, map_sub, sub_eq_zero] using h
  exact (hc.isClosedEmbedding hinj).isEmbedding.firstCountableTopology

theorem exists_weak_subsequence_of_compactCover_countableTotalDual
    (hdual : HasCountableTotalDual 𝕜 E) (u : ℕ → E)
    {K : Set (WeakSpace 𝕜 E)} (hK : IsCompact K)
    (hu : ∀ n, toWeakSpace 𝕜 E (u n) ∈ K) :
    ∃ x : E, ∃ r : ℕ → ℕ, StrictMono r ∧
      Tendsto (fun n => toWeakSpace 𝕜 E (u (r n))) atTop (𝓝 (toWeakSpace 𝕜 E x)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : FirstCountableTopology K := weakCompact_firstCountable_of_countableTotalDual hdual hK
  let v : ℕ → K := fun n => ⟨toWeakSpace 𝕜 E (u n), hu n⟩
  obtain ⟨x, r, hr, hx⟩ := CompactSpace.tendsto_subseq v
  refine ⟨(toWeakSpace 𝕜 E).symm x.val, r, hr, ?_⟩
  simpa only [Function.comp_def, v, LinearEquiv.apply_symm_apply] using
    continuous_subtype_val.tendsto x |>.comp hx

theorem exists_weak_subsequence_of_compactCover_separable [SeparableSpace E]
    (u : ℕ → E) {K : Set (WeakSpace 𝕜 E)} (hK : IsCompact K)
    (hu : ∀ n, toWeakSpace 𝕜 E (u n) ∈ K) :
    ∃ x : E, ∃ r : ℕ → ℕ, StrictMono r ∧
      Tendsto (fun n => toWeakSpace 𝕜 E (u (r n))) atTop (𝓝 (toWeakSpace 𝕜 E x)) :=
  exists_weak_subsequence_of_compactCover_countableTotalDual
    (hasCountableTotalDual_of_separable 𝕜 E) u hK hu

end ThesisCommon
