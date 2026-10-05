import ThesisCommon.Analysis.UncountableSchauderSumSupport

/-! Countable support in the actual arbitrary-index basis sum.

The first argument uses the genuine finite-subset sum net: summability gives
cofinite decay and hence countable support. For a separable subset, take the
union of the supports of a countable dense set and use closedness of the
corresponding coordinate subspace. These are the arguments of Lemmas 4.12
and 4.13 in the manuscript.
-/
noncomputable section
open TopologicalSpace
namespace ThesisCommon

variable {𝕜 Γ E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A scalar vector has countably many nonzero basis coordinates. This
follows from its actual unconditional expansion, with arbitrary index Γ. -/
theorem NormalizedSchauderFamily.countable_coord_support
    (b : NormalizedSchauderFamily 𝕜 Γ E) (x : E) :
    (Function.support (fun γ => b.coord γ x)).Countable := by
  apply (b.expansion x).summable.countable_support.mono
  intro γ hγ
  change b.coord γ x • b.vector γ ≠ 0
  apply smul_ne_zero hγ
  intro hz
  have hn := b.norm_vector γ
  simp [hz] at hn

namespace UncountableSchauderSum
variable [CompleteSpace E]
variable {b : NormalizedSchauderFamily 𝕜 Γ E} {hb : b.IsOneUnconditional}

/-- Every vector in E(Γ,X) has countable coordinate support. No cardinality
assumption on Γ or nontriviality assumption on X is needed. -/
theorem countable_support (x : UncountableSchauderSum b hb X) :
    (Function.support (fun γ => x γ)).Countable := by
  apply (b.countable_coord_support (normVector x)).mono
  intro γ hγ
  change b.coord γ (normVector x) ≠ 0
  rw [coord_normVector]
  exact RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hγ)

/-- Every norm-separable set lies in a closed countable-coordinate subspace. -/
theorem separable_countable_support {s : Set (UncountableSchauderSum b hb X)}
    (hs : IsSeparable s) :
    ∃ Δ : Set Γ, Δ.Countable ∧
      s ⊆ (supportedSubmodule (b := b) (hb := hb) (Y := X) Δ :
        Set (UncountableSchauderSum b hb X)) := by
  obtain ⟨d, hd, hsd⟩ := hs
  let Δ : Set Γ := ⋃ x ∈ d, Function.support (fun γ => x γ)
  refine ⟨Δ, hd.biUnion (fun x _ => countable_support x), ?_⟩
  apply hsd.trans
  apply (supportedSubmodule_isClosed (b := b) (hb := hb) (Y := X) Δ).closure_subset_iff.mpr
  intro x hx
  change ∀ γ, γ ∉ Δ → x γ = 0
  intro γ hγ
  by_contra hxγ
  exact hγ (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hxγ⟩⟩)

end UncountableSchauderSum
end ThesisCommon
