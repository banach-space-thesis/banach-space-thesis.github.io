import JFA.ClassificationReduction
import JFA.FiniteProjectionModels

/-! The numbered Theorem 1.4, with all projection cases and uniqueness proved.
The former finite-rank proof premise is supplied by the checked tensor-range
identification and comparison-kernel absorption. -/

noncomputable section
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

theorem theorem_1_4 : Theorem_1_4 𝕜 𝒜 :=
  theorem_1_4_of_nonzero_compact_scalar_case
    (fun h𝒜 hc hfew P hP hinf hk hne =>
      amplified_nonzero_compact_scalar_projection_range_iso h𝒜 hc hfew P hP hinf hk hne)

end JFA
