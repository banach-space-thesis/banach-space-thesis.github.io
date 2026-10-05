import Posets.OrdinalIdealTransportRegularFactorization

/-! The remaining reduction for Proposition 3.1. The only analytic hypothesis
here is explicitly the all-operator primary factorisation theorem in the
nonexceptional case; finite regular multiples have been proved separately. -/
noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096

/-- This isolates the precise remaining Alspach–Benyamini input without
altering the paper's proposition or asserting that input. -/
theorem proposition_3_1_of_nonexceptional_hasPFP (α : Ordinal.{0})
    (hpfp : (∀ c : Cardinal.{0}, Cardinal.aleph0 < c → c.IsRegular → ∀ n : ℕ, 2 ≤ n →
      ¬ Nonempty (OrdinalSpace 𝕜 α ≃L[𝕜] OrdinalSpace 𝕜 (c.ord * (n : Ordinal)))) →
      HasPFP 𝕜 (OrdinalSpace 𝕜 α)) : Proposition_3_1 𝕜 α := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) α) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  by_cases hexcl : ∀ c : Cardinal.{0}, Cardinal.aleph0 < c → c.IsRegular → ∀ n : ℕ, 2 ≤ n →
      ¬ Nonempty (OrdinalSpace 𝕜 α ≃L[𝕜] OrdinalSpace 𝕜 (c.ord * (n : Ordinal)))
  · have h := uniqueMaximal_of_hasPFP (hpfp hexcl)
    exact ⟨h.2, fun _ => h.1⟩
  · have hnexcl := hexcl
    push_neg at hnexcl
    obtain ⟨c, hu, hc, n, hn, ⟨e⟩⟩ := hnexcl
    obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
    have h := uniqueMaximalClosed_regular_finiteMultiple (𝕜 := 𝕜) hc hu m
    exact ⟨(uniqueMaximalClosed_operator_equiv e).mpr h,
      fun he => False.elim (hexcl he)⟩

end Posets
