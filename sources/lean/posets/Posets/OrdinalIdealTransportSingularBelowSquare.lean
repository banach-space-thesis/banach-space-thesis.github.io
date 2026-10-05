import Posets.OrdinalIdealTransportSingularReplication
import JLMS.OrdinalSpaceInitialFiniteReduction

/-! For a singular initial ordinal κ, every C[0,α] with κ ≤ α ≤ κ²
is actually isomorphic to C[0,κ]. Hence the proved initial-ordinal
factorisation theorem covers this entire closed interval. -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

def singularInitialBelowSquareEquiv {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    (α : Ordinal.{0}) (hlo : c.ord ≤ α) (hhi : α ≤ c.ord * c.ord) :
    OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 c.ord := by
  refine Classical.choice ?_
  by_cases hω : α < c.ord * Ordinal.omega0
  · obtain ⟨n, ρ, hρ, hα⟩ := exists_initial_finite_quotient_remainder c hc α hlo hω
    have hmul : c.ord ≤ c.ord * ((n + 1 : ℕ) : Ordinal) := by
      calc
        c.ord = c.ord * 1 := (mul_one _).symm
        _ ≤ c.ord * ((n + 1 : ℕ) : Ordinal) :=
          mul_le_mul_left' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) _
    exact ⟨(ordinalSpaceCongrIsometry (𝕜 := 𝕜) hα).toContinuousLinearEquiv.trans
      ((ordinalSpaceSmallRemainder c hc _ ρ hmul hρ).trans
        (ordinalSingularFiniteMultipleEquiv hc hs n))⟩
  · exact ⟨singularInitialInfiniteQuotientEquiv hc hs α (le_of_not_gt hω) hhi⟩

theorem singularInitialBelowSquare_hasUPFP {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    {α : Ordinal.{0}} (hlo : c.ord ≤ α) (hhi : α ≤ c.ord * c.ord) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 α) :=
  (singularInitialOrdinal_hasUPFP hc hs).of_equiv
    (singularInitialBelowSquareEquiv hc hs α hlo hhi).symm

theorem proposition_3_1_singular_belowSquare {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    {α : Ordinal.{0}} (hlo : c.ord ≤ α) (hhi : α ≤ c.ord * c.ord) :
    Proposition_3_1 𝕜 α := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) α) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP (singularInitialBelowSquare_hasUPFP (𝕜 := 𝕜) hc hs hlo hhi).hasPFP
  exact ⟨h.2, fun _ => h.1⟩

end Posets
