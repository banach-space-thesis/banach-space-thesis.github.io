/- Universe-polymorphic extension of the actual singular below-square equivalence and UPFP theorem. -/
import LPCK.GenericOrdinalSingularReplication
import LPCK.GenericOrdinalFixedExponent
import JLMS.OrdinalSpaceFinitePower
import JLMS.OrdinalSpaceInitialFiniteReduction

/-! For a singular initial ordinal κ, every C[0,α] with κ ≤ α ≤ κ²
is actually isomorphic to C[0,κ]. Hence the proved initial-ordinal
factorisation theorem covers this entire closed interval. -/
noncomputable section
universe u
namespace LPCK.GenericOrdinal
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

theorem initialOrdinal_of_principal_hasUPFP {c : Cardinal.{u}}
    (hu : Cardinal.aleph0 < c) : HasUPFP 𝕜 (OrdinalC 𝕜 c.ord) := by
  have hω : Ordinal.omega0 < c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hu
  exact (principalRank_hasUPFP (𝕜 := 𝕜) c.ord
    (Ordinal.principal_add_ord hu.le) hω).of_equiv
      (ordinalSpaceCongrIsometry (𝕜 := 𝕜)
        (Posets.ordinal_uncountable_initial_omega_power hu)).toContinuousLinearEquiv
def ordinalSingularFiniteMultipleEquiv {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (n : ℕ) :
    OrdinalC 𝕜 (c.ord * ((n+1 : ℕ) : Ordinal)) ≃L[𝕜] OrdinalC 𝕜 c.ord := by
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  exact (ordinalSpaceFinitePower (𝕜 := 𝕜) c.ord hκ n).trans
    (Posets.finitePiCollapseEquiv
      (ordinalSpaceSingularInitialSquareEquiv (𝕜 := 𝕜) c hc hs) n)

def singularInitialBelowSquareEquiv {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    (α : Ordinal.{u}) (hlo : c.ord ≤ α) (hhi : α ≤ c.ord * c.ord) :
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

theorem singularInitialBelowSquare_hasUPFP {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    {α : Ordinal.{u}} (hlo : c.ord ≤ α) (hhi : α ≤ c.ord * c.ord) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 α) :=
  (initialOrdinal_of_principal_hasUPFP (lt_of_le_of_ne hc (by intro h; apply hs; rw [← h]; exact Cardinal.isRegular_aleph0))).of_equiv
    (singularInitialBelowSquareEquiv hc hs α hlo hhi).symm

end LPCK.GenericOrdinal

