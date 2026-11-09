import JLMS.Rudin

/-!
# Atomic notation for the printed statements

The paper identifies C₀(K)* with its atomic measure representation. These
definitions fix that identification using the already proved Rudin theorem;
no representation is an assumption of the statements using this module.
`printedAtomicSupport (𝕜 := 𝕜) hK φ` is the set of nonzero point masses, and
`printedAtomicRestriction (𝕜 := 𝕜) hK A φ` is the actual bounded functional R_A φ.
-/

noncomputable section
namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

/-- The proved atomic representation, fixed for the printed notation. -/
def printedAtomicDualModel (hK : IsScattered K) : AtomicDualModel 𝕜 K :=
  Classical.choice (exists_atomicDualModel (𝕜 := 𝕜) hK)

/-- The paper's atomic support of a functional on C₀(K). -/
abbrev printedAtomicSupport (hK : IsScattered K) (φ : CZero 𝕜 K →L[𝕜] 𝕜) : Set K :=
  Function.support ((printedAtomicDualModel (𝕜 := 𝕜) hK).representation φ)

/-- R_A acts on the original Banach dual, with the atomic representation supplied internally. -/
abbrev printedAtomicRestriction (hK : IsScattered K) (A : Set K) :
    (CZero 𝕜 K →L[𝕜] 𝕜) →L[𝕜] (CZero 𝕜 K →L[𝕜] 𝕜) :=
  atomicRestriction (printedAtomicDualModel (𝕜 := 𝕜) hK) A

/-- On a finite set, restriction is exactly the finite sum of the corresponding point masses. -/
theorem printedAtomicRestriction_finset_apply (hK : IsScattered K)
    (A : Finset K) (φ : CZero 𝕜 K →L[𝕜] 𝕜) (f : CZero 𝕜 K) :
    printedAtomicRestriction (𝕜 := 𝕜) hK (A : Set K) φ f =
      ∑ k ∈ A, (printedAtomicDualModel (𝕜 := 𝕜) hK).representation φ k * f k :=
  atomicRestriction_finset_apply (printedAtomicDualModel (𝕜 := 𝕜) hK) A φ f

end JLMS
