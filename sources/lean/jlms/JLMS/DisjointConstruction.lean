import JLMS.DiagonalSelection
import JLMS.SeparatedAtoms
import JLMS.HalfAtomicPieces

/-!
# The disjoint-function theorems in Sections 6 and 7

The entire construction is proved from Rudin's representation: choose the
initial large finite pieces, perform Lemma 6.1's diagonal selection, and build
the phase functions with controlled tails. The primal and dual thresholds use
the two initial-selection propositions, while the diagonal proof is shared.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

local instance : NormedAddCommGroup (X →L[𝕜] 𝕜) := inferInstance
local instance : NormedSpace 𝕜 (X →L[𝕜] 𝕜) := inferInstance

/-- Lemma 6.1 in the original dual notation, with its support condition retained. -/
theorem separatedAtomicWitnesses_of_large_pieces
    (M : AtomicDualModel 𝕜 K) (hK : IsScattered K) (T : CZero 𝕜 K →L[𝕜] X)
    (r θ : ℝ) (hθ : 0 < θ)
    (φ : ℕ → (X →L[𝕜] 𝕜)) (A : ℕ → Finset K) (hφ : ∀ j, ‖φ j‖ ≤ 1)
    (hsupp : ∀ j, (A j : Set K) ⊆ Function.support (M.representation (banachAdjoint T (φ j))))
    (hA : Pairwise fun i j => Disjoint (A i) (A j))
    (hmass : ∀ j, r + θ < ‖atomicRestriction M (A j : Set K) (banachAdjoint T (φ j))‖) :
    SeparatedAtomicWitnesses M T r := by
  have hmass' (j : ℕ) : r + θ < ‖restrictionL1 (A j : Set K) (atomicAdjoint M T (φ j))‖ := by
    simpa only [atomicRestriction_norm, atomicAdjoint_apply] using hmass j
  obtain ⟨ψ, B, U, hψ, hsupport, hdisj, hlarge⟩ := exists_separated_atomic_pieces hK
    (atomicAdjoint M T) r θ hθ φ A hφ hsupp hA hmass'
  refine ⟨ψ, B, U, hψ, hsupport, hdisj, ?_⟩
  intro j
  simpa only [atomicRestriction_norm, atomicAdjoint_apply] using hlarge j

/-- Theorem 3.3, following its complete proof in Sections 4–6. The sole extra
data is the atomic dual model; no diagonal or disjoint-function hypothesis remains. -/
theorem disjointFunctionsHalf_of_atomicDualModel [CompleteSpace X]
    (M : AtomicDualModel 𝕜 K) : DisjointFunctionsHalf (𝕜 := 𝕜) (K := K) (X := X) := by
  intro hK T hnorm δ hδ hδhalf
  let θ := (1 / 2 - δ) / 4
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hr : 0 ≤ δ + 2 * θ := by linarith
  have hbound : 2 * (δ + 2 * θ) < essentialNorm T := by
    rw [hnorm]
    dsimp [θ]
    linarith
  obtain ⟨φ, A, hφ, hsupp, hA, hmass⟩ :=
    exists_disjoint_large_dual_atoms_of_primal M hK T hr hbound
  have hmass' (j : ℕ) : (δ + θ) + θ < ‖atomicRestriction M (A j : Set K) (banachAdjoint T (φ j))‖ := by
    have h := hmass j
    linarith
  have hsep := separatedAtomicWitnesses_of_large_pieces M hK T (δ + θ) θ hθ φ A hφ hsupp hA hmass'
  exact disjointFunctions_of_separatedAtoms M hK T hθ hsep

/-- The stronger Section 7 disjoint-function construction, at every threshold
strictly below the actual essential norm of the Banach adjoint. -/
theorem disjointFunctionsSharp_of_atomicDualModel [CompleteSpace X]
    (M : AtomicDualModel 𝕜 K) : DisjointFunctionsSharp (𝕜 := 𝕜) (K := K) (X := X) := by
  intro hK T δ hδ hδdual
  let θ := (dualEssentialNorm T - δ) / 4
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hr : 0 ≤ δ + 2 * θ := by linarith
  have hbound : δ + 2 * θ < dualEssentialNorm T := by dsimp [θ]; linarith
  obtain ⟨φ, A, hφ, hsupp, hA, hmass⟩ := exists_disjoint_large_dual_atoms M T hr hbound
  have hmass' (j : ℕ) : (δ + θ) + θ < ‖atomicRestriction M (A j : Set K) (banachAdjoint T (φ j))‖ := by
    have h := hmass j
    linarith
  have hsep := separatedAtomicWitnesses_of_large_pieces M hK T (δ + θ) θ hθ φ A hφ hsupp hA hmass'
  exact disjointFunctions_of_separatedAtoms M hK T hθ hsep

theorem disjointFunctionsHalf_of_rudin [CompleteSpace X] (hRudin : RudinRepresentation 𝕜 K) :
    DisjointFunctionsHalf (𝕜 := 𝕜) (K := K) (X := X) := by
  intro hK
  obtain ⟨M⟩ := hRudin hK
  exact disjointFunctionsHalf_of_atomicDualModel M hK

theorem disjointFunctionsSharp_of_rudin [CompleteSpace X] (hRudin : RudinRepresentation 𝕜 K) :
    DisjointFunctionsSharp (𝕜 := 𝕜) (K := K) (X := X) := by
  intro hK
  obtain ⟨M⟩ := hRudin hK
  exact disjointFunctionsSharp_of_atomicDualModel M hK

end JLMS
