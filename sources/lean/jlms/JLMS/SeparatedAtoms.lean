import JLMS.ProofTargets
import JLMS.AtomicNormingFunction

/-!
# Section 6: assembling disjoint functions from separated atoms

`SeparatedAtomicWitnesses` records the output of the diagonal construction in
Lemma 6.1, proved in `DiagonalSelection` and transferred to the original dual
in `DisjointConstruction`. The subsequent function construction is proved here,
including the strict norm bound and global disjointness.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The output of Lemma 6.1, retaining the original dual functionals and a
globally disjoint family of compact clopen neighborhoods. This definition
asserts no existence; its construction is proved in `DisjointConstruction`. -/
def SeparatedAtomicWitnesses (M : AtomicDualModel 𝕜 K)
    (T : CZero 𝕜 K →L[𝕜] X) (r : ℝ) : Prop :=
  ∃ φ : ℕ → (X →L[𝕜] 𝕜), ∃ A : ℕ → Finset K,
    ∃ U : ∀ j, NeighborhoodFamily (fun k : ↥(A j) => (k : K)),
      (∀ j, ‖φ j‖ ≤ 1) ∧
      (∀ j, (A j : Set K) ⊆ Function.support (M.representation (banachAdjoint T (φ j)))) ∧
      (Pairwise fun i j => Disjoint (⋃ k, (U i).sets k) (⋃ k, (U j).sets k)) ∧
      ∀ j, r < ‖atomicRestriction M (A j : Set K) (banachAdjoint T (φ j))‖

/-- The final proof of the disjoint-function conclusion in Section 6. Only
Rudin's model and the diagonal output remain as mathematical inputs. -/
theorem disjointFunctions_of_separatedAtoms [LocallyCompactSpace K] [T2Space K]
    (M : AtomicDualModel 𝕜 K) (hK : IsScattered K)
    (T : CZero 𝕜 K →L[𝕜] X) {δ θ : ℝ} (hθ : 0 < θ)
    (h : SeparatedAtomicWitnesses M T (δ + θ)) : DisjointFunctionWitnesses T δ := by
  classical
  obtain ⟨φ, A, U, hφ, _hsupport, hdisjoint, hmass⟩ := h
  choose η hη hsupp hlarge using fun j => exists_supported_atomic_norming_function M hK
    (banachAdjoint T (φ j)) (A j) (U j) hθ (hmass j)
  refine ⟨η, hη, ?_, ?_⟩
  · intro i j hij
    exact (hdisjoint hij).mono (hsupp i) (hsupp j)
  · intro j
    have hb := (φ j).le_opNorm (T (η j))
    have hb' := mul_le_mul_of_nonneg_right (hφ j) (norm_nonneg (T (η j)))
    exact (hlarge j).trans_le (hb.trans (by simpa only [one_mul] using hb'))

end JLMS
