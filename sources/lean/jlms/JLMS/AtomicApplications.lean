import JLMS.AtomicDual
import JLMS.LargeAtomicPieces
import JLMS.EssentialWeight

/-!
# Applying the coordinate results to the Banach adjoint

Rudin's representation is the explicit data input M. All subsequent restrictions,
finite pieces and essential-weight constructions below are proved, not additional
hypotheses. In particular, Proposition 7.1 uses the actual dual essential norm.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (M : AtomicDualModel 𝕜 K) (T : CZero 𝕜 K →L[𝕜] X)

local instance : NormedAddCommGroup (X →L[𝕜] 𝕜) := inferInstance
local instance : NormedSpace 𝕜 (X →L[𝕜] 𝕜) := inferInstance
local instance : NormedAddCommGroup (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance : NormedSpace 𝕜 (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

def atomicAdjoint : (X →L[𝕜] 𝕜) →L[𝕜] ellOneOn 𝕜 K :=
  (atomicCoordinates M).comp (banachAdjoint T)

@[simp] theorem atomicAdjoint_apply (φ : X →L[𝕜] 𝕜) :
    atomicAdjoint M T φ = M.representation (banachAdjoint T φ) := rfl

theorem atomicAdjoint_essentialNorm : essentialNorm (atomicAdjoint M T) = dualEssentialNorm T :=
  essentialNorm_isometryEquiv_comp (𝕜 := 𝕜) (E := X →L[𝕜] 𝕜)
    (F := CZero 𝕜 K →L[𝕜] 𝕜) (G := ellOneOn 𝕜 K) M.representation (banachAdjoint T)

/-- Proposition 7.1, with the paper's δ + 2θ threshold substituted for r. -/
theorem exists_disjoint_large_dual_atoms {r : ℝ} (hr : 0 ≤ r) (hT : r < dualEssentialNorm T) :
    ∃ φ : ℕ → (X →L[𝕜] 𝕜), ∃ A : ℕ → Finset K,
      (∀ j, ‖φ j‖ ≤ 1) ∧
      (∀ j, (A j : Set K) ⊆ Function.support (M.representation (banachAdjoint T (φ j)))) ∧
      (Pairwise fun i j => Disjoint (A i) (A j)) ∧
      ∀ j, r < ‖atomicRestriction M (A j : Set K) (banachAdjoint T (φ j))‖ := by
  have hr' : r < essentialNorm (atomicAdjoint M T) := by
    rwa [atomicAdjoint_essentialNorm]
  obtain ⟨φ, A, hφ, hsupp, hdisj, hmass⟩ := exists_disjoint_large_atomic_pieces
    (atomicAdjoint M T) hr hr'
  refine ⟨φ, A, hφ, hsupp, hdisj, ?_⟩
  intro j
  simpa only [atomicRestriction_norm, atomicAdjoint_apply] using hmass j

/-- Corollary 5.5 in the original dual-space notation. -/
theorem exists_neighborhood_subsequence_small_dual_weight
    [LocallyCompactSpace K] [T2Space K] (hK : IsScattered K)
    (φ : ℕ → (X →L[𝕜] 𝕜)) (hφ : ∀ j, ‖φ j‖ ≤ 1)
    (F : ℕ → Finset K) (hF : Pairwise fun i j => Disjoint (F i) (F j))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ U : NeighborhoodFamily (fun k : ↥(F n) => (k : K)),
      ∃ s : ℕ → ℕ, StrictMono s ∧
        ∀ j, ‖atomicRestriction M (⋃ k, U.sets k) (banachAdjoint T (φ (s j)))‖ < ε := by
  have hbound (j : ℕ) : ‖atomicAdjoint M T (φ j)‖ ≤ ‖T‖ := by
    rw [atomicAdjoint_apply, M.representation.norm_map]
    exact ((banachAdjoint T).le_opNorm (φ j)).trans (by
      simpa only [norm_banachAdjoint, mul_one] using
        mul_le_mul_of_nonneg_left (hφ j) (norm_nonneg (banachAdjoint T)))
  obtain ⟨n, U, s, hs, hsmall⟩ := exists_neighborhood_subsequence_small_weight hK
    (fun j => atomicAdjoint M T (φ j)) F hF ‖T‖ hbound hε
  refine ⟨n, U, s, hs, ?_⟩
  intro j
  simpa only [atomicRestriction_norm, atomicAdjoint_apply] using hsmall j

end JLMS
