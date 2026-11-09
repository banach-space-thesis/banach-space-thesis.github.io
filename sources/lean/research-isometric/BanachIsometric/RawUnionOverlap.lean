import BanachIsometric.RawUnionPairCycles
import BanachIsometric.RawDegreeHomology
import Mathlib.Algebra.Module.Submodule.Equiv

/-! The boundary of the left half of a subordinate singular cycle is a
literal chain in the overlap. Its homology class is the obstruction to
adjusting the two halves to individual cycles. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X : Type*} [TopologicalSpace X]

def rawUnionPairLeftBoundary (U V : Set X) (n : ℕ) :
    rawUnionPairCycles U V n →ₗ[ℚ] RawRationalChains X n :=
  (rawSubspaceChainInclusion U n).comp
    ((rawBoundary n).comp ((LinearMap.fst ℚ _ _).comp (rawUnionPairCycles U V n).subtype))

theorem rawUnionPairLeftBoundary_mem_overlap (U V : Set X) (n : ℕ)
    (z : rawUnionPairCycles U V n) :
    rawUnionPairLeftBoundary U V n z ∈
      LinearMap.range (rawSubspaceChainInclusion (U ∩ V) n) := by
  rw [range_rawSubspaceChainInclusion_inter]
  refine ⟨⟨rawBoundary n z.val.1, rfl⟩, ⟨-rawBoundary n z.val.2, ?_⟩⟩
  rw [map_neg]
  exact ((eq_neg_iff_add_eq_zero).mpr (rawUnionPairBoundary_add_eq_zero U V n z)).symm

def rawUnionPairOverlap (U V : Set X) (n : ℕ) :
    rawUnionPairCycles U V n →ₗ[ℚ] RawRationalChains (U ∩ V : Set X) n :=
  (LinearEquiv.ofInjective (rawSubspaceChainInclusion (U ∩ V) n)
      (rawSubspaceChainInclusion_injective (U ∩ V) n)).symm.toLinearMap.comp
    ((rawUnionPairLeftBoundary U V n).codRestrict _
      (rawUnionPairLeftBoundary_mem_overlap U V n))

theorem rawUnionPairOverlap_inclusion (U V : Set X) (n : ℕ)
    (z : rawUnionPairCycles U V n) :
    rawSubspaceChainInclusion (U ∩ V) n (rawUnionPairOverlap U V n z) =
      rawSubspaceChainInclusion U n (rawBoundary n z.val.1) := by
  let e := LinearEquiv.ofInjective (rawSubspaceChainInclusion (U ∩ V) n)
    (rawSubspaceChainInclusion_injective (U ∩ V) n)
  let c : LinearMap.range (rawSubspaceChainInclusion (U ∩ V) n) :=
    ⟨rawUnionPairLeftBoundary U V n z, rawUnionPairLeftBoundary_mem_overlap U V n z⟩
  exact congrArg Subtype.val (e.apply_symm_apply c)

theorem rawUnionPairOverlap_cycle (U V : Set X) (n : ℕ)
    (z : rawUnionPairCycles U V (n + 1)) :
    rawBoundary n (rawUnionPairOverlap U V (n + 1) z) = 0 := by
  apply rawSubspaceChainInclusion_injective (U ∩ V) n
  rw [map_zero]
  calc
    _ = rawBoundary n (rawSubspaceChainInclusion (U ∩ V) (n + 1)
        (rawUnionPairOverlap U V (n + 1) z)) :=
      (LinearMap.congr_fun (rawSubspaceChainInclusion_boundary (U ∩ V) n) _).symm
    _ = rawBoundary n (rawSubspaceChainInclusion U (n + 1) (rawBoundary (n + 1) z.val.1)) := by
      rw [rawUnionPairOverlap_inclusion]
    _ = rawSubspaceChainInclusion U n (rawBoundary n (rawBoundary (n + 1) z.val.1)) :=
      LinearMap.congr_fun (rawSubspaceChainInclusion_boundary U n) _
    _ = 0 := by
      have h : rawBoundary n (rawBoundary (n + 1) z.val.1) = 0 :=
        LinearMap.congr_fun (rawBoundary_squared n) z.val.1
      rw [h, map_zero]

def rawUnionPairToOverlapHomology (U V : Set X) : (n : ℕ) →
    rawUnionPairCycles U V n →ₗ[ℚ] RawDegreeHomology (U ∩ V : Set X) n
  | 0 => (LinearMap.range (rawBoundary (X := (U ∩ V : Set X)) 0)).mkQ.comp
      (rawUnionPairOverlap U V 0)
  | n + 1 => (rawBoundaries (U ∩ V : Set X) n).mkQ.comp
      ((rawUnionPairOverlap U V (n + 1)).codRestrict (rawCycles (U ∩ V : Set X) n)
        (rawUnionPairOverlap_cycle U V n))

theorem rawUnionPairOverlap_fills_of_class_zero (U V : Set X) (n : ℕ)
    (z : rawUnionPairCycles U V n) (hz : rawUnionPairToOverlapHomology U V n z = 0) :
    ∃ w : RawRationalChains (U ∩ V : Set X) (n + 1),
      rawBoundary n w = rawUnionPairOverlap U V n z := by
  cases n with
  | zero =>
      change (Submodule.Quotient.mk (rawUnionPairOverlap U V 0 z) :
        RawZeroHomology (U ∩ V : Set X)) = 0 at hz
      exact (Submodule.Quotient.mk_eq_zero _).mp hz
  | succ n =>
      let c : rawCycles (U ∩ V : Set X) n :=
        ⟨rawUnionPairOverlap U V (n + 1) z, rawUnionPairOverlap_cycle U V n z⟩
      change (Submodule.Quotient.mk c : RawPositiveHomology (U ∩ V : Set X) n) = 0 at hz
      have h : c ∈ rawBoundaries (U ∩ V : Set X) n := (Submodule.Quotient.mk_eq_zero _).mp hz
      obtain ⟨w, hw⟩ := h
      exact ⟨w, congrArg Subtype.val hw⟩

end BanachIsometric.SingularPrism
