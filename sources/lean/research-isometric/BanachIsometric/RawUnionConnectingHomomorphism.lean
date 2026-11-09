import BanachIsometric.RawUnionSmallCycles
import Mathlib.LinearAlgebra.Isomorphisms

/-! The two-set obstruction descends to a connecting homomorphism on actual
singular homology. This uses the small-chain filling of an ambient boundary. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X : Type*} [TopologicalSpace X]

theorem exists_overlapChain_of_pair_sum_zero (U V : Set X) (n : ℕ)
    (a : RawRationalChains U n) (b : RawRationalChains V n)
    (h : rawSubspaceChainInclusion U n a + rawSubspaceChainInclusion V n b = 0) :
    ∃ c : RawRationalChains (U ∩ V : Set X) n,
      rawSubspaceChainInclusion (U ∩ V) n c = rawSubspaceChainInclusion U n a := by
  have hc : rawSubspaceChainInclusion U n a ∈
      LinearMap.range (rawSubspaceChainInclusion (U ∩ V) n) := by
    rw [range_rawSubspaceChainInclusion_inter]
    refine ⟨⟨a, rfl⟩, ⟨-b, ?_⟩⟩
    rw [map_neg]
    exact ((eq_neg_iff_add_eq_zero).mpr h).symm
  exact hc

theorem rawBoundary_rawUnionChainSum (U V : Set X) (n : ℕ)
    (p : RawUnionChainPair U V (n + 1)) :
    rawBoundary n (rawUnionChainSum U V (n + 1) p) =
      rawUnionChainSum U V n (rawBoundary n p.1, rawBoundary n p.2) := by
  change rawBoundary n (rawSubspaceChainInclusion U (n + 1) p.1 +
    rawSubspaceChainInclusion V (n + 1) p.2) =
    rawSubspaceChainInclusion U n (rawBoundary n p.1) +
      rawSubspaceChainInclusion V n (rawBoundary n p.2)
  rw [map_add]
  exact congrArg₂ (· + ·) (LinearMap.congr_fun (rawSubspaceChainInclusion_boundary U n) p.1)
    (LinearMap.congr_fun (rawSubspaceChainInclusion_boundary V n) p.2)

theorem rawUnionPairToOverlapHomology_eq_zero_of_fill (U V : Set X) (n : ℕ)
    (z : rawUnionPairCycles U V n) (c : RawRationalChains (U ∩ V : Set X) (n + 1))
    (hc : rawBoundary n c = rawUnionPairOverlap U V n z) :
    rawUnionPairToOverlapHomology U V n z = 0 := by
  cases n with
  | zero =>
      change (Submodule.Quotient.mk (rawUnionPairOverlap U V 0 z) :
        RawZeroHomology (U ∩ V : Set X)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨c, hc⟩
  | succ n =>
      let w : rawCycles (U ∩ V : Set X) n :=
        ⟨rawUnionPairOverlap U V (n + 1) z, rawUnionPairOverlap_cycle U V n z⟩
      change (Submodule.Quotient.mk w : RawPositiveHomology (U ∩ V : Set X) n) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨c, Subtype.ext hc⟩

theorem rawUnionPairToOverlapHomology_eq_zero_of_ambient_zero
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) (z : rawUnionPairCycles U V n) (hz : rawUnionPairToHomology U V n z = 0) :
    rawUnionPairToOverlapHomology U V n z = 0 := by
  let c : RawRationalChains X (n + 1) := rawUnionChainSum U V (n + 1) z.val
  have hz' : rawUnionPairToCycles U V n z ∈ rawBoundaries X n :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨a, ha⟩ := hz'
  have ha' : rawBoundary (n + 1) a = c := congrArg Subtype.val ha
  have hc : c ∈ rawSmallChainCarrier (twoSetCover U V) (n + 1) := by
    rw [rawSmallChainCarrier_twoSet_eq_sup]
    exact Submodule.mem_sup.mpr ⟨_, ⟨z.val.1, rfl⟩, _, ⟨z.val.2, rfl⟩, rfl⟩
  obtain ⟨b, hb, hbc⟩ := exists_small_boundary_filling (twoSetCover U V)
    (fun i => by cases i <;> assumption) (twoSetCover_covers U V hcover) n c hc a ha'
  obtain ⟨p, hp⟩ := rawSmall_twoSet_split U V (n + 2) b hb
  let l := z.val.1 - rawBoundary (n + 1) p.1
  let r := z.val.2 - rawBoundary (n + 1) p.2
  have hzero : rawSubspaceChainInclusion U (n + 1) l +
      rawSubspaceChainInclusion V (n + 1) r = 0 := by
    change rawUnionChainSum U V (n + 1)
      (z.val - (rawBoundary (n + 1) p.1, rawBoundary (n + 1) p.2)) = 0
    rw [map_sub, ← rawBoundary_rawUnionChainSum, hp, hbc]
    exact sub_self c
  obtain ⟨w, hw⟩ := exists_overlapChain_of_pair_sum_zero U V (n + 1) l r hzero
  apply rawUnionPairToOverlapHomology_eq_zero_of_fill U V n z w
  apply rawSubspaceChainInclusion_injective (U ∩ V) n
  rw [rawUnionPairOverlap_inclusion]
  have hI := LinearMap.congr_fun (rawSubspaceChainInclusion_boundary (U ∩ V) n) w
  have hL := LinearMap.congr_fun (rawSubspaceChainInclusion_boundary U n) l
  change rawBoundary n (rawSubspaceChainInclusion (U ∩ V) (n + 1) w) =
    rawSubspaceChainInclusion (U ∩ V) n (rawBoundary n w) at hI
  change rawBoundary n (rawSubspaceChainInclusion U (n + 1) l) =
    rawSubspaceChainInclusion U n (rawBoundary n l) at hL
  rw [← hI, hw, hL]
  have hd : rawBoundary n (rawBoundary (n + 1) p.1) = 0 :=
    LinearMap.congr_fun (rawBoundary_squared n) p.1
  simp only [l, map_sub, hd, sub_zero]

def rawUnionConnectingHomomorphism (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    RawPositiveHomology X n →ₗ[ℚ] RawDegreeHomology (U ∩ V : Set X) n :=
  ((LinearMap.ker (rawUnionPairToHomology U V n)).liftQ
      (rawUnionPairToOverlapHomology U V n) (by
        intro z hz
        exact rawUnionPairToOverlapHomology_eq_zero_of_ambient_zero U V hU hV hcover n z hz)).comp
    ((rawUnionPairToHomology U V n).quotKerEquivOfSurjective
      (rawUnionPairToHomology_surjective U V hU hV hcover n)).symm.toLinearMap

theorem rawUnionConnectingHomomorphism_pair (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) (z : rawUnionPairCycles U V n) :
    rawUnionConnectingHomomorphism U V hU hV hcover n (rawUnionPairToHomology U V n z) =
      rawUnionPairToOverlapHomology U V n z := by
  let e := (rawUnionPairToHomology U V n).quotKerEquivOfSurjective
    (rawUnionPairToHomology_surjective U V hU hV hcover n)
  have he : e.symm (rawUnionPairToHomology U V n z) = Submodule.Quotient.mk z :=
    e.symm_apply_apply (Submodule.Quotient.mk z)
  have hker : LinearMap.ker (rawUnionPairToHomology U V n) ≤
      LinearMap.ker (rawUnionPairToOverlapHomology U V n) :=
    fun w hw => rawUnionPairToOverlapHomology_eq_zero_of_ambient_zero U V hU hV hcover n w hw
  change (LinearMap.ker (rawUnionPairToHomology U V n)).liftQ
    (rawUnionPairToOverlapHomology U V n) hker (e.symm (rawUnionPairToHomology U V n z)) = _
  simp only [he, Submodule.liftQ_apply]

end BanachIsometric.SingularPrism
