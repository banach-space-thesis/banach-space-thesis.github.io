import BanachIsometric.LipschitzStraighteningPrismIdentity
import BanachIsometric.LipschitzSubdivisionCycleFilling
import BanachIsometric.RawSmallChainInclusion
import BanachIsometric.SmallChainHomologyFilling
import BanachIsometric.PathConnectedZeroHomology

/-! Cycle representatives and fillings in the Lipschitz chain subcomplex.
Subdivision first makes the actual chains small enough to straighten. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set
open scoped Topology NNReal

theorem rawLipschitzCarrier_zero_eq_top (X : Type*) [PseudoMetricSpace X] :
    rawLipschitzCarrier X 0 = ⊤ := by
  have h : {simplex : RawSingularSimplex X 0 | ∃ L : ℝ≥0, LipschitzWith L simplex} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro simplex
    refine ⟨0, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simp [simplexZero_eq_vertex x, simplexZero_eq_vertex y]
  rw [rawLipschitzCarrier, h, Finsupp.supported_univ]

namespace LipschitzNeighborhoodRetraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} {s : Set E} (D : LipschitzNeighborhoodRetraction s)
variable (V : ι → Set E) (hConvex : ∀ i, Convex ℝ (V i)) (hDomain : ∀ i, V i ⊆ D.domain)
variable (hOpen : ∀ i, IsOpen (convexCoverInSubtype s V i))
variable (hCover : ∀ x : s, ∃ i, x ∈ convexCoverInSubtype s V i)

include D V hConvex hDomain hOpen hCover

theorem exists_lipschitz_cycle_representative_of_cover (n : ℕ)
    (c : RawRationalChains s (n + 1)) (hc : rawBoundary n c = 0) :
    ∃ d : RawRationalChains s (n + 1), d ∈ rawLipschitzCarrier s (n + 1) ∧
      rawBoundary n d = 0 ∧ ∃ a : RawRationalChains s (n + 2), rawBoundary (n + 1) a = c - d := by
  let U := convexCoverInSubtype s V
  obtain ⟨d, hd, hd0, a, ha⟩ := exists_small_cycle_representative U hOpen hCover n c hc
  obtain ⟨p, hp⟩ := exists_rawSmallCoordinates_of_mem U (n + 1) d hd
  have hp0 : rawSmallCoordinateBoundary U n p = 0 := by
    apply rawSmallCoordinateInclusion_injective U n
    rw [← rawSmallCoordinateInclusion_boundary_apply, hp, hd0, map_zero]
  let R := D.rawStraightenSmall V hConvex hDomain
  let P := D.rawSmallStraighteningPrism V hConvex hDomain
  refine ⟨R (n + 1) p, D.rawStraightenSmall_mem_lipschitz V hConvex hDomain (n + 1) p, ?_,
    a - P (n + 1) p, ?_⟩
  · have h := LinearMap.congr_fun (D.rawStraightenSmall_boundary V hConvex hDomain n) p
    change rawBoundary n (R (n + 1) p) = R n (rawSmallCoordinateBoundary U n p) at h
    rwa [hp0, map_zero] at h
  · have h := LinearMap.congr_fun (D.rawSmallStraighteningPrism_identity V hConvex hDomain n) p
    change rawBoundary (n + 1) (P (n + 1) p) + P n (rawSmallCoordinateBoundary U n p) =
      R (n + 1) p - rawSmallCoordinateInclusion U (n + 1) p at h
    rw [hp0, map_zero, add_zero, hp] at h
    rw [map_sub, ha, h]
    abel

theorem exists_lipschitz_boundary_filling_of_cover (n : ℕ)
    (c : RawRationalChains s (n + 1)) (hc : c ∈ rawLipschitzCarrier s (n + 1))
    (a : RawRationalChains s (n + 2)) (ha : rawBoundary (n + 1) a = c) :
    ∃ b : RawRationalChains s (n + 2), b ∈ rawLipschitzCarrier s (n + 2) ∧
      rawBoundary (n + 1) b = c := by
  let U := convexCoverInSubtype s V
  obtain ⟨k, hk⟩ := exists_rawSubdivision_small_chain U hOpen hCover (n + 2) a
  obtain ⟨p, hp⟩ := exists_rawSmallCoordinates_of_mem U (n + 2)
    ((rawSubdivision s (n + 2) ^ k) a) hk
  let q := rawSmallCoordinateBoundary U (n + 1) p
  have hq : rawSmallCoordinateInclusion U (n + 1) q = (rawSubdivision s (n + 1) ^ k) c := by
    change rawSmallCoordinateInclusion U (n + 1) (rawSmallCoordinateBoundary U (n + 1) p) = _
    rw [← rawSmallCoordinateInclusion_boundary_apply, hp]
    have h := LinearMap.congr_fun (rawSubdivision_boundary_power s (n + 1) k) a
    simpa only [LinearMap.comp_apply, ha] using h
  have hq0 : rawSmallCoordinateBoundary U n q = 0 :=
    LinearMap.congr_fun (rawSmallCoordinateBoundary_squared U n) p
  have hqLip : rawSmallCoordinateInclusion U (n + 1) q ∈ rawLipschitzCarrier s (n + 1) := by
    rw [hq]
    exact rawSubdivision_power_preserves_lipschitz (n + 1) k hc
  have hc0 : rawBoundary n c = 0 := by
    rw [← ha]
    exact LinearMap.congr_fun (rawBoundary_squared n) a
  let R := D.rawStraightenSmall V hConvex hDomain
  let P := D.rawSmallStraighteningPrism V hConvex hDomain
  let T := rawSubdivisionCycleFilling s n k c
  have hR := LinearMap.congr_fun (D.rawStraightenSmall_boundary V hConvex hDomain (n + 1)) p
  change rawBoundary (n + 1) (R (n + 2) p) = R (n + 1) q at hR
  have hP := LinearMap.congr_fun (D.rawSmallStraighteningPrism_identity V hConvex hDomain n) q
  change rawBoundary (n + 1) (P (n + 1) q) + P n (rawSmallCoordinateBoundary U n q) =
    R (n + 1) q - rawSmallCoordinateInclusion U (n + 1) q at hP
  rw [hq0, map_zero, add_zero, hq] at hP
  have hT : rawBoundary (n + 1) T = c - (rawSubdivision s (n + 1) ^ k) c :=
    rawSubdivisionCycleFilling_boundary s n k c hc0
  refine ⟨R (n + 2) p - P (n + 1) q + T, ?_, ?_⟩
  · exact (rawLipschitzCarrier s (n + 2)).add_mem
      ((rawLipschitzCarrier s (n + 2)).sub_mem
        (D.rawStraightenSmall_mem_lipschitz V hConvex hDomain (n + 2) p)
        (D.rawSmallStraighteningPrism_mem_lipschitz V hConvex hDomain (n + 1) q hqLip))
      (rawSubdivisionCycleFilling_mem_lipschitz n k c hc)
  · rw [map_add, map_sub, hR, hP, hT]
    abel

theorem exists_lipschitz_zero_boundary_filling_of_cover
    (c : RawRationalChains s 0) (a : RawRationalChains s 1) (ha : rawBoundary 0 a = c) :
    ∃ b : RawRationalChains s 1, b ∈ rawLipschitzCarrier s 1 ∧ rawBoundary 0 b = c := by
  let U := convexCoverInSubtype s V
  obtain ⟨k, hk⟩ := exists_rawSubdivision_small_chain U hOpen hCover 1 a
  obtain ⟨p, hp⟩ := exists_rawSmallCoordinates_of_mem U 1 ((rawSubdivision s 1 ^ k) a) hk
  let q := rawSmallCoordinateBoundary U 0 p
  have hq : rawSmallCoordinateInclusion U 0 q = c := by
    change rawSmallCoordinateInclusion U 0 (rawSmallCoordinateBoundary U 0 p) = c
    rw [← rawSmallCoordinateInclusion_boundary_apply, hp]
    have h := LinearMap.congr_fun (rawSubdivision_boundary_power s 0 k) a
    simp only [LinearMap.comp_apply, ha, rawSubdivision_zero] at h
    change rawBoundary 0 ((rawSubdivision s 1 ^ k) a) =
      ((1 : Module.End ℚ (RawRationalChains s 0)) ^ k) c at h
    simpa only [one_pow, Module.End.one_apply] using h
  have hqLip : rawSmallCoordinateInclusion U 0 q ∈ rawLipschitzCarrier s 0 := by
    simp [rawLipschitzCarrier_zero_eq_top]
  let R := D.rawStraightenSmall V hConvex hDomain
  let P := D.rawSmallStraighteningPrism V hConvex hDomain
  have hR := LinearMap.congr_fun (D.rawStraightenSmall_boundary V hConvex hDomain 0) p
  change rawBoundary 0 (R 1 p) = R 0 q at hR
  have hP := LinearMap.congr_fun (D.rawSmallStraighteningPrism_zero_identity V hConvex hDomain) q
  change rawBoundary 0 (P 0 q) = R 0 q - rawSmallCoordinateInclusion U 0 q at hP
  rw [hq] at hP
  refine ⟨R 1 p - P 0 q, (rawLipschitzCarrier s 1).sub_mem
    (D.rawStraightenSmall_mem_lipschitz V hConvex hDomain 1 p)
    (D.rawSmallStraighteningPrism_mem_lipschitz V hConvex hDomain 0 q hqLip), ?_⟩
  rw [map_sub, hR, hP]
  abel

end LipschitzNeighborhoodRetraction
end BanachIsometric.SingularPrism
