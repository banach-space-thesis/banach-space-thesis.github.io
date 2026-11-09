import BanachIsometric.LipschitzSmallChainStraightening
import BanachIsometric.RawZeroSingularHomology

/-! The actual prism of affine straightening satisfies the chain homotopy
identity on the actual small-chain complex. Face naturality identifies the
prisms on its boundary with the prisms for the small faces. -/

noncomputable section
namespace BanachIsometric.SingularPrism.LipschitzNeighborhoodRetraction

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} {s : Set E} (D : LipschitzNeighborhoodRetraction s)
variable (V : ι → Set E) (hConvex : ∀ i, Convex ℝ (V i)) (hDomain : ∀ i, V i ⊆ D.domain)

theorem rawPrism_straightening_face {n : ℕ} (i : Fin (n + 2))
    (simplex : RawSmallSimplex (convexCoverInSubtype s V) (n + 1)) :
    rawPrism (D.smallStraighteningHomotopy V hConvex hDomain simplex) n (Finsupp.single (face i) 1) =
      rawPrism (D.smallStraighteningHomotopy V hConvex hDomain
        (rawSmallCoordinateFace (convexCoverInSubtype s V) i simplex)) n
          (Finsupp.single (ContinuousMap.id (Simplex n)) 1) := by
  simp only [rawPrism_single_one]
  apply Finset.sum_congr rfl
  intro j _
  have h : homotopyPrism (D.smallStraighteningHomotopy V hConvex hDomain simplex) j (face i) =
      homotopyPrism (D.smallStraighteningHomotopy V hConvex hDomain
        (rawSmallCoordinateFace (convexCoverInSubtype s V) i simplex)) j (ContinuousMap.id (Simplex n)) := by
    apply ContinuousMap.ext
    intro w
    exact D.straighteningHomotopy_precomp i.succAbove simplex.val
      (D.smallSimplexFits V hConvex hDomain simplex) (prism j w).1 (prism j w).2
  rw [h]

theorem rawSmallStraighteningPrism_identity (n : ℕ) :
    (rawBoundary (n + 1)).comp (D.rawSmallStraighteningPrism V hConvex hDomain (n + 1)) +
      (D.rawSmallStraighteningPrism V hConvex hDomain n).comp
        (rawSmallCoordinateBoundary (convexCoverInSubtype s V) n) =
      D.rawStraightenSmall V hConvex hDomain (n + 1) -
        rawSmallCoordinateInclusion (convexCoverInSubtype s V) (n + 1) := by
  apply Finsupp.lhom_ext
  intro simplex a
  have ha : Finsupp.single simplex a = a • Finsupp.single simplex 1 := by simp
  rw [ha]
  simp only [map_smul]
  congr 1
  have h := LinearMap.congr_fun
    (rawPrism_chain_identity (D.smallStraighteningHomotopy V hConvex hDomain simplex) n)
      (Finsupp.single (ContinuousMap.id (Simplex (n + 1))) 1)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, rawBoundary_single,
    ContinuousMap.id_comp, map_sum, map_zsmul, rawPrism_straightening_face,
    rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, ContinuousMap.comp_id] at h
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    rawSmallStraighteningPrism_single, rawSmallCoordinateBoundary_single, map_sum, map_zsmul,
    rawStraightenSmall_single, rawSmallCoordinateInclusion_single] using h

theorem rawSmallStraighteningPrism_zero_identity :
    (rawBoundary 0).comp (D.rawSmallStraighteningPrism V hConvex hDomain 0) =
      D.rawStraightenSmall V hConvex hDomain 0 - rawSmallCoordinateInclusion (convexCoverInSubtype s V) 0 := by
  apply Finsupp.lhom_ext
  intro simplex a
  have ha : Finsupp.single simplex a = a • Finsupp.single simplex 1 := by simp
  rw [ha]
  simp only [map_smul]
  congr 1
  have h := LinearMap.congr_fun
    (rawPrism_zero_identity (D.smallStraighteningHomotopy V hConvex hDomain simplex))
      (Finsupp.single (ContinuousMap.id (Simplex 0)) 1)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, rawChainMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, ContinuousMap.comp_id] at h
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, rawSmallStraighteningPrism_single,
    rawStraightenSmall_single, rawSmallCoordinateInclusion_single] using h

end BanachIsometric.SingularPrism.LipschitzNeighborhoodRetraction
