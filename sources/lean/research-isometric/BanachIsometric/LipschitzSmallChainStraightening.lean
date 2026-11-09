import BanachIsometric.LipschitzSimplexStraightening
import BanachIsometric.RawLipschitzPrism
import BanachIsometric.RawSmallChainCoordinates

/-! Affine straightening and its prism act on the literal small-chain
coordinates for a cover by convex parts of the retraction domain. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} {s : Set E}

def convexCoverInSubtype (s : Set E) (V : ι → Set E) : ι → Set s :=
  fun i => Subtype.val ⁻¹' V i

namespace LipschitzNeighborhoodRetraction

variable (D : LipschitzNeighborhoodRetraction s) (V : ι → Set E)
variable (hConvex : ∀ i, Convex ℝ (V i)) (hDomain : ∀ i, V i ⊆ D.domain)

include hConvex hDomain in
theorem smallSimplexFits {n : ℕ} (simplex : RawSmallSimplex (convexCoverInSubtype s V) n) :
    SimplexFitsConvexDomain D.domain simplex.val := by
  obtain ⟨i, hi⟩ := simplex.property
  exact ⟨V i, hConvex i, hDomain i, fun w => hi (Set.mem_range_self w)⟩

def straightenSmallSimplex {n : ℕ} (simplex : RawSmallSimplex (convexCoverInSubtype s V) n) :
    RawSingularSimplex s n :=
  D.straighten simplex.val (D.smallSimplexFits V hConvex hDomain simplex)

def smallStraighteningHomotopy {n : ℕ} (simplex : RawSmallSimplex (convexCoverInSubtype s V) n) :
    simplex.val.Homotopy (D.straightenSmallSimplex V hConvex hDomain simplex) :=
  D.straighteningHomotopy simplex.val (D.smallSimplexFits V hConvex hDomain simplex)

def rawStraightenSmall (n : ℕ) : RawSmallCoordinates (convexCoverInSubtype s V) n →ₗ[ℚ]
    RawRationalChains s n :=
  Finsupp.lmapDomain ℚ ℚ (D.straightenSmallSimplex V hConvex hDomain)

def rawSmallStraighteningPrism (n : ℕ) : RawSmallCoordinates (convexCoverInSubtype s V) n →ₗ[ℚ]
    RawRationalChains s (n + 1) :=
  Finsupp.linearCombination ℚ (fun simplex => rawPrism
    (D.smallStraighteningHomotopy V hConvex hDomain simplex) n
    (Finsupp.single (ContinuousMap.id (Simplex n)) 1))

theorem rawStraightenSmall_single (n : ℕ) (simplex : RawSmallSimplex (convexCoverInSubtype s V) n) (a : ℚ) :
    D.rawStraightenSmall V hConvex hDomain n (Finsupp.single simplex a) =
      Finsupp.single (D.straightenSmallSimplex V hConvex hDomain simplex) a := by
  simp only [rawStraightenSmall, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem rawSmallStraighteningPrism_single (n : ℕ)
    (simplex : RawSmallSimplex (convexCoverInSubtype s V) n) :
    D.rawSmallStraighteningPrism V hConvex hDomain n (Finsupp.single simplex 1) =
      rawPrism (D.smallStraighteningHomotopy V hConvex hDomain simplex) n
        (Finsupp.single (ContinuousMap.id (Simplex n)) 1) := by
  simp only [rawSmallStraighteningPrism, Finsupp.linearCombination_single, one_smul]

theorem straightenSmallSimplex_face {n : ℕ} (i : Fin (n + 2))
    (simplex : RawSmallSimplex (convexCoverInSubtype s V) (n + 1)) :
    (D.straightenSmallSimplex V hConvex hDomain simplex).comp (face i) =
      D.straightenSmallSimplex V hConvex hDomain
        (rawSmallCoordinateFace (convexCoverInSubtype s V) i simplex) :=
  D.straighten_precomp i.succAbove simplex.val (D.smallSimplexFits V hConvex hDomain simplex)

theorem rawStraightenSmall_boundary (n : ℕ) :
    (rawBoundary n).comp (D.rawStraightenSmall V hConvex hDomain (n + 1)) =
      (D.rawStraightenSmall V hConvex hDomain n).comp
        (rawSmallCoordinateBoundary (convexCoverInSubtype s V) n) := by
  apply Finsupp.lhom_ext
  intro simplex a
  simp only [LinearMap.comp_apply, rawStraightenSmall_single, rawBoundary_single,
    rawSmallCoordinateBoundary_single, map_sum, map_zsmul, straightenSmallSimplex_face]

theorem rawStraightenSmall_mem_lipschitz (n : ℕ) (c : RawSmallCoordinates (convexCoverInSubtype s V) n) :
    D.rawStraightenSmall V hConvex hDomain n c ∈ rawLipschitzCarrier s n := by
  have hmap : Finsupp.supported ℚ ℚ (Set.univ : Set (RawSmallSimplex (convexCoverInSubtype s V) n)) ≤
      (rawLipschitzCarrier s n).comap (D.rawStraightenSmall V hConvex hDomain n) := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨simplex, _, rfl⟩
    change D.rawStraightenSmall V hConvex hDomain n (Finsupp.single simplex 1) ∈ rawLipschitzCarrier s n
    rw [rawStraightenSmall_single]
    exact Finsupp.single_mem_supported ℚ 1 (D.exists_lipschitz_straighten simplex.val
      (D.smallSimplexFits V hConvex hDomain simplex))
  exact hmap ((Finsupp.mem_supported ℚ c).mpr (Set.subset_univ _))

theorem rawSmallStraighteningPrism_mem_lipschitz (n : ℕ)
    (c : RawSmallCoordinates (convexCoverInSubtype s V) n)
    (hc : rawSmallCoordinateInclusion (convexCoverInSubtype s V) n c ∈ rawLipschitzCarrier s n) :
    D.rawSmallStraighteningPrism V hConvex hDomain n c ∈ rawLipschitzCarrier s (n + 1) := by
  let P : Set (RawSmallSimplex (convexCoverInSubtype s V) n) :=
    {simplex | ∃ L : ℝ≥0, LipschitzWith L simplex.val}
  have hcP : c ∈ Finsupp.supported ℚ ℚ P := by
    apply (Finsupp.mem_supported' ℚ c).mpr
    intro simplex hsimplex
    have hz := (Finsupp.mem_supported' ℚ _).mp hc simplex.val hsimplex
    change Finsupp.mapDomain (fun simplex : RawSmallSimplex (convexCoverInSubtype s V) n => simplex.val)
      c simplex.val = 0 at hz
    rwa [Finsupp.mapDomain_apply Subtype.val_injective] at hz
  have hmap : Finsupp.supported ℚ ℚ P ≤
      (rawLipschitzCarrier s (n + 1)).comap (D.rawSmallStraighteningPrism V hConvex hDomain n) := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨simplex, ⟨L, hL⟩, rfl⟩
    change D.rawSmallStraighteningPrism V hConvex hDomain n (Finsupp.single simplex 1) ∈
      rawLipschitzCarrier s (n + 1)
    rw [rawSmallStraighteningPrism_single]
    obtain ⟨K, hK⟩ := D.exists_lipschitz_straighteningHomotopy simplex.val
      (D.smallSimplexFits V hConvex hDomain simplex) hL
    exact rawPrism_preserves_lipschitz (D.smallStraighteningHomotopy V hConvex hDomain simplex) hK n
      (Finsupp.single_mem_supported ℚ 1 ⟨1, LipschitzWith.id⟩)
  exact hmap hcP

end LipschitzNeighborhoodRetraction
end BanachIsometric.SingularPrism
