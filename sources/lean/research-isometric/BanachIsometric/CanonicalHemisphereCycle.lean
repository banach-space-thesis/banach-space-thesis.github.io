import BanachIsometric.CanonicalHemisphereCone
import BanachIsometric.HemisphericalBaseCycle

/-! The oriented normalized affine cones fill the literal canonical
equator cycle. Their north-minus-south cycle is a concrete sphere cycle. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
def equatorHemisphereInclusion (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v) :
    C(EquatorSphere v, closedHemisphere pole) := by
  have hMem (x : EquatorSphere v) : equatorInclusion v x ∈ closedHemisphere pole := by
    change 0 ≤ inner ℝ pole.val (equatorInclusion v x).val
    rcases hPole with h | h
    · rw [h, equatorInclusion_inner]
    · rw [h]
      change 0 ≤ inner ℝ (-v.val) (equatorInclusion v x).val
      rw [inner_neg_left, equatorInclusion_inner, neg_zero]
  exact ⟨fun x => ⟨equatorInclusion v x, hMem x⟩, (equatorInclusion v).continuous.subtype_mk hMem⟩

theorem affineHemisphereSimplex_centeredEquatorFacet
    (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) :
    affineHemisphereSimplex pole (centeredEquatorFacetVertices v n hdim i) =
      (equatorHemisphereInclusion v pole hPole).comp (canonicalEquatorFace v n hdim i) := by
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  apply Subtype.ext
  change (affineHemisphereSimplex pole (centeredEquatorFacetVertices v n hdim i) w).val.val =
    (canonicalEquatorFace v n hdim i w).val.val
  rw [affineHemisphereSimplex_val pole _ (centeredEquatorFacet_admissible v pole hPole n hdim i),
    canonicalEquatorFace_val]

def canonicalHemisphereChain (v pole : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) :
    RawRationalChains (closedHemisphere pole) (n + 2) :=
  affineHemisphereRealization pole (n + 2) (affineCone pole.val (n + 1) (canonicalEquatorAffineChain v n hdim))

theorem canonicalHemisphereChain_eq_sum (v pole : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) : canonicalHemisphereChain v pole n hdim =
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (canonicalHemisphereFacet v pole n hdim i) 1 := by
  simp only [canonicalHemisphereChain, canonicalEquatorAffineChain_eq_sum, map_sum, map_zsmul,
    affineCone_single, affineHemisphereRealization_single, canonicalHemisphereFacet, canonicalHemisphereFacetVertices]

theorem canonicalHemisphereChain_boundary (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v)
    (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) :
    rawBoundary (n + 1) (canonicalHemisphereChain v pole n hdim) =
      rawChainMap (equatorHemisphereInclusion v pole hPole) (n + 1) (canonicalEquatorCycle v n hdim).val := by
  let c := canonicalEquatorAffineChain v n hdim
  let A := Finsupp.supported ℚ ℚ {vertices : Fin (n + 3) → V | affineHemisphereAdmissible pole vertices}
  have hc : affineCone pole.val (n + 1) c ∈ A := by
    change affineCone pole.val (n + 1) (canonicalEquatorAffineChain v n hdim) ∈ A
    rw [canonicalEquatorAffineChain_eq_sum, map_sum]
    apply A.sum_mem
    intro i _
    rw [map_zsmul, affineCone_single]
    apply A.toAddSubgroup.zsmul_mem
    exact Finsupp.single_mem_supported ℚ 1 (canonicalHemisphereFacet_admissible v pole hPole n hdim i)
  have hcone : affineBoundary (n + 1) (affineCone pole.val (n + 1) c) = c := by
    have h := LinearMap.congr_fun (affineBoundary_cone pole.val n) c
    change affineBoundary (n + 1) (affineCone pole.val (n + 1) c) +
      affineCone pole.val n (affineBoundary n c) = c at h
    have hzero : affineBoundary n c = 0 := canonicalEquatorAffineChain_boundary v n hdim
    rwa [hzero, map_zero, add_zero] at h
  calc
    _ = affineHemisphereRealization pole (n + 1) (affineBoundary (n + 1) (affineCone pole.val (n + 1) c)) :=
      affineHemisphereRealization_boundary pole (n + 1) _ hc
    _ = affineHemisphereRealization pole (n + 1) c := by rw [hcone]
    _ = _ := by
      change affineHemisphereRealization pole (n + 1) (canonicalEquatorAffineChain v n hdim) = _
      simp only [canonicalEquatorAffineChain_eq_sum, canonicalEquatorCycle_val_eq_sum, map_sum, map_zsmul,
        affineHemisphereRealization_single, rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
        affineHemisphereSimplex_centeredEquatorFacet v pole hPole]

theorem canonicalNorthChain_boundary (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) :
    rawBoundary (n + 1) (canonicalHemisphereChain v v n hdim) =
      rawChainMap (equatorNorth v) (n + 1) (canonicalEquatorCycle v n hdim).val :=
  canonicalHemisphereChain_boundary v v (Or.inl rfl) n hdim

theorem canonicalSouthChain_boundary (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) :
    rawBoundary (n + 1) (canonicalHemisphereChain v (-v) n hdim) =
      rawChainMap (equatorSouth v) (n + 1) (canonicalEquatorCycle v n hdim).val :=
  canonicalHemisphereChain_boundary v (-v) (Or.inr rfl) n hdim

def canonicalSuspensionCycle (v : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) :
    rawCycles (sphere (0 : V) 1) (n + 1) :=
  hemisphericalBaseCycle v n (canonicalEquatorCycle v n hdim)
    (canonicalHemisphereChain v v n hdim) (canonicalHemisphereChain v (-v) n hdim)
    (canonicalNorthChain_boundary v n hdim) (canonicalSouthChain_boundary v n hdim)

def canonicalSphereHemisphereFacet (v pole : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) :
    RawSingularSimplex (sphere (0 : V) 1) (n + 2) :=
  (closedHemisphereInclusion pole).comp (canonicalHemisphereFacet v pole n hdim i)

theorem canonicalSuspensionCycle_val_eq_sum (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) : (canonicalSuspensionCycle v n hdim).val =
      (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (canonicalSphereHemisphereFacet v v n hdim i) 1) -
        ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (canonicalSphereHemisphereFacet v (-v) n hdim i) 1 := by
  change rawChainMap (closedHemisphereInclusion v) (n + 2) (canonicalHemisphereChain v v n hdim) -
    rawChainMap (closedHemisphereInclusion (-v)) (n + 2) (canonicalHemisphereChain v (-v) n hdim) = _
  simp only [canonicalHemisphereChain_eq_sum, map_sum, map_zsmul, canonicalSphereHemisphereFacet,
    rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

end BanachIsometric.SingularPrism
