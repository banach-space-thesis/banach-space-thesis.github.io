import BanachIsometric.CanonicalSphereCycle
import BanachIsometric.EquatorIsometricCoordinates
import BanachIsometric.AffineRationalComplex

/-! The canonical equator cycle is the radial normalization of an explicit
affine simplex boundary in its actual orthogonal hyperplane. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric NormedSpace SphereGenerator
open scoped Topology

def centeredSimplexVertices (n : ℕ) : Fin (n + 3) → EuclideanSpace ℝ (Fin (n + 2)) :=
  fun i => centeredSimplexVector n ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩

theorem affineSingularSimplex_centeredSimplexVertices (n : ℕ) (w : Simplex (n + 2)) :
    affineSingularSimplex (centeredSimplexVertices n) w = centeredSimplexVector n w := by
  classical
  apply PiLp.ext
  intro k
  let coordinate : EuclideanSpace ℝ (Fin (n + 2)) →ₗ[ℝ] ℝ := PiLp.projₗ 2 (fun _ : Fin (n + 2) => ℝ) k
  change coordinate (∑ j : Fin (n + 3), w j • centeredSimplexVertices n j) = w k.succ - simplexCenter n
  rw [map_sum]
  simp only [map_smul]
  change (∑ j : Fin (n + 3), w j * ((Pi.single j (1 : ℝ) : Fin (n + 3) → ℝ) k.succ - simplexCenter n)) = _
  have hvertex : (∑ j : Fin (n + 3), w j * (Pi.single j (1 : ℝ) : Fin (n + 3) → ℝ) k.succ) = w k.succ := by
    simp [Pi.single_apply, eq_comm]
  have hmass : (∑ j : Fin (n + 3), w j * simplexCenter n) = simplexCenter n := by
    rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hvertex, hmass]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def equatorCenteredLinear (v : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) :
    EuclideanSpace ℝ (Fin (n + 2)) →ₗ[ℝ] V :=
  ((ℝ ∙ v.val)ᗮ).subtype.comp (equatorStandardLinearIsometry v (n + 1) hdim).symm.toLinearEquiv.toLinearMap

theorem equatorCenteredLinear_injective (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) : Function.Injective (equatorCenteredLinear v n hdim) :=
  Subtype.val_injective.comp (equatorStandardLinearIsometry v (n + 1) hdim).symm.injective

theorem norm_equatorCenteredLinear (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (y : EuclideanSpace ℝ (Fin (n + 2))) :
    ‖equatorCenteredLinear v n hdim y‖ = ‖y‖ :=
  (equatorStandardLinearIsometry v (n + 1) hdim).symm.norm_map y

theorem equatorCenteredLinear_normalize (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (y : EuclideanSpace ℝ (Fin (n + 2))) :
    equatorCenteredLinear v n hdim (normalize y) = normalize (equatorCenteredLinear v n hdim y) := by
  simp only [NormedSpace.normalize, map_smul, norm_equatorCenteredLinear]

theorem inner_equatorCenteredLinear (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v)
    (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) (y : EuclideanSpace ℝ (Fin (n + 2))) :
    inner ℝ pole.val (equatorCenteredLinear v n hdim y) = 0 := by
  have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    ((equatorStandardLinearIsometry v (n + 1) hdim).symm y).property
  change inner ℝ v.val (equatorCenteredLinear v n hdim y) = 0 at h
  rcases hPole with rfl | rfl
  · exact h
  · change inner ℝ (-v.val) (equatorCenteredLinear v n hdim y) = 0
    rw [inner_neg_left, h, neg_zero]

def centeredEquatorVertices (v : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) :
    Fin (n + 3) → V := fun i => equatorCenteredLinear v n hdim (centeredSimplexVertices n i)

def centeredEquatorFacetVertices (v : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3)
    (i : Fin (n + 3)) : Fin (n + 2) → V := centeredEquatorVertices v n hdim ∘ i.succAbove

theorem affineSingularSimplex_centeredEquatorFacet (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) (w : Simplex (n + 1)) :
    affineSingularSimplex (centeredEquatorFacetVertices v n hdim i) w =
      equatorCenteredLinear v n hdim (centeredSimplexVector n (face i w)) := by
  have h := ContinuousMap.congr_fun (affineSingularSimplex_precomp i.succAbove (centeredSimplexVertices n)) w
  change affineSingularSimplex (centeredSimplexVertices n) (face i w) =
    affineSingularSimplex (centeredSimplexVertices n ∘ i.succAbove) w at h
  calc
    _ = equatorCenteredLinear v n hdim (affineSingularSimplex (centeredSimplexVertices n ∘ i.succAbove) w) := by
      change (∑ j : Fin (n + 2), w j • equatorCenteredLinear v n hdim (centeredSimplexVertices n (i.succAbove j))) =
        equatorCenteredLinear v n hdim (∑ j : Fin (n + 2), w j • centeredSimplexVertices n (i.succAbove j))
      simp only [map_sum, map_smul]
    _ = _ := by rw [← h, affineSingularSimplex_centeredSimplexVertices]

def canonicalEquatorAffineChain (v : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) :
    AffineRationalChains V (n + 1) :=
  affineBoundary (n + 1) (Finsupp.single (centeredEquatorVertices v n hdim) 1)

theorem canonicalEquatorAffineChain_eq_sum (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) : canonicalEquatorAffineChain v n hdim =
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (centeredEquatorFacetVertices v n hdim i) 1 :=
  affineBoundary_single (n + 1) (centeredEquatorVertices v n hdim) 1

theorem canonicalEquatorAffineChain_boundary (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) : affineBoundary n (canonicalEquatorAffineChain v n hdim) = 0 :=
  LinearMap.congr_fun (affineBoundary_squared n) (Finsupp.single (centeredEquatorVertices v n hdim) 1)

def canonicalEquatorCoordinates (v : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) :
    C(Sph (n + 1), EquatorSphere v) :=
  ⟨(equatorStandardSphereHomeomorph v (n + 1) hdim).symm,
    (equatorStandardSphereHomeomorph v (n + 1) hdim).symm.continuous⟩

def canonicalEquatorFace (v : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3)
    (i : Fin (n + 3)) : C(Simplex (n + 1), EquatorSphere v) :=
  (canonicalEquatorCoordinates v n hdim).comp (boundarySimplexSphereFace n i)

theorem canonicalEquatorFace_val (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) (w : Simplex (n + 1)) :
    (canonicalEquatorFace v n hdim i w).val.val =
      normalize (affineSingularSimplex (centeredEquatorFacetVertices v n hdim i) w) := by
  rw [affineSingularSimplex_centeredEquatorFacet]
  exact equatorCenteredLinear_normalize v n hdim (centeredSimplexVector n (face i w))

def canonicalEquatorCycle (v : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) :
    rawCycles (EquatorSphere v) n := rawCyclesMap (canonicalEquatorCoordinates v n hdim) n (canonicalSphereCycle n)

theorem canonicalEquatorCycle_val_eq_sum (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) : (canonicalEquatorCycle v n hdim).val =
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (canonicalEquatorFace v n hdim i) 1 := by
  change rawChainMap (canonicalEquatorCoordinates v n hdim) (n + 1) (canonicalSphereChain n) = _
  simp only [canonicalSphereChain, map_sum, map_zsmul, rawChainMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, canonicalEquatorFace]

end BanachIsometric.SingularPrism
