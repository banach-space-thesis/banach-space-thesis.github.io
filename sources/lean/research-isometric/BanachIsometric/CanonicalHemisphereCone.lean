import BanachIsometric.CanonicalEquatorAffine
import BanachIsometric.AffineHemisphereRealization

/-! A geometric hemisphere facet is obtained by adjoining the pole to the
actual centered equator facet and normalizing the affine simplex. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric NormedSpace
open scoped Topology unitInterval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def canonicalHemisphereFacetVertices (v pole : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) : Fin (n + 3) → V :=
  Fin.cons pole.val (centeredEquatorFacetVertices v n hdim i)

theorem centeredEquatorFacet_admissible (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v)
    (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) :
    affineHemisphereAdmissible pole (centeredEquatorFacetVertices v n hdim i) := by
  intro w
  rw [affineSingularSimplex_centeredEquatorFacet]
  refine ⟨?_, ?_⟩
  · intro h
    exact centeredSimplexVector_face_ne_zero n i w
      (equatorCenteredLinear_injective v n hdim (by simpa only [map_zero] using h))
  · rw [inner_equatorCenteredLinear v pole hPole]

theorem inner_affineSingularSimplex_canonicalHemisphereFacet
    (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) (w : Simplex (n + 2)) :
    inner ℝ pole.val (affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim i) w) = w 0 := by
  have hself : inner ℝ pole.val pole.val = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere pole]
    norm_num
  have htail (j : Fin (n + 2)) :
      inner ℝ pole.val (w j.succ • canonicalHemisphereFacetVertices v pole n hdim i j.succ) = 0 := by
    change inner ℝ pole.val (w j.succ • equatorCenteredLinear v n hdim
      (centeredSimplexVertices n (i.succAbove j))) = 0
    rw [real_inner_smul_right, inner_equatorCenteredLinear v pole hPole, mul_zero]
  change (innerSL ℝ pole.val) (∑ j : Fin (n + 3), w j • canonicalHemisphereFacetVertices v pole n hdim i j) = w 0
  rw [map_sum, Fin.sum_univ_succ]
  change inner ℝ pole.val (w 0 • pole.val) +
    ∑ j : Fin (n + 2), inner ℝ pole.val (w j.succ • canonicalHemisphereFacetVertices v pole n hdim i j.succ) = w 0
  simp only [htail, Finset.sum_const_zero, add_zero, real_inner_smul_right, hself, mul_one]

theorem canonicalHemisphereFacet_admissible
    (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) :
    affineHemisphereAdmissible pole (canonicalHemisphereFacetVertices v pole n hdim i) := by
  intro w
  have hi := inner_affineSingularSimplex_canonicalHemisphereFacet v pole hPole n hdim i w
  refine ⟨?_, hi.symm ▸ stdSimplex.zero_le w 0⟩
  intro hz
  have hzero : w 0 = 0 := by
    rw [hz, inner_zero_right] at hi
    exact hi.symm
  let b : Simplex (n + 1) := ⟨fun j => w j.succ, fun j => stdSimplex.zero_le w j.succ, by
    have hs := stdSimplex.sum_eq_one w
    rw [Fin.sum_univ_succ, hzero, zero_add] at hs
    exact hs⟩
  have hbase : affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim i) w =
      affineSingularSimplex (centeredEquatorFacetVertices v n hdim i) b := by
    change (∑ j : Fin (n + 3), w j • canonicalHemisphereFacetVertices v pole n hdim i j) =
      ∑ j : Fin (n + 2), w j.succ • centeredEquatorFacetVertices v n hdim i j
    simp only [Fin.sum_univ_succ, hzero, zero_smul, zero_add, canonicalHemisphereFacetVertices, Fin.cons_succ]
  rw [hbase] at hz
  exact (centeredEquatorFacet_admissible v pole hPole n hdim i b).1 hz

def canonicalHemisphereFacet (v pole : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) : C(Simplex (n + 2), closedHemisphere pole) :=
  affineHemisphereSimplex pole (canonicalHemisphereFacetVertices v pole n hdim i)

theorem canonicalHemisphereFacet_val (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v)
    (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) (w : Simplex (n + 2)) :
    (canonicalHemisphereFacet v pole n hdim i w).val.val =
      normalize (affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim i) w) :=
  affineHemisphereSimplex_val pole _ (canonicalHemisphereFacet_admissible v pole hPole n hdim i) w

def simplexConeWeights (n : ℕ) (t : unitInterval) (u : Simplex (n + 1)) : Simplex (n + 2) := by
  refine ⟨Fin.cons (t : ℝ) (fun j => (1 - (t : ℝ)) * u j), ?_, ?_⟩
  · intro j
    refine Fin.cases t.property.1 (fun k => mul_nonneg (sub_nonneg.mpr t.property.2) (stdSimplex.zero_le u k)) j
  · rw [Fin.sum_univ_succ]
    change (t : ℝ) + (∑ j : Fin (n + 2), (1 - (t : ℝ)) * u j) = 1
    rw [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]
    ring

theorem affineSingularSimplex_canonicalHemisphereFacet_coneWeights
    (v pole : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3))
    (t : unitInterval) (u : Simplex (n + 1)) :
    affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim i) (simplexConeWeights n t u) =
      (t : ℝ) • pole.val + (1 - (t : ℝ)) • equatorCenteredLinear v n hdim (centeredSimplexVector n (face i u)) := by
  rw [← affineSingularSimplex_centeredEquatorFacet]
  change (∑ j : Fin (n + 3), simplexConeWeights n t u j • canonicalHemisphereFacetVertices v pole n hdim i j) =
    (t : ℝ) • pole.val + (1 - (t : ℝ)) • ∑ j : Fin (n + 2), u j • centeredEquatorFacetVertices v n hdim i j
  rw [Fin.sum_univ_succ, Finset.smul_sum]
  change (t : ℝ) • pole.val +
    (∑ j : Fin (n + 2), ((1 - (t : ℝ)) * u j) • centeredEquatorFacetVertices v n hdim i j) =
      (t : ℝ) • pole.val +
        ∑ j : Fin (n + 2), (1 - (t : ℝ)) • (u j • centeredEquatorFacetVertices v n hdim i j)
  simp only [mul_smul]

theorem simplexConeWeights_positive (n : ℕ) (t : unitInterval) (u : Simplex (n + 1))
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) (hu : ∀ j, 0 < u j) :
    ∀ i, 0 < simplexConeWeights n t u i := by
  intro i
  refine Fin.cases ht0 (fun j => ?_) i
  change 0 < (1 - (t : ℝ)) * u j
  exact mul_pos (sub_pos.mpr ht1) (hu j)

theorem exists_simplexConeWeights_reconstruct (n : ℕ) (w : Simplex (n + 2)) (hw : w 0 < 1) :
    ∃ (t : unitInterval) (u : Simplex (n + 1)), (t : ℝ) = w 0 ∧ simplexConeWeights n t u = w := by
  let t : unitInterval := ⟨w 0, stdSimplex.zero_le w 0, stdSimplex.le_one w 0⟩
  have hden : 0 < 1 - w 0 := sub_pos.mpr hw
  have htail : (∑ j : Fin (n + 2), w j.succ) = 1 - w 0 := by
    have hs := stdSimplex.sum_eq_one w
    rw [Fin.sum_univ_succ] at hs
    linarith
  let u : Simplex (n + 1) := ⟨fun j => w j.succ / (1 - w 0),
    fun j => div_nonneg (stdSimplex.zero_le w j.succ) hden.le, by
      change (∑ j : Fin (n + 2), w j.succ / (1 - w 0)) = 1
      simp only [div_eq_mul_inv, ← Finset.sum_mul, htail, mul_inv_cancel₀ hden.ne']⟩
  refine ⟨t, u, rfl, ?_⟩
  apply Subtype.ext
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  change (1 - w 0) * (w j.succ / (1 - w 0)) = w j.succ
  field_simp

end BanachIsometric.SingularPrism
