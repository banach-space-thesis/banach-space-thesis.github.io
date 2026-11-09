import BanachIsometric.CanonicalHemisphereFacetInteriors
import BanachIsometric.HemisphereConeSurjective
import BanachIsometric.HemisphereSuspension

/-! The normalized affine facets cover the actual closed hemispheres.
Every positive barycentric hit is the unique hit in that hemisphere and
its direction does not belong to the opposite closed hemisphere. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric NormedSpace SphereGenerator
open scoped Topology unitInterval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem canonicalHemisphereFacet_hit_of_decomposition
    (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (x : closedHemisphere pole)
    (h r : ℝ) (hh : 0 ≤ h) (hr : 0 ≤ r) (z : EquatorSphere v)
    (hx : x.val.val = h • pole.val + r • z.val.val) :
    ∃ (i : Fin (n + 3)) (w : Simplex (n + 2)), canonicalHemisphereFacet v pole n hdim i w = x := by
  by_cases hr0 : r = 0
  · have hp : x.val.val = pole.val := by
      have hnorm : ‖x.val.val‖ = h := by
        rw [hx, hr0, zero_smul, add_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh,
          norm_eq_of_mem_sphere pole, mul_one]
      rw [norm_eq_of_mem_sphere x.val] at hnorm
      rw [hx, hr0, zero_smul, add_zero, ← hnorm, one_smul]
    let w : Simplex (n + 2) := ⟨Pi.single (0 : Fin (n + 3)) 1, single_mem_stdSimplex ℝ 0⟩
    refine ⟨0, w, ?_⟩
    have hA : affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim 0) w = pole.val := by
      change (∑ j : Fin (n + 3), (Pi.single (0 : Fin (n + 3)) (1 : ℝ) : Fin (n + 3) → ℝ) j •
        canonicalHemisphereFacetVertices v pole n hdim 0 j) = pole.val
      simp [Pi.single_apply, canonicalHemisphereFacetVertices]
    apply Subtype.ext
    apply Subtype.ext
    rw [canonicalHemisphereFacet_val v pole hPole, hA, normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere pole), hp]
  have hrpos := lt_of_le_of_ne hr (Ne.symm hr0)
  obtain ⟨i, u, hu⟩ := exists_canonicalEquatorFace_hit v n hdim z
  let W := equatorCenteredLinear v n hdim (centeredSimplexVector n (face i u))
  let l := ‖W‖
  have hl : 0 < l := by
    change 0 < ‖equatorCenteredLinear v n hdim (centeredSimplexVector n (face i u))‖
    rw [← affineSingularSimplex_centeredEquatorFacet]
    exact norm_pos_iff.mpr (centeredEquatorFacet_admissible v pole hPole n hdim i u).1
  have hW : W = l • z.val.val := by
    have hv := canonicalEquatorFace_val v n hdim i u
    rw [hu, affineSingularSimplex_centeredEquatorFacet] at hv
    change z.val.val = normalize W at hv
    rw [hv, norm_smul_normalize]
  let d := r + h * l
  have hd : 0 < d := add_pos_of_pos_of_nonneg hrpos (mul_nonneg hh hl.le)
  let t : unitInterval := ⟨h * l / d, div_nonneg (mul_nonneg hh hl.le) hd.le,
    (div_le_iff₀ hd).mpr (by dsimp only [d]; linarith)⟩
  let k := l / d
  have hk : 0 < k := div_pos hl hd
  have htH : (t : ℝ) = k * h := by
    change h * l / d = (l / d) * h
    field_simp [hd.ne']
  have htR : (1 - (t : ℝ)) * l = k * r := by
    change (1 - h * l / d) * l = (l / d) * r
    field_simp [hd.ne']
    dsimp only [d]
    ring
  refine ⟨i, simplexConeWeights n t u, ?_⟩
  have hA : affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim i) (simplexConeWeights n t u) =
      k • x.val.val := by
    rw [affineSingularSimplex_canonicalHemisphereFacet_coneWeights]
    change (t : ℝ) • pole.val + (1 - (t : ℝ)) • W = _
    rw [hW, smul_smul, htR, htH, hx, smul_add, smul_smul, smul_smul]
  apply Subtype.ext
  apply Subtype.ext
  rw [canonicalHemisphereFacet_val v pole hPole, hA, normalize_smul_of_pos hk,
    normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x.val)]

theorem canonicalHemisphereFacet_cover
    (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (x : closedHemisphere pole) :
    ∃ (i : Fin (n + 3)) (w : Simplex (n + 2)), canonicalHemisphereFacet v pole n hdim i w = x := by
  let q₀ := (equatorStandardSphereHomeomorph v (n + 1) hdim).symm (sphereBasepoint (n + 1))
  rcases hPole with he | he
  · subst pole
    obtain ⟨⟨t, z⟩, rfl⟩ := hemisphereCone_surjective v q₀ x
    exact canonicalHemisphereFacet_hit_of_decomposition v v (Or.inl rfl) n hdim _ _ _
      (Real.sqrt_nonneg _) t.property.1 z rfl
  · subst pole
    obtain ⟨⟨t, z⟩, rfl⟩ := hemisphereCone_surjective (-v) (equatorOppositePole v q₀) x
    let z' := (equatorOppositePole v).symm z
    have hz : z.val.val = z'.val.val := by
      change z.val.val = ((equatorOppositePole v) z').val.val
      rw [(equatorOppositePole v).apply_symm_apply]
    refine canonicalHemisphereFacet_hit_of_decomposition v (-v) (Or.inr rfl) n hdim
      (hemisphereCone (-v) (t, z)) (Real.sqrt (1 - (t : ℝ) ^ 2)) t
      (Real.sqrt_nonneg _) t.property.1 z' ?_
    rw [hemisphereCone_val, hz]

theorem canonicalHemisphereFacet_unique_of_interior
    (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) (w : Simplex (n + 2))
    (hw : ∀ j, 0 < w j) :
    0 < inner ℝ pole.val (canonicalHemisphereFacet v pole n hdim i w).val.val ∧
      ∀ b : Fin (n + 3) × Simplex (n + 2),
        canonicalHemisphereFacet v pole n hdim b.1 b.2 = canonicalHemisphereFacet v pole n hdim i w → b = (i, w) := by
  let A := affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim i) w
  let l := ‖A‖
  have hl : 0 < l := norm_pos_iff.mpr (canonicalHemisphereFacet_admissible v pole hPole n hdim i w).1
  have ht₁ : w 0 < 1 := by
    have hs := stdSimplex.sum_eq_one w
    rw [Fin.sum_univ_succ] at hs
    have hle : w (0 : Fin (n + 2)).succ ≤ ∑ q : Fin (n + 2), w q.succ :=
      Finset.single_le_sum (fun (q : Fin (n + 2)) _ => stdSimplex.zero_le w q.succ)
        (Finset.mem_univ (0 : Fin (n + 2)))
    have hp : 0 < ∑ q : Fin (n + 2), w q.succ := (hw _).trans_le hle
    linarith
  have hHeight : 0 < inner ℝ pole.val (canonicalHemisphereFacet v pole n hdim i w).val.val := by
    rw [canonicalHemisphereFacet_val v pole hPole, NormedSpace.normalize, real_inner_smul_right,
      inner_affineSingularSimplex_canonicalHemisphereFacet v pole hPole]
    exact mul_pos (inv_pos.mpr hl) (hw 0)
  refine ⟨hHeight, ?_⟩
  obtain ⟨t, u, ht, hwu⟩ := exists_simplexConeWeights_reconstruct n w ht₁
  have ht0 : 0 < (t : ℝ) := ht.symm ▸ hw 0
  have ht1 : (t : ℝ) < 1 := ht.trans_lt ht₁
  have hu (j : Fin (n + 2)) : 0 < u j := by
    have h := hw j.succ
    rw [← hwu] at h
    change 0 < (1 - (t : ℝ)) * u j at h
    exact pos_of_mul_pos_right h (sub_nonneg.mpr t.property.2)
  let W := equatorCenteredLinear v n hdim (centeredSimplexVector n (face i u))
  let z := canonicalEquatorFace v n hdim i u
  let k := ‖W‖
  have hk : 0 < k := by
    change 0 < ‖equatorCenteredLinear v n hdim (centeredSimplexVector n (face i u))‖
    rw [← affineSingularSimplex_centeredEquatorFacet]
    exact norm_pos_iff.mpr (centeredEquatorFacet_admissible v pole hPole n hdim i u).1
  have hW : W = k • z.val.val := by
    have hv := canonicalEquatorFace_val v n hdim i u
    rw [affineSingularSimplex_centeredEquatorFacet] at hv
    change z.val.val = normalize W at hv
    rw [hv, norm_smul_normalize]
  let h := l⁻¹ * (t : ℝ)
  let r := l⁻¹ * ((1 - (t : ℝ)) * k)
  have hh : 0 < h := mul_pos (inv_pos.mpr hl) ht0
  have hr : 0 < r := mul_pos (inv_pos.mpr hl) (mul_pos (sub_pos.mpr ht1) hk)
  let x := canonicalHemisphereFacet v pole n hdim i w
  have hx : x.val.val = h • pole.val + r • z.val.val := by
    change (canonicalHemisphereFacet v pole n hdim i w).val.val = _
    rw [canonicalHemisphereFacet_val v pole hPole]
    change l⁻¹ • A = _
    have hA : A = (t : ℝ) • pole.val + (1 - (t : ℝ)) • W := by
      change affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim i) w = _
      rw [← hwu, affineSingularSimplex_canonicalHemisphereFacet_coneWeights]
    rw [hA, hW, smul_smul, smul_add, smul_smul, smul_smul]
  obtain ⟨a, _, _, hUnique⟩ := exists_canonicalHemisphereFacet_interior_and_unique v pole hPole n hdim
    x h r hh hr z hx (canonicalEquatorOffSeam_of_positive_face v n hdim i u hu)
  intro b hb
  exact (hUnique b hb).trans (hUnique (i, w) rfl).symm

end BanachIsometric.SingularPrism
