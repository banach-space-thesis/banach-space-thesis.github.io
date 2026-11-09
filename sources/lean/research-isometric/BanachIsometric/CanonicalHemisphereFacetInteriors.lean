import BanachIsometric.CanonicalHemisphereCone
import BanachIsometric.CanonicalEquatorFacetInteriors

/-! The cone facets have multiplicity one in positive barycentric
coordinates, above each equator direction off the equator seams. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric NormedSpace
open scoped Topology unitInterval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_canonicalHemisphereFacet_interior_and_unique
    (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v)
    (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) (x : closedHemisphere pole)
    (h r : ℝ) (hh : 0 < h) (hr : 0 < r) (z : EquatorSphere v)
    (hx : x.val.val = h • pole.val + r • z.val.val)
    (hz : canonicalEquatorOffSeam v n hdim z) :
    ∃ a : Fin (n + 3) × Simplex (n + 2),
      canonicalHemisphereFacet v pole n hdim a.1 a.2 = x ∧ (∀ j, 0 < a.2 j) ∧
      ∀ b : Fin (n + 3) × Simplex (n + 2), canonicalHemisphereFacet v pole n hdim b.1 b.2 = x → b = a := by
  obtain ⟨⟨i, u⟩, huHit, huPos, hEquatorUnique⟩ :=
    exists_canonicalEquatorFace_interior_and_unique v n hdim z hz
  let W := equatorCenteredLinear v n hdim (centeredSimplexVector n (face i u))
  let l := ‖W‖
  have hWne : W ≠ 0 := by
    change equatorCenteredLinear v n hdim (centeredSimplexVector n (face i u)) ≠ 0
    rw [← affineSingularSimplex_centeredEquatorFacet v n hdim i u]
    exact (centeredEquatorFacet_admissible v pole hPole n hdim i u).1
  have hl : 0 < l := norm_pos_iff.mpr hWne
  have hznorm : ‖z.val.val‖ = 1 := norm_eq_of_mem_sphere z
  have hW : W = l • z.val.val := by
    have hv := canonicalEquatorFace_val v n hdim i u
    rw [huHit, affineSingularSimplex_centeredEquatorFacet] at hv
    change z.val.val = normalize W at hv
    rw [hv, norm_smul_normalize]
  let d := r + h * l
  have hd : 0 < d := add_pos hr (mul_pos hh hl)
  let t₀ := h * l / d
  have ht₀ : 0 < t₀ := div_pos (mul_pos hh hl) hd
  have ht₁ : t₀ < 1 := by
    apply (div_lt_iff₀ hd).mpr
    change h * l < 1 * (r + h * l)
    linarith
  let t : unitInterval := ⟨t₀, ht₀.le, ht₁.le⟩
  let k := l / d
  have hk : 0 < k := div_pos hl hd
  have ht_height : (t : ℝ) = k * h := by
    change h * l / d = (l / d) * h
    field_simp [hd.ne']
  have ht_tangent : (1 - (t : ℝ)) * l = k * r := by
    change (1 - h * l / d) * l = (l / d) * r
    field_simp [hd.ne']
    dsimp only [d]
    ring
  let w := simplexConeWeights n t u
  have hwHit : canonicalHemisphereFacet v pole n hdim i w = x := by
    have hAffine : affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim i) w = k • x.val.val := by
      calc
        _ = (t : ℝ) • pole.val + ((1 - (t : ℝ)) * l) • z.val.val := by
          change affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim i)
            (simplexConeWeights n t u) = _
          rw [affineSingularSimplex_canonicalHemisphereFacet_coneWeights]
          change (t : ℝ) • pole.val + (1 - (t : ℝ)) • W = _
          rw [hW, smul_smul]
        _ = (k * h) • pole.val + (k * r) • z.val.val := by rw [ht_tangent, ht_height]
        _ = k • x.val.val := by simp only [hx, smul_add, smul_smul]
    apply Subtype.ext
    apply Subtype.ext
    rw [canonicalHemisphereFacet_val v pole hPole, hAffine, normalize_smul_of_pos hk,
      normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x.val)]
  have hOrth : inner ℝ pole.val z.val.val = 0 := by
    have hz₀ : inner ℝ v.val z.val.val = 0 := equatorInclusion_inner v z
    rcases hPole with h | h
    · rw [h]
      exact hz₀
    · rw [h]
      change inner ℝ (-v.val) z.val.val = 0
      rw [inner_neg_left, hz₀, neg_zero]
  have hSelf : inner ℝ pole.val pole.val = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere pole]
    norm_num
  have hxHeight : inner ℝ pole.val x.val.val = h := by
    rw [hx, inner_add_right, real_inner_smul_right, real_inner_smul_right, hSelf, hOrth, mul_one, mul_zero, add_zero]
  have hxNe : x.val.val ≠ pole.val := by
    intro hxPole
    have hOne : h = 1 := by rw [← hxHeight, hxPole, hSelf]
    have hzero : r • z.val.val = 0 := by
      have hsum : pole.val + 0 = pole.val + r • z.val.val := by
        simpa only [hOne, one_smul, add_zero] using hxPole.symm.trans hx
      exact (add_left_cancel hsum).symm
    have hnorm := congrArg (fun w : V => ‖w‖) hzero
    change ‖r • z.val.val‖ = ‖(0 : V)‖ at hnorm
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hznorm, mul_one, norm_zero] at hnorm
    exact hr.ne' hnorm
  refine ⟨(i, w), hwHit, simplexConeWeights_positive n t u ht₀ ht₁ huPos, ?_⟩
  rintro ⟨j, b⟩ hbHit
  have hb₀ : b 0 < 1 := by
    by_contra! hge
    have hOne : b 0 = 1 := le_antisymm (stdSimplex.le_one b 0) hge
    have hs := stdSimplex.sum_eq_one b
    rw [Fin.sum_univ_succ, hOne] at hs
    have hsum : ∑ q : Fin (n + 2), b q.succ = 0 := by linarith
    have htail (q : Fin (n + 2)) : b q.succ = 0 := by
      have hle : b q.succ ≤ ∑ k : Fin (n + 2), b k.succ :=
        Finset.single_le_sum (fun k _ => stdSimplex.zero_le b k.succ) (Finset.mem_univ q)
      rw [hsum] at hle
      exact le_antisymm hle (stdSimplex.zero_le b q.succ)
    have hA : affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim j) b = pole.val := by
      change (∑ k : Fin (n + 3), b k • canonicalHemisphereFacetVertices v pole n hdim j k) = pole.val
      simp only [Fin.sum_univ_succ, hOne, htail, one_smul, zero_smul, Finset.sum_const_zero,
        add_zero, canonicalHemisphereFacetVertices, Fin.cons_zero]
    have hFacet := canonicalHemisphereFacet_val v pole hPole n hdim j b
    change canonicalHemisphereFacet v pole n hdim j b = x at hbHit
    rw [hbHit, hA, normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere pole)] at hFacet
    exact hxNe hFacet
  obtain ⟨s, u', hs, hb⟩ := exists_simplexConeWeights_reconstruct n b hb₀
  have hs₁ : (s : ℝ) < 1 := hs.trans_lt hb₀
  have hbHit' : canonicalHemisphereFacet v pole n hdim j (simplexConeWeights n s u') = x := by
    rw [hb]
    exact hbHit
  let A := affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim j) (simplexConeWeights n s u')
  let ρ := ‖A‖
  have hρ : 0 < ρ := norm_pos_iff.mpr
    (canonicalHemisphereFacet_admissible v pole hPole n hdim j (simplexConeWeights n s u')).1
  have hNorm : normalize A = x.val.val := by
    have hp := canonicalHemisphereFacet_val v pole hPole n hdim j (simplexConeWeights n s u')
    rw [hbHit'] at hp
    exact hp.symm
  have hA : A = ρ • x.val.val := by
    rw [← hNorm, norm_smul_normalize]
  have hsHeight : (s : ℝ) = ρ * h := by
    have H := inner_affineSingularSimplex_canonicalHemisphereFacet v pole hPole n hdim j (simplexConeWeights n s u')
    change inner ℝ pole.val A = (s : ℝ) at H
    rw [hA, real_inner_smul_right, hxHeight] at H
    exact H.symm
  let W' := equatorCenteredLinear v n hdim (centeredSimplexVector n (face j u'))
  have hTang : (1 - (s : ℝ)) • W' = (ρ * r) • z.val.val := by
    have hsum : (s : ℝ) • pole.val + (1 - (s : ℝ)) • W' =
        (s : ℝ) • pole.val + (ρ * r) • z.val.val := by
      calc
        _ = A := (affineSingularSimplex_canonicalHemisphereFacet_coneWeights v pole n hdim j s u').symm
        _ = ρ • x.val.val := hA
        _ = _ := by simp only [hx, smul_add, smul_smul, hsHeight]
    exact add_left_cancel hsum
  have huHit' : canonicalEquatorFace v n hdim j u' = z := by
    have H := congrArg (NormedSpace.normalize : V → V) hTang
    rw [normalize_smul_of_pos (sub_pos.mpr hs₁), normalize_smul_of_pos (mul_pos hρ hr),
      normalize_eq_self_of_norm_eq_one hznorm] at H
    apply Subtype.ext
    apply Subtype.ext
    rw [canonicalEquatorFace_val, affineSingularSimplex_centeredEquatorFacet]
    exact H
  have hEq := hEquatorUnique (j, u') huHit'
  have hj := congrArg Prod.fst hEq
  have hu' := congrArg Prod.snd hEq
  change j = i at hj
  change u' = u at hu'
  subst j
  subst u'
  have hTangNorm : (1 - (s : ℝ)) * l = ρ * r := by
    have H := congrArg (fun x : V => ‖x‖) hTang
    change ‖(1 - (s : ℝ)) • W‖ = ‖(ρ * r) • z.val.val‖ at H
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hs₁), abs_of_pos (mul_pos hρ hr),
      hznorm, mul_one] using H
  have hprod : (s : ℝ) * d = h * l := by
    calc
      _ = r * (s : ℝ) + h * l * (s : ℝ) := by dsimp only [d]; ring
      _ = h * (ρ * r) + h * l * (s : ℝ) := by rw [hsHeight]; ring
      _ = h * l := by rw [← hTangNorm]; ring
  have hst : s = t := Subtype.ext ((eq_div_iff hd.ne').mpr hprod)
  exact Prod.ext rfl (by rw [← hb, hst])

theorem existsUnique_canonicalHemisphereFacet_interior
    (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v)
    (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) (x : closedHemisphere pole)
    (h r : ℝ) (hh : 0 < h) (hr : 0 < r) (z : EquatorSphere v)
    (hx : x.val.val = h • pole.val + r • z.val.val)
    (hz : canonicalEquatorOffSeam v n hdim z) :
    ∃! a : Fin (n + 3) × Simplex (n + 2),
      (∀ j, 0 < a.2 j) ∧ canonicalHemisphereFacet v pole n hdim a.1 a.2 = x := by
  obtain ⟨a, ha, hp, hu⟩ := exists_canonicalHemisphereFacet_interior_and_unique v pole hPole n hdim x h r hh hr z hx hz
  exact ⟨a, ⟨hp, ha⟩, fun b hb => hu b hb.2⟩

end BanachIsometric.SingularPrism
