import BanachIsometric.CanonicalHemisphereConeDerivative

/-! The literal cone fiber is parametrized by the facet fiber of the target
direction. The source coordinates are exactly the facet barycentric weights
multiplied by the target radius. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric NormedSpace
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {p : V → ℝ}

def canonicalHemisphereConedFacet (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (v pole : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) :
    RawSingularSimplex (Fin (n + 3) → ℝ) (n + 3) :=
  lipschitzSingularCone (n + 2) (canonicalHemisphereCoordinateFacet hp hcont v pole n hdim i)

def canonicalHemisphereConedExtension (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (v pole : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) : (Fin (n + 3) → ℝ) → (Fin (n + 3) → ℝ) :=
  signedSimplexExtension (n + 3) (canonicalHemisphereConedFacet hp hcont v pole n hdim i)

theorem exists_lipschitz_canonicalHemisphereConedFacet
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) {L : ℝ≥0}
    (hSphere : LipschitzOnWith L p (sphere (0 : V) 1)) (v pole : sphere (0 : V) 1)
    (hSide : pole = v ∨ pole = -v) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3)
    (i : Fin (n + 3)) : ∃ K : ℝ≥0, LipschitzWith K (canonicalHemisphereConedFacet hp hcont v pole n hdim i) :=
  exists_lipschitz_lipschitzSingularCone (n + 2) _
    (exists_lipschitz_canonicalHemisphereCoordinateFacet hp hcont hSphere v pole hSide n hdim i)

theorem canonicalHemisphereConedExtension_apply
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) {L : ℝ≥0}
    (hSphere : LipschitzOnWith L p (sphere (0 : V) 1)) (v pole : sphere (0 : V) 1)
    (hSide : pole = v ∨ pole = -v) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3)
    (i : Fin (n + 3)) (w : Simplex (n + 3)) :
    canonicalHemisphereConedExtension hp hcont v pole n hdim i (signedSimplexDrop (n + 3) w) =
      singularConeFun (n + 2) (canonicalHemisphereCoordinateFacet hp hcont v pole n hdim i) w := by
  let x := signedSimplexCoordinates (n + 3) w
  change signedSimplexExtension (n + 3) (canonicalHemisphereConedFacet hp hcont v pole n hdim i) x.val = _
  rw [(signedSimplexExtension_spec (n + 3) _
    (exists_lipschitz_canonicalHemisphereConedFacet hp hcont hSphere v pole hSide n hdim i)).2 x,
    show (signedSimplexCoordinates (n + 3)).symm x = w from (signedSimplexCoordinates (n + 3)).symm_apply_apply w]
  exact lipschitzSingularCone_apply (n + 2) _
    (exists_lipschitz_canonicalHemisphereCoordinateFacet hp hcont hSphere v pole hSide n hdim i) w

theorem canonicalHemisphereConedExtension_hit_iff
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) {L : ℝ≥0}
    (hSphere : LipschitzOnWith L p (sphere (0 : V) 1)) (v pole : sphere (0 : V) 1)
    (hSide : pole = v ∨ pole = -v) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3)
    (i : Fin (n + 3)) (r : ℝ) (hr : 0 < r) (hr₁ : r ≤ 1) (q : sphere (0 : V) 1)
    (x : Fin (n + 3) → ℝ) :
    x ∈ signedSimplexDomain (n + 3) ∧ canonicalHemisphereConedExtension hp hcont v pole n hdim i x =
      canonicalHemisphereChartCoordinates v n hdim (r • radialGaugeMap p q.val) ↔
      ∃ b : Simplex (n + 2), (canonicalHemisphereFacet v pole n hdim i b).val = q ∧ x = r • b.val := by
  let e := canonicalHemisphereChartCoordinates v n hdim
  let σ := canonicalHemisphereCoordinateFacet hp hcont v pole n hdim i
  let F := canonicalHemisphereConedExtension hp hcont v pole n hdim i
  have hpq : p (r • radialGaugeMap p q.val) = r := by
    rw [hp.smul_nonneg _ hr.le, gauge_radialGaugeMap hp, norm_eq_of_mem_sphere q, mul_one]
  constructor
  · rintro ⟨hx, hxy⟩
    change F x = e (r • radialGaugeMap p q.val) at hxy
    let w := (signedSimplexCoordinates (n + 3)).symm ⟨x, hx⟩
    have hf : F x = singularConeFun (n + 2) σ w :=
      canonicalHemisphereConedExtension_apply hp hcont hSphere v pole hSide n hdim i w
    have hR : 0 < simplexConeRadius (n + 2) w := by
      by_contra hbad
      rw [singularConeFun, dif_neg hbad, hxy] at hf
      have hz : r • radialGaugeMap p q.val = 0 := e.injective (by simpa only [map_zero] using hf)
      rw [hz, (hp.eq_zero_iff 0).mpr rfl] at hpq
      exact hr.ne' hpq.symm
    let b := simplexConeBase (n + 2) w hR
    let q' := (canonicalHemisphereFacet v pole n hdim i b).val
    have he : r • radialGaugeMap p q.val = simplexConeRadius (n + 2) w • radialGaugeMap p q'.val := by
      rw [singularConeFun, dif_pos hR, hxy] at hf
      change e (r • radialGaugeMap p q.val) = simplexConeRadius (n + 2) w • e (radialGaugeMap p q'.val) at hf
      apply e.injective
      exact hf.trans (e.map_smul (simplexConeRadius (n + 2) w) (radialGaugeMap p q'.val)).symm
    have heR : simplexConeRadius (n + 2) w = r := by
      have h := congrArg p he
      rw [hpq, hp.smul_nonneg _ hR.le, gauge_radialGaugeMap hp, norm_eq_of_mem_sphere q', mul_one] at h
      exact h.symm
    refine ⟨b, ?_, ?_⟩
    · apply Subtype.ext
      rw [heR] at he
      have h := congrArg (radialGaugeMapInv p) (smul_right_injective V hr.ne' he)
      rw [radialGaugeMapInv_map hp, radialGaugeMapInv_map hp] at h
      exact h.symm
    · funext j
      change w j.succ = r * (w j.succ / simplexConeRadius (n + 2) w)
      rw [heR]
      field_simp [hr.ne']
  · rintro ⟨b, hb, rfl⟩
    let X := signedSimplexCoordinates (n + 2) b
    let u : Fin (n + 3) → ℝ := Fin.cons r X.val
    have hu : signedConeSourceChart (n + 2) u = r • b.val := by
      rw [signedConeSourceChart_apply]
      change r • signedSimplexBarycentric (n + 2) (signedSimplexDrop (n + 2) b) = _
      rw [signedSimplexBarycentric_drop]
    have hU := signedConeSourceChart_mem (n + 2) hr.le hr₁ X
    refine ⟨hu ▸ hU, ?_⟩
    let w := (signedSimplexCoordinates (n + 3)).symm ⟨signedConeSourceChart (n + 2) u, hU⟩
    obtain ⟨hR, hB⟩ := signedConeSourceChart_radius_base (n + 2) hr hr₁ X
    have hR' : simplexConeRadius (n + 2) w = r := hR
    have hr' : 0 < simplexConeRadius (n + 2) w := hR'.symm ▸ hr
    have hB' : simplexConeBase (n + 2) w hr' = b := hB.trans ((signedSimplexCoordinates (n + 2)).symm_apply_apply b)
    have hf := canonicalHemisphereConedExtension_apply hp hcont hSphere v pole hSide n hdim i w
    change F (signedConeSourceChart (n + 2) u) = singularConeFun (n + 2) σ w at hf
    rw [hu, singularConeFun, dif_pos hr', hB', hR'] at hf
    change F (r • b.val) = r • e (radialGaugeMap p (canonicalHemisphereFacet v pole n hdim i b).val.val) at hf
    rw [hb, ← map_smul] at hf
    exact hf

end BanachIsometric.SingularPrism
