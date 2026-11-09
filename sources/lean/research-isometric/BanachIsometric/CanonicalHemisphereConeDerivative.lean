import BanachIsometric.CanonicalHemisphereOrientation
import BanachIsometric.CanonicalHemisphereLipschitz
import BanachIsometric.SignedConeMatrixDerivative
import BanachIsometric.LipschitzSingularCone
import BanachIsometric.SignedSimplexCount
import BanachIsometric.RadialHomeomorphismLipschitz
import BanachIsometric.RadialGaugeHomotopy

/-! The actual cone on each canonical hemisphere facet has the signed
vertex determinant times a strictly positive radial normalization factor.
The ordinary derivative of the chosen Lipschitz extension is determined by
its literal simplex values near every positive interior parameter. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric Filter NormedSpace Matrix
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {p : V → ℝ}

def canonicalHemisphereCoordinateFacet (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (v pole : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) :
    RawSingularSimplex (Fin (n + 3) → ℝ) (n + 2) :=
  ⟨fun w => canonicalHemisphereChartCoordinates v n hdim
      (radialGaugeMap p (canonicalHemisphereFacet v pole n hdim i w).val.val),
    (canonicalHemisphereChartCoordinates v n hdim).continuous.comp
      ((radialGaugeHomeomorph hp hcont).continuous.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp (canonicalHemisphereFacet v pole n hdim i).continuous)))⟩

theorem exists_lipschitz_canonicalHemisphereCoordinateFacet
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) {L₀ : ℝ≥0}
    (hSphere : LipschitzOnWith L₀ p (sphere (0 : V) 1)) (v pole : sphere (0 : V) 1)
    (hSide : pole = v ∨ pole = -v) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3)
    (i : Fin (n + 3)) : ∃ L : ℝ≥0, LipschitzWith L (canonicalHemisphereCoordinateFacet hp hcont v pole n hdim i) := by
  obtain ⟨L, hL⟩ := exists_lipschitz_affineHemisphereSimplex pole _
    (canonicalHemisphereFacet_admissible v pole hSide n hdim i)
  obtain ⟨L₁, hL₁⟩ := exists_lipschitz_radialGaugeMap hp hSphere
  exact ⟨_, (canonicalHemisphereChartCoordinates v n hdim).lipschitz.comp
    (hL₁.comp ((LipschitzWith.subtype_val _).comp ((LipschitzWith.subtype_val _).comp hL)))⟩

def canonicalHemisphereAffineGaugeFactor (p : V → ℝ) (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (ε : ℝ) (i : Fin (n + 3))
    (x : Fin (n + 2) → ℝ) : ℝ :=
  (p ((canonicalHemisphereChartCoordinates v n hdim).symm
    ((signedHemisphereVertexMatrix (n + 1) ε i).mulVec (signedSimplexBarycentric (n + 2) x))))⁻¹

theorem canonicalHemisphereAffineGaugeFactor_eq (p : V → ℝ) (v pole : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (ε : ℝ) (hPole : pole.val = ε • v.val)
    (i : Fin (n + 3)) (x : signedSimplexDomain (n + 2)) :
    canonicalHemisphereAffineGaugeFactor p v n hdim ε i x.val =
      (p (affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim i)
        ((signedSimplexCoordinates (n + 2)).symm x)))⁻¹ := by
  let w := (signedSimplexCoordinates (n + 2)).symm x
  change (p ((canonicalHemisphereChartCoordinates v n hdim).symm
    ((signedHemisphereVertexMatrix (n + 1) ε i).mulVec w.val)))⁻¹ = _
  rw [← canonicalHemisphereFacet_affine_coordinates v pole n hdim ε hPole i w,
    ContinuousLinearEquiv.symm_apply_apply]

omit [FiniteDimensional ℝ V] in
theorem radialGaugeMap_normalize_eq_inv_gauge_smul (hp : IsDefinitePositiveHomogeneous p)
    {x : V} (hx : x ≠ 0) : radialGaugeMap p (NormedSpace.normalize x) = (p x)⁻¹ • x := by
  have hn := norm_pos_iff.mpr hx
  rw [radialGaugeMap, norm_normalize hx, NormedSpace.normalize,
    hp.smul_nonneg _ (inv_nonneg.mpr hn.le), smul_smul]
  congr 1
  field_simp [hn.ne', (hp.pos hx).ne']

theorem canonicalHemisphereConeMatrix_germ (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (v pole : sphere (0 : V) 1)
    (hSide : pole = v ∨ pole = -v) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3)
    (ε : ℝ) (hPole : pole.val = ε • v.val) (i : Fin (n + 3))
    {F : (Fin (n + 3) → ℝ) → (Fin (n + 3) → ℝ)} {u : Fin (n + 3) → ℝ}
    (hr : 0 < u 0) (hr₁ : u 0 < 1) (hx : signedTailLinear (n + 2) u ∈ interior (signedSimplexDomain (n + 2)))
    (hF : ∀ w : Simplex (n + 3), F (signedSimplexDrop (n + 3) w) =
      singularConeFun (n + 2) (canonicalHemisphereCoordinateFacet hp hcont v pole n hdim i) w) :
    ∀ᶠ z in 𝓝 u, F (signedConeSourceChart (n + 2) z) =
      (signedHemisphereVertexMatrix (n + 1) ε i).mulVec
        (signedConeSourceChart (n + 2)
          (signedRayTransport (n + 2) (canonicalHemisphereAffineGaugeFactor p v n hdim ε i) id z)) := by
  have h₀ : {z : Fin (n + 3) → ℝ | 0 < z 0} ∈ 𝓝 u :=
    (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hr
  have h₁ : {z : Fin (n + 3) → ℝ | z 0 < 1} ∈ 𝓝 u :=
    (isOpen_lt (continuous_apply 0) continuous_const).mem_nhds hr₁
  let tail := (signedTailLinear (n + 2)).toContinuousLinearMap
  have hTail : ∀ᶠ z in 𝓝 u, tail z ∈ interior (signedSimplexDomain (n + 2)) :=
    tail.continuous.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hx)
  filter_upwards [h₀, h₁, hTail] with z hz₀ hz₁ hzTail
  let x : signedSimplexDomain (n + 2) := ⟨tail z, interior_subset hzTail⟩
  have hz : Fin.cons (z 0) x.val = z := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  have hSource : signedConeSourceChart (n + 2) z ∈ signedSimplexDomain (n + 3) := by
    simpa only [hz] using signedConeSourceChart_mem (n + 2) hz₀.le hz₁.le x
  let w := (signedSimplexCoordinates (n + 3)).symm ⟨signedConeSourceChart (n + 2) z, hSource⟩
  have hR : ∃ h : simplexConeRadius (n + 2) w = z 0,
      simplexConeBase (n + 2) w (h.symm ▸ hz₀) = (signedSimplexCoordinates (n + 2)).symm x := by
    simpa only [hz] using signedConeSourceChart_radius_base (n + 2) hz₀ hz₁.le x
  obtain ⟨hradius, hbase⟩ := hR
  have hrpos : 0 < simplexConeRadius (n + 2) w := hradius.symm ▸ hz₀
  have hval := hF w
  change F (signedConeSourceChart (n + 2) z) = _ at hval
  rw [singularConeFun, dif_pos hrpos, hbase, hradius] at hval
  rw [hval, signedConeSourceChart_apply]
  let b := (signedSimplexCoordinates (n + 2)).symm x
  let e := canonicalHemisphereChartCoordinates v n hdim
  let M := signedHemisphereVertexMatrix (n + 1) ε i
  change (z 0) • e (radialGaugeMap p (canonicalHemisphereFacet v pole n hdim i b).val.val) =
    M.mulVec ((z 0 * canonicalHemisphereAffineGaugeFactor p v n hdim ε i x.val) • b.val)
  rw [canonicalHemisphereFacet_val v pole hSide,
    radialGaugeMap_normalize_eq_inv_gauge_smul hp (canonicalHemisphereFacet_admissible v pole hSide n hdim i b).1,
    map_smul, smul_smul, canonicalHemisphereFacet_affine_coordinates v pole n hdim ε hPole,
    canonicalHemisphereAffineGaugeFactor_eq p v pole n hdim ε hPole i x]
  exact (M.mulVecLin.map_smul _ _).symm

theorem canonicalHemisphereCone_fderiv_det (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (v pole : sphere (0 : V) 1)
    (hSide : pole = v ∨ pole = -v) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3)
    (ε : ℝ) (hε : ε ≠ 0) (hPole : pole.val = ε • v.val) (i : Fin (n + 3))
    {F : (Fin (n + 3) → ℝ) → (Fin (n + 3) → ℝ)} {u : Fin (n + 3) → ℝ}
    (hr : 0 < u 0) (hr₁ : u 0 < 1) (hx : signedTailLinear (n + 2) u ∈ interior (signedSimplexDomain (n + 2)))
    (hD : DifferentiableAt ℝ F (signedConeSourceChart (n + 2) u))
    (hF : ∀ w : Simplex (n + 3), F (signedSimplexDrop (n + 3) w) =
      singularConeFun (n + 2) (canonicalHemisphereCoordinateFacet hp hcont v pole n hdim i) w) :
    ∃ c : ℝ, 0 < c ∧ (fderiv ℝ F (signedConeSourceChart (n + 2) u)).det =
      ε * (Int.negOnePow (i.val : ℤ) • c) := by
  let a := canonicalHemisphereAffineGaugeFactor p v n hdim ε i
  let x : signedSimplexDomain (n + 2) := ⟨signedTailLinear (n + 2) u, interior_subset hx⟩
  let M := signedHemisphereVertexMatrix (n + 1) ε i
  have he := canonicalHemisphereConeMatrix_germ hp hcont v pole hSide n hdim ε hPole i hr hr₁ hx hF
  have hM : M.det ≠ 0 := by
    rw [signedHemisphereVertexMatrix_det]
    rcases Int.units_eq_one_or (Int.negOnePow (i.val : ℤ)) with h | h <;>
      simp [h, hε, (signedFacetCenter_pos (n + 1)).ne']
  have ha := differentiableAt_radialFactor_of_signedConeMatrix_germ (n + 2) M hM hr hD he
  have hdet := (det_fderiv_of_signedConeMatrix_germ (n + 2) M hr ha he).2
  have haPos : 0 < a x.val := by
    change 0 < canonicalHemisphereAffineGaugeFactor p v n hdim ε i x.val
    rw [canonicalHemisphereAffineGaugeFactor_eq p v pole n hdim ε hPole i x]
    exact inv_pos.mpr (hp.pos
      (canonicalHemisphereFacet_admissible v pole hSide n hdim i ((signedSimplexCoordinates (n + 2)).symm x)).1)
  refine ⟨signedFacetCenter (n + 1) * (a x.val) ^ (n + 3),
    mul_pos (signedFacetCenter_pos (n + 1)) (pow_pos haPos _), ?_⟩
  rw [hdet, show M.det = ε * (Int.negOnePow (i.val : ℤ) • signedFacetCenter (n + 1)) from
    signedHemisphereVertexMatrix_det (n + 1) ε i]
  change (ε * (Int.negOnePow (i.val : ℤ) • signedFacetCenter (n + 1))) * (a x.val) ^ (n + 3) = _
  rcases Int.units_eq_one_or (Int.negOnePow (i.val : ℤ)) with h | h <;> simp [h, mul_assoc]

end BanachIsometric.SingularPrism
