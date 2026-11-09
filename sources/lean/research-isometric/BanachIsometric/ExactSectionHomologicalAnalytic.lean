import BanachIsometric.CanonicalHemisphereIsometricCoordinates
import BanachIsometric.CanonicalMomentReferenceMap
import BanachIsometric.CanonicalHemisphereLipschitz
import BanachIsometric.ExactSectionHomologicalLift
import BanachIsometric.ExactSectionCompactTotalSpace
import BanachIsometric.ExactBodyGauge
import BanachIsometric.LiftedCycleQuadratic
import BanachIsometric.SphereNormalProjection

/-! Apply the signed-moment proof to the actual bundle operators, with an
isometric change of ambient coordinates and the literal projected chain. -/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData

open Set Metric MeasureTheory SingularPrism
open scoped NNReal Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {m : ℕ} {p : F → ℝ} {H : sphere (0 : F) 1 → Submodule ℝ F} {a₀ : sphere (0 : F) 1}

theorem exists_reference_quadraticForm_of_lipschitz_canonical_lift
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hEven : Even (n + 3)) (hcont : Continuous p)
    (c : rawCycles (ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H) (n + 1))
    (hc : c.val ∈ rawLipschitzCarrier _ (n + 2))
    (b : RawRationalChains (sphere (0 : F) 1) (n + 3))
    (hb : b ∈ rawLipschitzCarrier _ (n + 3))
    (hfill : rawBoundary (n + 2) b = rawChainMap D.homologicalProjection (n + 2) c.val -
      (canonicalSuspensionCycle v n hdim).val)
    (hMoment : ∀ k ≤ 1, rawSignedSimplexMoment (n + 3) volume
      (fun z => ‖(canonicalHemisphereChartCoordinates v n hdim).symm z‖ ^ (2 * k))
      (rawLipschitzCone (n + 2) (rawChainMap (canonicalMomentReferenceMap hp hcont v n hdim)
        (n + 2) (canonicalSuspensionCycle v n hdim).val)) ≠ 0) :
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧
      ∀ y, Q y = p (D.reference y) ^ 2 := by
  let E := EuclideanSpace ℝ (Fin m)
  let V := EuclideanSpace ℝ (Fin (n + 3))
  let X := ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H
  letI : CompactSpace X := D.compactSpace_actualTotalSpace μ hp hSphere
  let L := canonicalHemisphereIsometricCoordinates v n hdim
  let e := linearIsometry_unitSphereMap L
  have he : LipschitzWith 1 e := (linearIsometry_unitSphereMap_isometry L).lipschitz
  let g : V → ℝ := p ∘ L.symm
  let q : E → ℝ := p ∘ D.reference
  have hg : IsDefinitePositiveHomogeneous g := hp.comp_linearIsometry L.symm.toLinearIsometry
  have hq : IsDefinitePositiveHomogeneous q := hp.comp_linearIsometry D.reference
  have hgc : Continuous g := hcont.comp L.symm.continuous
  have hgs : LipschitzOnWith (C * 1) g (sphere (0 : V) 1) := by
    apply hSphere.comp L.symm.isometry.lipschitz.lipschitzOnWith
    intro x hx
    simpa only [mem_sphere, dist_zero_right, L.symm.norm_map] using hx
  let T : (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] V) :=
    ContinuousLinearMap.compL ℝ E F V L.toContinuousLinearEquiv.toContinuousLinearMap
  let A : C(X, E →L[ℝ] V) :=
    ⟨fun t => T t.val.2, T.continuous.comp (continuous_snd.comp continuous_subtype_val)⟩
  have hA : LipschitzWith _ A :=
    T.lipschitz.comp (LipschitzWith.prod_snd.comp (LipschitzWith.subtype_val _))
  let normal := e.comp D.homologicalProjection
  have hN : LipschitzWith _ normal :=
    he.comp (LipschitzWith.prod_fst.comp (LipschitzWith.subtype_val _))
  have htan (t : X) (y : E) : inner ℝ (A t y) (normal t).val = 0 := by
    change inner ℝ (L (t.val.2 y)) (L t.val.1.val) = 0
    rw [L.inner_map_map, real_inner_comm]
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    apply hTangent t.val.1
    exact t.property.2.1.le (LinearMap.mem_range_self _ y)
  have hexact (t : X) (y : E) : g (A t y) = q y := by
    change p (L.symm (L (t.val.2 y))) = p (D.reference y)
    rw [L.symm_apply_apply]
    apply gauge_eq_of_exact_body_image hq hp (t.val.2).toLinearMap t.property.1 _ y
    change t.val.2 '' D.ModelBody = {x : F | p x ≤ 1} ∩ (LinearMap.range t.val.2.toLinearMap : Set F)
    rw [t.property.2.1]
    exact t.property.2.2
  let a := (canonicalSuspensionCycle v n hdim).val
  let a' := rawChainMap e (n + 2) a
  let b' := rawChainMap e (n + 3) b
  have ha : a ∈ rawLipschitzCarrier _ (n + 2) := canonicalSuspensionCycle_mem_lipschitz v n hdim
  have ha' := rawChainMap_preserves_lipschitz e he _ ha
  have hb' := rawChainMap_preserves_lipschitz e he _ hb
  have hfill' : rawBoundary (n + 2) b' = rawChainMap normal (n + 2) c.val - a' := by
    have h := LinearMap.congr_fun (rawChainMap_boundary e (n + 2)) b
    simp only [LinearMap.comp_apply, hfill, map_sub] at h
    have hcomp : rawChainMap e (n + 2) (rawChainMap D.homologicalProjection (n + 2) c.val) =
        rawChainMap normal (n + 2) c.val :=
      (LinearMap.congr_fun (rawChainMap_comp D.homologicalProjection e (n + 2)) c.val).symm
    rw [hcomp] at h
    exact h
  have hmap : (scaledGaugeSphereMap hg hgc 1).comp e = canonicalMomentReferenceMap hp hcont v n hdim := by
    apply ContinuousMap.ext
    intro u
    rw [ContinuousMap.comp_apply, scaledGaugeSphereMap_apply]
    change (EuclideanSpace.equiv (Fin (n + 3)) ℝ) ((1 : ℝ) • radialGaugeMap g (L u.val)) =
      canonicalHemisphereChartCoordinates v n hdim (radialGaugeMap p u.val)
    rw [one_smul, radialGaugeMap, L.norm_map]
    change (EuclideanSpace.equiv (Fin (n + 3)) ℝ) ((‖u.val‖ / p (L.symm (L u.val))) • L u.val) = _
    rw [L.symm_apply_apply, ← L.map_smul, canonicalHemisphereIsometricCoordinates_coordinate]
    rfl
  have hweight (k : ℕ) : euclideanSimplexWeight (n + 3) k =
      fun z => ‖(canonicalHemisphereChartCoordinates v n hdim).symm z‖ ^ (2 * k) := by
    funext z
    change ‖(EuclideanSpace.equiv (Fin (n + 3)) ℝ).symm z‖ ^ (2 * k) = _
    rw [← L.symm.norm_map, canonicalHemisphereIsometricCoordinates_symm_coordinate]
  apply exists_posDef_quadratic_of_liftedCycle (X := X) (d := n + 1) volume hg hq hgc hgs hEven
    A hA normal hN htan hexact c.val hc c.property a' ha' b' hb' hfill'
  intro k hk
  change rawSignedSimplexMoment (n + 3) volume (euclideanSimplexWeight (n + 3) k)
    (rawLipschitzCone (n + 2) (((rawChainMap (scaledGaugeSphereMap hg hgc 1) (n + 2)).comp
      (rawChainMap e (n + 2))) a)) ≠ 0
  rw [hweight, ← rawChainMap_comp, hmap]
  exact hMoment k hk

end BanachIsometric.ExactSectionPrincipalData
