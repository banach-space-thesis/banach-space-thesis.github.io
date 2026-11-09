import BanachIsometric.LipschitzChainSignedCount
import BanachIsometric.LipschitzOrthogonalChainHomotopy
import BanachIsometric.ScaledGaugeSphereMap
import BanachIsometric.SignedOperatorSimplexPolynomial
import BanachIsometric.RawSingularHomology

/-! A lifted cycle of exact tangential operators has the signed moments of
its projected sphere cycle, scaled by the actual gauge of the evaluation
vector. The equality uses an actual Lipschitz prism and shell filling. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric NormedSpace MeasureTheory
open scoped NNReal Topology

variable {X : Type*} [PseudoMetricSpace X] [CompactSpace X] {m d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "V" => EuclideanSpace ℝ (Fin (d + 2))
local notation "N" => (d + 2)
local notation "S" => sphere (0 : V) 1
local notation "P" => (Fin N → ℝ)
local notation "Op" => (E →L[ℝ] V)

set_option maxHeartbeats 800000 in
theorem liftedCycle_operatorMoment_eq_power
    (μ : Measure P) [μ.IsAddHaarMeasure] {g : V → ℝ} {p : E → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) (hp : IsDefinitePositiveHomogeneous p)
    (hcont : Continuous g) {K : ℝ≥0} (hK : LipschitzOnWith K g S)
    (A : C(X, Op)) {LA : ℝ≥0} (hA : LipschitzWith LA A)
    (normal : C(X, S)) {LN : ℝ≥0} (hN : LipschitzWith LN normal)
    (htan : ∀ x y, inner ℝ (A x y) (normal x).val = 0)
    (hexact : ∀ x y, g (A x y) = p y)
    (c : RawRationalChains X (d + 1)) (hc : c ∈ rawLipschitzCarrier X (d + 1))
    (hcycle : rawBoundary d c = 0)
    (a : RawRationalChains S (d + 1)) (ha : a ∈ rawLipschitzCarrier S (d + 1))
    (b : RawRationalChains S (d + 2)) (hb : b ∈ rawLipschitzCarrier S (d + 2))
    (hfill : rawBoundary (d + 1) b = rawChainMap normal (d + 1) c - a)
    (k : ℕ) (y : E) (hy : y ≠ 0) :
    let M := rawSignedSimplexMoment N μ (euclideanSimplexWeight N k)
    let e := continuousLinearSingularMap (operatorSimplexEval m N y)
    M (rawChainMap e N (rawLipschitzCone (d + 1) (rawChainMap A (d + 1) c))) =
      p y ^ (N + 2 * k) * M (rawLipschitzCone (d + 1)
        (rawChainMap (scaledGaugeSphereMap hg hcont 1) (d + 1) a)) := by
  dsimp only
  let q := p y
  have hq : 0 < q := hp.pos hy
  let v : X → V := fun x => A x y
  have hvLip : LipschitzWith _ v := (ContinuousLinearMap.apply ℝ V y).lipschitz.comp hA
  have hv (x : X) : v x ≠ 0 := by
    intro he
    have h := hexact x y
    change g (v x) = q at h
    rw [he, (hg.eq_zero_iff 0).mpr rfl] at h
    exact hq.ne' h.symm
  obtain ⟨L, hL⟩ := exists_lipschitz_normalize_of_compact hvLip hv
  let f : C(X, S) := ⟨fun x => ⟨normalize (v x), mem_sphere_zero_iff_norm.mpr (norm_normalize (hv x))⟩,
    (hL.subtype_mk (fun x => mem_sphere_zero_iff_norm.mpr (norm_normalize (hv x)))).continuous⟩
  have hf : LipschitzWith L f := hL.subtype_mk (fun x => (f x).property)
  have hperp (x : X) : inner ℝ (f x).val (normal x).val = 0 := by
    change inner ℝ (‖v x‖⁻¹ • v x) (normal x).val = 0
    rw [real_inner_smul_left, htan x y, mul_zero]
  obtain ⟨z, hz, hzfill⟩ := exists_lipschitz_orthogonal_projection_filling d f normal hperp
    hf hN c hc hcycle a b hb hfill
  let G := scaledGaugeSphereMap hg hcont q
  let G₁ := scaledGaugeSphereMap hg hcont 1
  let e := continuousLinearSingularMap (operatorSimplexEval m N y)
  have he : G.comp f = e.comp A := by
    apply ContinuousMap.ext
    intro x
    change (scaledGaugeSphereMap hg hcont q) (f x) = e (A x)
    rw [scaledGaugeSphereMap_apply]
    change (EuclideanSpace.equiv (Fin N) ℝ) (q • radialGaugeMap g (normalize (v x))) =
      (EuclideanSpace.equiv (Fin N) ℝ) (v x)
    have hqx : g (v x) = q := hexact x y
    apply congrArg (fun w => (EuclideanSpace.equiv (Fin N) ℝ) w)
    calc
      q • radialGaugeMap g (normalize (v x)) =
          g (v x) • radialGaugeMap g (normalize (v x)) := by rw [hqx]
      _ = v x := gauge_smul_radialGaugeMap_normalize hg (hv x)
  obtain ⟨LG, hG⟩ := exists_lipschitz_scaledGaugeSphereMap hg hcont hK q
  obtain ⟨LG₁, hG₁⟩ := exists_lipschitz_scaledGaugeSphereMap hg hcont hK 1
  let U := rawChainMap e (d + 1) (rawChainMap A (d + 1) c)
  let B := rawChainMap G (d + 1) a
  let B₁ := rawChainMap G₁ (d + 1) a
  have hB₁ : B₁ ∈ rawLipschitzCarrier P (d + 1) := rawChainMap_preserves_lipschitz G₁ hG₁ _ ha
  have hU : U ∈ rawLipschitzCarrier P (d + 1) :=
    rawChainMap_preserves_lipschitz e (operatorSimplexEval m N y).lipschitz _
      (rawChainMap_preserves_lipschitz A hA _ hc)
  have hB : B ∈ rawLipschitzCarrier P (d + 1) := rawChainMap_preserves_lipschitz G hG _ ha
  have hzG := LinearMap.congr_fun (rawChainMap_boundary G (d + 1)) z
  simp only [LinearMap.comp_apply, hzfill, map_sub] at hzG
  have hcomp : rawChainMap G (d + 1) (rawChainMap f (d + 1) c) = U := by
    change ((rawChainMap G (d + 1)).comp (rawChainMap f (d + 1))) c =
      ((rawChainMap e (d + 1)).comp (rawChainMap A (d + 1))) c
    rw [← rawChainMap_comp f G, ← rawChainMap_comp A e, he]
  rw [hcomp] at hzG
  have hnull : μ (Set.range G) = 0 :=
    measure_range_scaledGaugeSphereMap_eq_zero μ hg hcont hq
  have hfillG : rawBoundary (d + 1) (rawChainMap G (d + 2) z) = U - B := hzG
  have hcount : ∀ᵐ w ∂μ,
      rawSignedSimplexCount N (rawLipschitzCone (d + 1) U) w =
        rawSignedSimplexCount N (rawLipschitzCone (d + 1) B) w := by
    exact ae_rawSignedSimplexCount_cones_eq_of_shell_filling d μ G hG hnull U B z hz hfillG
  let M := rawSignedSimplexMoment N μ (euclideanSimplexWeight N k)
  have hM : M (rawLipschitzCone (d + 1) U) = M (rawLipschitzCone (d + 1) B) := by
    rw [rawSignedSimplexMoment_eq_integral _ μ _ (rawLipschitzCone_preserves_lipschitz _ hU)
        (continuous_euclideanSimplexWeight N k),
      rawSignedSimplexMoment_eq_integral _ μ _ (rawLipschitzCone_preserves_lipschitz _ hB)
        (continuous_euclideanSimplexWeight N k)]
    apply integral_congr_ae
    filter_upwards [hcount] with x hx
    rw [hx]
  have hBscale : B = rawChainMap (continuousLinearSingularMap (simplexScalarMap N q)) (d + 1) B₁ := by
    change rawChainMap G (d + 1) a =
      ((rawChainMap (continuousLinearSingularMap (simplexScalarMap N q)) (d + 1)).comp
        (rawChainMap G₁ (d + 1))) a
    rw [← rawChainMap_comp, scaledGaugeSphereMap_comp_scale]
  change M (rawChainMap e N (rawLipschitzCone (d + 1) (rawChainMap A (d + 1) c))) =
    q ^ (N + 2 * k) * M (rawLipschitzCone (d + 1) B₁)
  rw [← rawLipschitzCone_rawChainMap_linear (d + 1) (operatorSimplexEval m N y) _
    (rawChainMap_preserves_lipschitz A hA _ hc), hM, hBscale,
    rawLipschitzCone_rawChainMap_linear (d + 1) (simplexScalarMap N q) B₁ hB₁]
  have hweight (x : P) :
      euclideanSimplexWeight N k (q • x) = q ^ (2 * k) * euclideanSimplexWeight N k x := by
    simp [euclideanSimplexWeight, norm_smul, Real.norm_of_nonneg hq.le, mul_pow]
  exact rawSignedSimplexMoment_scale N μ q (2 * k) (continuous_euclideanSimplexWeight N k) hweight _
    (rawLipschitzCone_preserves_lipschitz (d + 1) hB₁)

end BanachIsometric.SingularPrism
