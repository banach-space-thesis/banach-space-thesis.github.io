import BanachIsometric.SignedFacetRayOnSphere
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! At an ordinary regular interior facet preimage the actual boundary cone
has the corresponding ordinary derivative. The determinant sign carries the
orientation coefficient of the facet. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric NormedSpace SphereGenerator Filter
open scoped Topology NNReal

theorem signedFacetRadialFactor_differentiableAt (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) (i : Fin (n + 3))
    (x : signedSimplexDomain (n + 1))
    (hx : DifferentiableAt ℝ (signedFacetFunction n σ i) x.val) :
    DifferentiableAt ℝ (signedFacetRadialFactor n σ i) x.val := by
  have hV : DifferentiableAt ℝ (signedFacetEuclidean n i) x.val :=
    (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm.hasFDerivAt.differentiableAt.comp x.val
      (signedFacetVector_hasFDerivAt (n + 1) i x.val).differentiableAt
  have hVne : signedFacetEuclidean n i x.val ≠ 0 := by
    rw [signedFacetEuclidean_eq_centered]
    exact centeredSimplexVector_face_ne_zero n i _
  have hcoord : DifferentiableAt ℝ
      (fun z => Fin.cons (α := fun _ => ℝ) 1 (signedFacetFunction n σ i z)) x.val := by
    apply differentiableAt_pi.mpr
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact differentiableAt_const _
    · exact (differentiableAt_pi.mp hx) k
  have hU : DifferentiableAt ℝ
      (fun z => signedUpperVector (n + 1) (signedFacetFunction n σ i z)) x.val :=
    (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm.hasFDerivAt.differentiableAt.comp x.val hcoord
  have hUne : signedUpperVector (n + 1) (signedFacetFunction n σ i x.val) ≠ 0 :=
    signedUpperVector_ne_zero (n + 1) (signedFacetFunction n σ i x.val)
  have hnV : DifferentiableAt ℝ (fun z => ‖signedFacetEuclidean n i z‖) x.val :=
    hV.norm ℝ hVne
  have hnU : DifferentiableAt ℝ
      (fun z => ‖signedUpperVector (n + 1) (signedFacetFunction n σ i z)‖) x.val :=
    hU.norm ℝ hUne
  have hnorm : ‖signedUpperVector (n + 1) (signedFacetFunction n σ i x.val)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hUne
  change DifferentiableAt ℝ
    (fun z => ‖signedFacetEuclidean n i z‖ / ‖signedUpperVector (n + 1) (signedFacetFunction n σ i z)‖) x.val
  simp only [div_eq_mul_inv]
  exact hnV.mul (hnU.fun_inv hnorm)

theorem signedFacetCone_determinant (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) {L : ℝ≥0} (hσ : LipschitzWith L σ)
    (i : Fin (n + 3)) (x : signedSimplexDomain (n + 1))
    (hxi : x.val ∈ interior (signedSimplexDomain (n + 1)))
    (hxf : DifferentiableAt ℝ (signedFacetFunction n σ i) x.val) {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (unitSphereCone (signedSimplexBoundaryMap n σ))
      (r • signedFacetEuclidean n i x.val) ∧
      ∃ c : ℝ, 0 < c ∧
        (fderiv ℝ (unitSphereCone (signedSimplexBoundaryMap n σ))
          (r • signedFacetEuclidean n i x.val)).det =
        Int.negOnePow (i.val : ℤ) • (c * (fderiv ℝ (signedFacetFunction n σ i) x.val).det) := by
  let e := EuclideanSpace.equiv (Fin (n + 2)) ℝ
  let G := unitSphereCone (signedSimplexBoundaryMap n σ)
  let F := coordinateMapConjugate e G
  let u : Fin (n + 2) → ℝ := Fin.cons r x.val
  let T := signedTailLinear (n + 1)
  have hR : ∀ᶠ z in 𝓝 u, 0 < z 0 := by
    apply (continuous_apply 0).continuousAt.preimage_mem_nhds
    exact IsOpen.mem_nhds isOpen_Ioi hr
  have hT : ∀ᶠ z in 𝓝 u, T z ∈ signedSimplexDomain (n + 1) :=
    T.toContinuousLinearMap.continuous.continuousAt.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hxi)
  have heq : ∀ᶠ z in 𝓝 u,
      F (signedFacetRay (n + 1) i z) = signedTargetRay (n + 1)
        (signedRayTransport (n + 1) (signedFacetRadialFactor n σ i) (signedFacetFunction n σ i) z) := by
    filter_upwards [hR, hT] with z hz hzT
    let b : signedSimplexDomain (n + 1) := ⟨T z, hzT⟩
    have hb : Fin.cons (z 0) b.val = z := by
      funext j
      refine Fin.cases rfl (fun _ => rfl) j
    simpa only [hb] using signedFacetRay_actual_semiconjugacy n σ hσ i b hz
  obtain ⟨hF, c, hc, hdet⟩ := det_of_signedFacetRay_semiconjugacy (n + 1) i
    (u := u) hr (signedFacetRadialFactor_pos n σ i x)
    (signedFacetRadialFactor_differentiableAt n σ i x hxf) hxf heq
  let v := r • signedFacetEuclidean n i x.val
  have hv : e v = signedFacetRay (n + 1) i u := by
    rw [e.map_smul]
    change r • e (e.symm (signedFacetVector (n + 1) i x.val)) = _
    rw [e.apply_symm_apply]
    rfl
  rw [← hv] at hF hdet
  have hG : G = e.symm ∘ F ∘ e := by
    funext z
    simp [F, coordinateMapConjugate]
  refine ⟨?_, c, hc, ?_⟩
  · change DifferentiableAt ℝ G v
    rw [hG]
    exact e.symm.hasFDerivAt.differentiableAt.comp v
      (hF.comp v e.hasFDerivAt.differentiableAt)
  · change (fderiv ℝ G v).det = _
    rw [← det_fderiv_coordinateConjugate e G v]
    exact hdet

end BanachIsometric.SingularPrism
