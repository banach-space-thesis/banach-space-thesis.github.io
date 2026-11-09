import BanachIsometric.SignedSimplexConeFibers
import BanachIsometric.SignedFacetRegularValue
import BanachIsometric.SphereRegularValueDegree

/-! The alternating signed count of a Lipschitz simplex boundary vanishes
almost everywhere. The proof computes the degree of the actual boundary map
into the upper hemisphere at an ordinary regular cone value. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric MeasureTheory
open scoped Topology NNReal

private def facetFiberCoords (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) (i : Fin (n + 3)) (y : Fin (n + 1) → ℝ) :
    SignedFacetFiber n σ i y ≃ {x : Fin (n + 1) → ℝ //
      x ∈ signedSimplexDomain (n + 1) ∧ signedFacetFunction n σ i x = y} where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem signedSimplexBoundaryCount_zero_of_regular_facets (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) {L : ℝ≥0} (hσ : LipschitzWith L σ)
    (y : Fin (n + 1) → ℝ)
    (hreg : ∀ i (x : SignedFacetFiber n σ i y),
      x.val.val ∈ interior (signedSimplexDomain (n + 1)) ∧
      DifferentiableAt ℝ (signedFacetFunction n σ i) x.val.val ∧
      (fderiv ℝ (signedFacetFunction n σ i) x.val.val).det ≠ 0) :
    ∑ i : Fin (n + 3), (-1 : ℝ) ^ (i : ℕ) * signedSimplexCount (n + 1) (σ.comp (face i)) y = 0 := by
  classical
  let e := signedFacetConeFiberEquiv n σ hσ y (fun i x => (hreg i x).1)
  let G := unitSphereCone (signedSimplexBoundaryMap n σ)
  let v := signedSimplexConeTarget n y
  have hdet (a : Σ i : Fin (n + 3), SignedFacetFiber n σ i y) :
      DifferentiableAt ℝ G (e a).val ∧
      ∃ c : ℝ, 0 < c ∧ (fderiv ℝ G (e a).val).det =
        Int.negOnePow (a.1.val : ℤ) • (c * (fderiv ℝ (signedFacetFunction n σ a.1) a.2.val.val).det) := by
    have hv : signedFacetEuclidean n a.1 a.2.val.val ≠ 0 := by
      rw [signedFacetEuclidean_eq_centered]
      exact centeredSimplexVector_face_ne_zero n a.1 _
    have hr : 0 < (1 / 2 : ℝ) / ‖signedFacetEuclidean n a.1 a.2.val.val‖ :=
      div_pos (by norm_num) (norm_pos_iff.mpr hv)
    rw [show (e a).val = _ from signedFacetConeFiberEquiv_apply n σ hσ y _ a]
    exact signedFacetCone_determinant n σ hσ a.1 a.2.val (hreg a.1 a.2).1 (hreg a.1 a.2).2.1 hr
  have hG (z) (hz : z ∈ closedBall 0 1) (hzy : G z = v) :
      DifferentiableAt ℝ G z ∧ (fderiv ℝ G z).det ≠ 0 := by
    let w : SignedBoundaryConeFiber n σ y := ⟨z, hz, hzy⟩
    let a := e.symm w
    have ha : (e a).val = z := congrArg Subtype.val (e.apply_symm_apply w)
    obtain ⟨hD, c, hc, hC⟩ := hdet a
    rw [ha] at hD hC
    refine ⟨hD, ?_⟩
    rw [hC]
    have hne := (hreg a.1 a.2).2.2
    rcases Int.units_eq_one_or (Int.negOnePow (a.1.val : ℤ)) with hs | hs <;>
      simp [hs, hc.ne', hne]
  obtain ⟨C, hC⟩ := exists_lipschitz_signedSimplexBoundaryMap n σ hσ
  have hvball : ‖v‖ < 1 := by rw [norm_signedSimplexConeTarget]; norm_num
  have hzero : signedFiberCount G (fderiv ℝ G) (closedBall 0 1) v = 0 := by
    rw [← sphereSignedDegree_eq_signedFiberCount_of_regular_value
      (EuclideanSpace.equiv (Fin (n + 2)) ℝ) hC hvball hG]
    exact signedSimplexBoundaryMap_degree_zero n σ hσ
  have hfin (i : Fin (n + 3)) : {x : Fin (n + 1) → ℝ |
      x ∈ signedSimplexDomain (n + 1) ∧ signedFacetFunction n σ i x = y}.Finite := by
    obtain ⟨K, hK⟩ := exists_lipschitz_face i
    obtain ⟨M, hM⟩ := (signedSimplexExtension_spec (n + 1) (σ.comp (face i)) ⟨L * K, hσ.comp hK⟩).1
    have h := finite_actual_regular_fiber (isCompact_signedSimplexDomain (n + 1))
      hM.continuous.continuousOn (fun x hx he => (hreg i ⟨⟨x, hx⟩, he⟩).2)
    simpa only [Set.inter_def, Set.mem_preimage, Set.mem_singleton_iff] using h
  letI (i : Fin (n + 3)) : Fintype (SignedFacetFiber n σ i y) :=
    letI : Fintype {x : Fin (n + 1) → ℝ // x ∈ signedSimplexDomain (n + 1) ∧
        signedFacetFunction n σ i x = y} := (hfin i).fintype
    Fintype.ofEquiv _ (facetFiberCoords n σ i y).symm
  letI : Fintype (SignedBoundaryConeFiber n σ y) := Fintype.ofEquiv _ e
  have hfG : {z | z ∈ closedBall 0 1 ∧ G z = v}.Finite := by
    obtain ⟨M, hM⟩ := exists_lipschitz_unitSphereCone hC
    simpa only [Set.inter_def, Set.mem_preimage, Set.mem_singleton_iff] using
      finite_actual_regular_fiber (isCompact_closedBall 0 1) hM.continuous.continuousOn hG
  have hsum0 : signedFiberSum G (fderiv ℝ G) (closedBall 0 1) v = 0 := by
    rw [signedFiberSum_eq_coe_signedFiberCount _ _ _ _ hfG, hzero, Int.cast_zero]
  have horient (a : Σ i : Fin (n + 3), SignedFacetFiber n σ i y) :
      jacobianOrientation (fderiv ℝ G) (e a).val = (-1 : ℝ) ^ (a.1 : ℕ) *
        jacobianOrientation (fderiv ℝ (signedFacetFunction n σ a.1)) a.2.val.val := by
    obtain ⟨_, c, hc, hd⟩ := hdet a
    have hs := Int.cast_negOnePow_natCast ℝ a.1.val
    rw [← hs, jacobianOrientation, hd]
    have hsign (t : ℝ) : SignType.sign (c * t) = SignType.sign t := by
      rw [sign_mul, sign_pos hc, one_mul]
    rcases Int.units_eq_one_or (Int.negOnePow (a.1.val : ℤ)) with hh | hh
    · simp [hh, jacobianOrientation, hsign]
    · simp [hh, jacobianOrientation, Left.sign_neg, hsign]
  have hsumFacet (i : Fin (n + 3)) :
      (∑ x : SignedFacetFiber n σ i y,
        jacobianOrientation (fderiv ℝ (signedFacetFunction n σ i)) x.val.val) =
      signedSimplexCount (n + 1) (σ.comp (face i)) y := by
    change _ = (signedFiberCount (signedFacetFunction n σ i)
      (fderiv ℝ (signedFacetFunction n σ i)) (signedSimplexDomain (n + 1)) y : ℝ)
    rw [← signedFiberSum_eq_coe_signedFiberCount _ _ _ _ (hfin i)]
    change _ = ∑' x : {x : Fin (n + 1) → ℝ // x ∈ signedSimplexDomain (n + 1) ∧
      signedFacetFunction n σ i x = y}, jacobianOrientation (fderiv ℝ (signedFacetFunction n σ i)) x.val
    rw [← (facetFiberCoords n σ i y).tsum_eq]
    rw [tsum_fintype]
    rfl
  calc
    _ = ∑ i : Fin (n + 3), ∑ x : SignedFacetFiber n σ i y,
        (-1 : ℝ) ^ (i : ℕ) * jacobianOrientation (fderiv ℝ (signedFacetFunction n σ i)) x.val.val := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, hsumFacet]
    _ = ∑ a : Σ i : Fin (n + 3), SignedFacetFiber n σ i y,
        jacobianOrientation (fderiv ℝ G) (e a).val := by
      simp only [horient, Fintype.sum_sigma]
    _ = signedFiberSum G (fderiv ℝ G) (closedBall 0 1) v := by
      unfold signedFiberSum
      rw [← e.tsum_eq, tsum_fintype]
    _ = 0 := hsum0

theorem ae_signedSimplexBoundaryCount_zero (n : ℕ) (μ : Measure (Fin (n + 1) → ℝ))
    [μ.IsAddHaarMeasure] (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2))
    {L : ℝ≥0} (hσ : LipschitzWith L σ) :
    ∀ᵐ y ∂μ, rawSignedSimplexCount (n + 1) (rawBoundary (n + 1) (Finsupp.single σ 1)) y = 0 := by
  have hAE (i : Fin (n + 3)) : ∀ᵐ y ∂μ, ∀ x ∈ signedSimplexDomain (n + 1),
      signedFacetFunction n σ i x = y → x ∈ interior (signedSimplexDomain (n + 1)) ∧
      DifferentiableAt ℝ (signedFacetFunction n σ i) x ∧
      (fderiv ℝ (signedFacetFunction n σ i) x).det ≠ 0 := by
    obtain ⟨K, hK⟩ := exists_lipschitz_face i
    exact signedSimplexExtension_ae_regular_interior (n + 1) μ (σ.comp (face i)) ⟨L * K, hσ.comp hK⟩
  filter_upwards [ae_all_iff.mpr hAE] with y hy
  rw [rawBoundary_single, map_sum, Finset.sum_apply]
  simp only [map_zsmul, rawSignedSimplexCount_single, one_smul, Pi.smul_apply, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact signedSimplexBoundaryCount_zero_of_regular_facets n σ hσ y
    (fun i x => hy i x.val.val x.val.property x.property)

end BanachIsometric.SingularPrism
