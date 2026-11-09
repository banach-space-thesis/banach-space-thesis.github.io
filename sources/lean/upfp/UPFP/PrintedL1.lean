import ThesisCommon.Analysis.L1EllOneFiniteInterference
import ThesisCommon.Analysis.LebesgueLpRestrictionAlgebra
import ThesisCommon.Analysis.IntervalAtomlessFiniteL1Equiv
import ThesisCommon.Analysis.PrimaryIsomorphism
import ThesisCommon.Analysis.LpFamilyDiagonal

/-! The actual measurable parts and operators in UPFP Lemma 6.3 and
Proposition 6.6. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Cardinal
namespace UPFP.Printed
open ThesisCommon
set_option maxHeartbeats 2000000

abbrev IntervalL1 (𝕜 : Type*) [RCLike 𝕜] := Lp 𝕜 1 (volume : Measure UnitInterval)
abbrev IntervalL1Part (𝕜 : Type*) [RCLike 𝕜] (B : Set UnitInterval) :=
  Lp 𝕜 1 ((volume : Measure UnitInterval).restrict B)

variable {𝕜 Λ : Type*} [RCLike 𝕜]

/-- The canonical zero extension of an actual measurable part. -/
def intervalPartExtend (B : Set UnitInterval) (hB : MeasurableSet B) :
    IntervalL1Part 𝕜 B →L[𝕜] IntervalL1 𝕜 :=
  (lebesgueLpExtend (𝕜 := 𝕜) (p := 1) (μ := (volume : Measure UnitInterval))
    B hB).toContinuousLinearMap

theorem norm_intervalPartExtend_le (B : Set UnitInterval) (hB : MeasurableSet B) :
    ‖intervalPartExtend (𝕜 := 𝕜) B hB‖ ≤ 1 :=
  (lebesgueLpExtend (𝕜 := 𝕜) (E := 𝕜) (p := 1)
    (μ := (volume : Measure UnitInterval)) B hB).norm_toContinuousLinearMap_le

private theorem extend_bound_of_cut
    (T : IntervalL1 𝕜 →L[𝕜] EllOneSum Λ (IntervalL1 𝕜))
    (F : Finset Λ) (B : Set UnitInterval) (hB : MeasurableSet B) {r : ℝ}
    (h : ‖(lpCoordinateProjection 1 (↑F : Set Λ)ᶜ).comp (T.comp (lpCutL B hB))‖ ≤ r) :
    ‖(lpCoordinateProjection 1 (↑F : Set Λ)ᶜ).comp
      (T.comp (intervalPartExtend (𝕜 := 𝕜) B hB))‖ ≤ r := by
  let J : IntervalL1Part 𝕜 B →L[𝕜] IntervalL1 𝕜 :=
    intervalPartExtend B hB
  let Q := lpCoordinateProjection (𝕜 := 𝕜) (X := IntervalL1 𝕜) 1 (↑F : Set Λ)ᶜ
  have hj : (lpCutL B hB).comp J = J := by
    dsimp only [J, intervalPartExtend]
    rw [← lebesgueLpExtend_comp_restrict, ContinuousLinearMap.comp_assoc,
      lebesgueLpRestrict_comp_extend]
    rfl
  change ‖Q.comp (T.comp J)‖ ≤ r
  have he : (Q.comp (T.comp (lpCutL B hB))).comp J = Q.comp (T.comp J) := by
    simp only [ContinuousLinearMap.comp_assoc, hj]
  rw [← he]
  exact (norm_comp_right_contraction (Q.comp (T.comp (lpCutL B hB))) J
    (norm_intervalPartExtend_le B hB)).trans h

/-- Lemma 6.3, real scalars, with the strict bound and actual zero extension. -/
theorem lemma_6_3_real (T : IntervalL1 ℝ →L[ℝ] EllOneSum Λ (IntervalL1 ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∃ (F : Finset Λ) (B : Set UnitInterval) (hB : MeasurableSet B),
      0 < volume B ∧ ‖(lpCoordinateProjection 1 (↑F : Set Λ)ᶜ).comp
        (T.comp (intervalPartExtend (𝕜 := ℝ) B hB))‖ < η := by
  obtain ⟨F, B, _, hB, hp, hn⟩ := realL1_ellOne_finite_interference
    (X := UnitInterval) (Z := UnitInterval) (I := Λ) (μ := (volume : Measure UnitInterval))
    volume T univ MeasurableSet.univ (by simp) (η / 2) (half_pos hη)
  exact ⟨F, B, hB, hp, (extend_bound_of_cut T F B hB hn).trans_lt (half_lt_self hη)⟩

/-- Lemma 6.3, complex scalars. -/
theorem lemma_6_3_complex (T : IntervalL1 ℂ →L[ℂ] EllOneSum Λ (IntervalL1 ℂ))
    {η : ℝ} (hη : 0 < η) :
    ∃ (F : Finset Λ) (B : Set UnitInterval) (hB : MeasurableSet B),
      0 < volume B ∧ ‖(lpCoordinateProjection 1 (↑F : Set Λ)ᶜ).comp
        (T.comp (intervalPartExtend (𝕜 := ℂ) B hB))‖ < η := by
  obtain ⟨F, B, _, hB, hp, hn⟩ := complexL1_ellOne_finite_interference
    (X := UnitInterval) (Z := UnitInterval) (I := Λ) (μ := (volume : Measure UnitInterval))
    volume T univ MeasurableSet.univ (by simp) (η / 2) (half_pos hη)
  exact ⟨F, B, hB, hp, (extend_bound_of_cut T F B hB hn).trans_lt (half_lt_self hη)⟩

/-- Proposition 6.6 for actual measurable parts of positive measure. The
coordinatewise isometries preserve the printed constant, without perturbation. -/
theorem proposition_6_6 (hΛ : Cardinal.aleph0 < Cardinal.mk Λ)
    (B : Λ → Set UnitInterval) (_hB : ∀ i, MeasurableSet (B i))
    (hp : ∀ i, 0 < volume (B i)) {C : ℝ} (hC : 1 ≤ C)
    (hX : HasCPFP 𝕜 (IntervalLp 𝕜 ⟨1, le_rfl⟩) C)
    (D : lp (fun i => IntervalL1Part 𝕜 (B i)) 1 →L[𝕜]
      lp (fun i => IntervalL1Part 𝕜 (B i)) 1)
    (hD : ∃ G : ∀ i, IntervalL1Part 𝕜 (B i) →L[𝕜] IntervalL1Part 𝕜 (B i),
      ∀ x i, D x i = G i (x i)) :
    FactorsIdentityWith D (lp (fun i => IntervalL1Part 𝕜 (B i)) 1) C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - D)
        (lp (fun i => IntervalL1Part 𝕜 (B i)) 1) C := by
  classical
  obtain ⟨G, hG⟩ := hD
  let Z := IntervalLp 𝕜 ⟨1, le_rfl⟩
  let Y := lp (fun i => IntervalL1Part 𝕜 (B i)) 1
  let e (i : Λ) : IntervalL1Part 𝕜 (B i) ≃ₗᵢ[𝕜] Z :=
    intervalAtomlessFiniteL1Equiv 𝕜 (volume.restrict (B i)) (by
      intro hz
      have h := congrArg (fun m : Measure UnitInterval => m univ) hz
      change (volume.restrict (B i)) univ = (0 : Measure UnitInterval) univ at h
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at h
      exact (hp i).ne' (by simpa using h))
  let E := lpFamilyMapEquiv (p := 1) (fun i => (e i).toContinuousLinearEquiv)
    1 1 zero_le_one zero_le_one (fun i => (e i).toLinearIsometry.norm_toContinuousLinearMap_le)
    (fun i => (e i).symm.toLinearIsometry.norm_toContinuousLinearMap_le)
  let A := E.toContinuousLinearMap
  let V := E.symm.toContinuousLinearMap
  have hA : ‖A‖ ≤ 1 := lpFamilyMapEquiv_norm_le _ _ _ _ _ _ _
  have hV : ‖V‖ ≤ 1 := lpFamilyMapEquiv_symm_norm_le _ _ _ _ _ _ _
  have hAV : A.comp V = ContinuousLinearMap.id 𝕜 (EllOneSum Λ Z) := by
    ext x : 1
    exact E.apply_symm_apply x
  let F (i : Λ) : Z →L[𝕜] Z := (e i).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((G i).comp (e i).symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hF (i : Λ) : ‖F i‖ ≤ ‖D‖ := by
    apply (norm_comp_left_contraction _ (e i).toLinearIsometry.norm_toContinuousLinearMap_le _).trans
    apply (norm_comp_right_contraction _ _
      (e i).symm.toLinearIsometry.norm_toContinuousLinearMap_le).trans
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
    intro x
    have hx := lp.norm_apply_le_norm (by simp : (1 : ℝ≥0∞) ≠ 0) (D (lp.single 1 i x)) i
    rw [hG, lp.single_apply_self] at hx
    exact hx.trans ((D.le_opNorm _).trans_eq (by
      rw [lp.norm_single (by simp : (0 : ℝ≥0∞) < 1)]))
  let D' := lpDiagonal 1 F ‖D‖ (norm_nonneg D) hF
  have heq : D' = (A.comp D).comp V := by
    ext x : 1
    apply lp.ext
    funext i
    change F i (x i) = e i (D (V x) i)
    rw [hG]
    rfl
  have pull (T : Y →L[𝕜] Y)
      (hT : FactorsIdentityWith ((A.comp T).comp V) (EllOneSum Λ Z) C) :
      FactorsIdentityWith T Y C := by
    apply ((hT.of_compression A V).target_equiv E.symm).mono
    have hn : ‖A‖ * ‖V‖ ≤ 1 := by
      simpa only [mul_one] using mul_le_mul hA hV (norm_nonneg _) zero_le_one
    have hn' : ‖V‖ * ‖A‖ ≤ 1 := by rwa [mul_comm]
    have hE : ‖E.symm.toContinuousLinearMap‖ * ‖E.symm.symm.toContinuousLinearMap‖ ≤ 1 := by
      simpa only [ContinuousLinearEquiv.symm_symm, A, V] using hn'
    calc
      _ ≤ C * 1 * 1 := by gcongr
      _ = C := by ring
  have hd := ellOne_diagonal_dichotomy_arbitrary hΛ.le (zero_le_one.trans hC) hX
    F ‖D‖ (norm_nonneg D) hF
  change FactorsIdentityWith D' (EllOneSum Λ Z) C ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - D') (EllOneSum Λ Z) C at hd
  rcases hd with hd | hd
  · exact Or.inl (pull D (heq ▸ hd))
  · right
    apply pull (ContinuousLinearMap.id 𝕜 _ - D)
    rw [compression_complement D A V hAV, ← heq]
    exact hd

end UPFP.Printed
