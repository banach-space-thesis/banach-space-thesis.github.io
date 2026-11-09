import BanachIsometric.LipschitzSingularCone

/-! The actual cone of a positive-dimensional Lipschitz chain satisfies the
ordinary singular boundary identity, with the cone apex as first vertex. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem face_value_succAbove {n : ℕ} (i : Fin (n + 2)) (w : Simplex n) (j : Fin (n + 1)) :
    (face i w) (i.succAbove j) = w j := by
  change (face i w).val (i.succAbove j) = w.val j
  rw [signedFace_barycentric, Fin.insertNth_apply_succAbove]

theorem face_value_missing {n : ℕ} (i : Fin (n + 2)) (w : Simplex n) : (face i w) i = 0 := by
  change (face i w).val i = 0
  rw [signedFace_barycentric, Fin.insertNth_apply_same]

theorem simplexConeRadius_face_succ (n : ℕ) (i : Fin (n + 2)) (w : Simplex (n + 1)) :
    simplexConeRadius (n + 1) (face i.succ w) = simplexConeRadius n w := by
  unfold simplexConeRadius
  rw [show (face i.succ w) 0 = w 0 from by
    simpa only [Fin.succ_succAbove_zero] using face_value_succAbove i.succ w 0]

theorem simplexConeBase_face_succ (n : ℕ) (i : Fin (n + 2)) (w : Simplex (n + 1))
    (hw : 0 < simplexConeRadius n w) :
    simplexConeBase (n + 1) (face i.succ w)
      ((simplexConeRadius_face_succ n i w).symm ▸ hw) = face i (simplexConeBase n w hw) := by
  apply Subtype.ext
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · change (face i.succ w) i.succ / simplexConeRadius (n + 1) (face i.succ w) =
      (face i (simplexConeBase n w hw)) i
    rw [face_value_missing, face_value_missing, zero_div]
  · change (face i.succ w) (i.succAbove k).succ / simplexConeRadius (n + 1) (face i.succ w) =
      (face i (simplexConeBase n w hw)) (i.succAbove k)
    rw [simplexConeRadius_face_succ, ← Fin.succ_succAbove_succ, face_value_succAbove, face_value_succAbove]
    rfl

theorem lipschitzSingularCone_face_zero (n : ℕ) (σ : RawSingularSimplex V n)
    (hσ : ∃ L : ℝ≥0, LipschitzWith L σ) :
    (lipschitzSingularCone n σ).comp (face 0) = σ := by
  apply ContinuousMap.ext
  intro w
  have hr : simplexConeRadius n (face 0 w) = 1 := by
    unfold simplexConeRadius
    rw [face_value_missing, sub_zero]
  have hp : 0 < simplexConeRadius n (face 0 w) := hr.symm ▸ zero_lt_one
  have hb : simplexConeBase n (face 0 w) hp = w := by
    apply Subtype.ext
    funext j
    change (face 0 w) j.succ / simplexConeRadius n (face 0 w) = w j
    rw [hr, div_one]
    exact face_value_succAbove 0 w j
  change lipschitzSingularCone n σ (face 0 w) = σ w
  rw [lipschitzSingularCone_apply n σ hσ, singularConeFun, dif_pos hp, hb, hr, one_smul]

theorem lipschitzSingularCone_face_succ (n : ℕ) (σ : RawSingularSimplex V (n + 1))
    (hσ : ∃ L : ℝ≥0, LipschitzWith L σ) (i : Fin (n + 2)) :
    (lipschitzSingularCone (n + 1) σ).comp (face i.succ) =
      lipschitzSingularCone n (σ.comp (face i)) := by
  obtain ⟨L, hL⟩ := hσ
  obtain ⟨M, hM⟩ := exists_lipschitz_face i
  apply ContinuousMap.ext
  intro w
  change lipschitzSingularCone (n + 1) σ (face i.succ w) = lipschitzSingularCone n (σ.comp (face i)) w
  rw [lipschitzSingularCone_apply (n + 1) σ ⟨L, hL⟩,
    lipschitzSingularCone_apply n _ ⟨L * M, hL.comp hM⟩]
  by_cases hw : 0 < simplexConeRadius n w
  · have hp : 0 < simplexConeRadius (n + 1) (face i.succ w) :=
      (simplexConeRadius_face_succ n i w).symm ▸ hw
    rw [singularConeFun, dif_pos hp, singularConeFun, dif_pos hw, simplexConeBase_face_succ,
      simplexConeRadius_face_succ]
    rfl
  · have hp : ¬ 0 < simplexConeRadius (n + 1) (face i.succ w) :=
      (simplexConeRadius_face_succ n i w).symm ▸ hw
    rw [singularConeFun, dif_neg hp, singularConeFun, dif_neg hw]

theorem rawBoundary_rawLipschitzCone_single (n : ℕ) (σ : RawSingularSimplex V (n + 1))
    (hσ : ∃ L : ℝ≥0, LipschitzWith L σ) (a : ℚ) :
    rawBoundary (n + 1) (rawLipschitzCone (n + 1) (Finsupp.single σ a)) =
      Finsupp.single σ a - rawLipschitzCone n (rawBoundary n (Finsupp.single σ a)) := by
  rw [rawLipschitzCone_single, rawBoundary_single, Fin.sum_univ_succ,
    lipschitzSingularCone_face_zero (n + 1) σ hσ, rawBoundary_single, map_sum]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul,
    map_zsmul, rawLipschitzCone_single, lipschitzSingularCone_face_succ n σ hσ]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]

theorem rawBoundary_rawLipschitzCone (n : ℕ) (c : RawRationalChains V (n + 1))
    (hc : c ∈ rawLipschitzCarrier V (n + 1)) :
    rawBoundary (n + 1) (rawLipschitzCone (n + 1) c) = c - rawLipschitzCone n (rawBoundary n c) := by
  let A := (rawBoundary (X := V) (n + 1)).comp (rawLipschitzCone (n + 1))
  let B := LinearMap.id - (rawLipschitzCone n).comp (rawBoundary (X := V) n)
  have hsub : rawLipschitzCarrier V (n + 1) ≤ LinearMap.ker (A - B) := by
    rw [rawLipschitzCarrier, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change (A - B) (Finsupp.single σ 1) = 0
    exact sub_eq_zero.mpr (rawBoundary_rawLipschitzCone_single n σ hσ 1)
  have hz := hsub hc
  change (A - B) c = 0 at hz
  exact sub_eq_zero.mp hz

end BanachIsometric.SingularPrism
