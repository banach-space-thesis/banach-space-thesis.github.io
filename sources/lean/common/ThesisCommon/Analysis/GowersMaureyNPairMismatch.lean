import ThesisCommon.Analysis.GowersMaureyMismatchSizes

/-! Mismatched averaged functionals on genuine normalized RIS pairs.
Every high-size hypothesis is explicit: no growth of sigma-codes beyond
their prescribed range and injectivity is assumed. In particular the
cutoff may be the next odd construction size after a special size k. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem averaged_pairing_le_inv_square_of_interval_bound
    (D : ConstructionData 𝕜) {k m : ℕ} (hkm : k < m)
    {a x : C00 𝕜} (ha : AveragedFunctional (implicitNorm D) (D.j m) a)
    (hx : intervalNorm D (D.j m) x ≤ 8) :
    ‖pairing a x‖ ≤ 1 / (D.j k : ℝ)^2 := by
  have hf : 0 < logarithmicWeight (D.j m) :=
    zero_lt_one.trans_le (one_le_logarithmicWeight (D.j_positive m))
  calc
    _ ≤ (logarithmicWeight (D.j m))⁻¹ * intervalNorm D (D.j m) x :=
      ha.isForm.intervalNorm_bound hf x
    _ ≤ (logarithmicWeight (D.j m))⁻¹ * 8 :=
      mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hf.le)
    _ = 8 / logarithmicWeight (D.j m) := by ring
    _ ≤ _ := D.eight_div_weight_le_inv_square hkm

theorem averaged_pairing_normalizedPairVector_le_inv_square_of_large
    (D : ConstructionData 𝕜) {k n m : ℕ} (hkn : k < 2*n+1) (hnm : 2*n+1 < m)
    {u : Fin (D.j (2*n+1)) → C00 𝕜} (hu : IsRIS D 1 u)
    {a : C00 𝕜} (ha : AveragedFunctional (implicitNorm D) (D.j m) a) :
    ‖pairing a (normalizedPairVector u)‖ ≤ 1 / (D.j k : ℝ)^2 := by
  obtain ⟨hu⟩ := hu
  have hM2 : 2 ≤ D.j m := by
    have hh := D.size_large m
    exact_mod_cast (show (2 : ℝ) ≤ D.j m by linarith)
  have hbound := hu.form_bound hM2
    (sqrt_logarithmicWeight_le_weight (D.one_le_size m)) ha.isForm
  have hratio := D.size_div_sqrt_weight_le_one hnm
  have hthree : ‖pairing a (∑ i, u i)‖ ≤ 3 := by linarith
  have hscale : 0 ≤ logarithmicWeight (D.j (2*n+1)) / (D.j (2*n+1) : ℝ) :=
    div_nonneg (logarithmicWeight_nonneg _) (Nat.cast_nonneg _)
  rw [normalizedPairVector, (pairing a).map_smul_of_tower, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hscale]
  calc
    _ ≤ (logarithmicWeight (D.j (2*n+1)) / (D.j (2*n+1) : ℝ)) * 3 :=
      mul_le_mul_of_nonneg_left hthree hscale
    _ = 3 * logarithmicWeight (D.j (2*n+1)) / (D.j (2*n+1) : ℝ) := by ring
    _ ≤ _ := D.three_weight_div_size_le_inv_square hkn

theorem averaged_pairing_normalizedPairVector_le_inv_square
    (D : ConstructionData 𝕜) {k n m : ℕ} (hkn : k < 2*n+1) (hkm : k < m)
    (hmn : m ≠ 2*n+1) {u : Fin (D.j (2*n+1)) → C00 𝕜} (hu : IsRIS D 1 u)
    {a : C00 𝕜} (ha : AveragedFunctional (implicitNorm D) (D.j m) a) :
    ‖pairing a (normalizedPairVector u)‖ ≤ 1 / (D.j k : ℝ)^2 := by
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact averaged_pairing_le_inv_square_of_interval_bound D hkm ha
      (normalizedPairVector_intervalNorm_le_eight n hu (D.j_positive m)
        (D.size_le_sqrt_size hlt))
  · exact averaged_pairing_normalizedPairVector_le_inv_square_of_large D hkn hgt hu ha

/-- High odd sizes above the next odd size after the actual special size j(2t).
This is stronger than requiring both sizes to exceed the printed first seed. -/
theorem averaged_pairing_normalizedPairVector_le_special_inv_square
    (D : ConstructionData 𝕜) {t n m : ℕ} (htn : t ≤ n) (htm : t ≤ m) (hmn : m ≠ n)
    {u : Fin (D.j (2*n+1)) → C00 𝕜} (hu : IsRIS D 1 u)
    {a : C00 𝕜} (ha : AveragedFunctional (implicitNorm D) (D.j (2*m+1)) a) :
    ‖pairing a (normalizedPairVector u)‖ ≤ 1 / (D.j (2*t) : ℝ)^2 :=
  averaged_pairing_normalizedPairVector_le_inv_square D (by omega) (by omega) (by omega) hu ha

end ThesisCommon.GowersMaurey
