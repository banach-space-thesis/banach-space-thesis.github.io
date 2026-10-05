import ThesisCommon.Analysis.OperatorModulusSup
import ThesisCommon.Analysis.PositiveConeExtension
import ThesisCommon.Analysis.PositiveOperatorOrder

/-! Scalar Riesz--Kantorovich modulus on the dual of an arbitrary real
normed lattice. No AL norm assumption on the domain is used. -/
noncomputable section
open Set Finset
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]

/-- Selecting the signs of a finite positive decomposition gives the sharp
scalar bound without additivity of the domain norm. -/
theorem PositiveDecomposition.scalar_value_le (φ : E →L[ℝ] ℝ) {x : E}
    (d : PositiveDecomposition x) : d.value φ ≤ ‖φ‖ * ‖x‖ := by
  classical
  let y : d.Index → E := fun i => if 0 ≤ φ (d.part i) then d.part i else -d.part i
  have hy (i : d.Index) : |y i| = d.part i := by
    dsimp [y]
    split <;> simp only [abs_neg, abs_of_nonneg (d.nonneg i)]
  have habs : |∑ i, y i| ≤ x := by
    calc
      |∑ i, y i| ≤ ∑ i, |y i| := lattice_abs_sum_le _ _
      _ = x := by simp_rw [hy]; exact d.sum_eq
  have hx : 0 ≤ x := by rw [← d.sum_eq]; exact sum_nonneg fun i _ => d.nonneg i
  have hnorm : ‖∑ i, y i‖ ≤ ‖x‖ :=
    norm_le_norm_of_abs_le_abs (by simpa only [abs_of_nonneg hx] using habs)
  have heval : φ (∑ i, y i) = d.value φ := by
    rw [map_sum]
    apply sum_congr rfl
    intro i _
    dsimp [y]
    split_ifs with h
    · exact (abs_of_nonneg h).symm
    · rw [map_neg, abs_of_neg (lt_of_not_ge h)]
  calc
    d.value φ = φ (∑ i, y i) := heval.symm
    _ ≤ ‖φ (∑ i, y i)‖ := le_abs_self _
    _ ≤ ‖φ‖ * ‖∑ i, y i‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * ‖x‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg φ)

def dualModulusPos (φ : E →L[ℝ] ℝ) (x : E) (_hx : 0 ≤ x) : ℝ :=
  sSup (modulusCandidates φ x)

theorem dualModulusPos_isLUB (φ : E →L[ℝ] ℝ) (x : E) (hx : 0 ≤ x) :
    IsLUB (modulusCandidates φ x) (dualModulusPos φ x hx) := by
  apply isLUB_csSup
  · exact ⟨(PositiveDecomposition.single x hx).value φ, ⟨_, rfl⟩⟩
  · refine ⟨‖φ‖ * ‖x‖, ?_⟩
    rintro _ ⟨d, rfl⟩
    exact d.scalar_value_le φ

theorem dualModulusPos_dominates (φ : E →L[ℝ] ℝ) (x : E) (hx : 0 ≤ x) :
    |φ x| ≤ dualModulusPos φ x hx := by
  have h := (dualModulusPos_isLUB φ x hx).1
    (show (PositiveDecomposition.single x hx).value φ ∈ modulusCandidates φ x from ⟨_, rfl⟩)
  simpa only [PositiveDecomposition.value_single] using h

theorem dualModulusPos_nonneg (φ : E →L[ℝ] ℝ) (x : E) (hx : 0 ≤ x) :
    0 ≤ dualModulusPos φ x hx := (abs_nonneg _).trans (dualModulusPos_dominates φ x hx)

theorem dualModulusPos_le (φ : E →L[ℝ] ℝ) (x : E) (hx : 0 ≤ x) :
    dualModulusPos φ x hx ≤ ‖φ‖ * ‖x‖ := by
  apply (dualModulusPos_isLUB φ x hx).2
  rintro _ ⟨d, rfl⟩
  exact d.scalar_value_le φ

theorem norm_dualModulusPos_le (φ : E →L[ℝ] ℝ) (x : E) (hx : 0 ≤ x) :
    ‖dualModulusPos φ x hx‖ ≤ ‖φ‖ * ‖x‖ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (dualModulusPos_nonneg φ x hx)]
  exact dualModulusPos_le φ x hx

theorem dualModulusPos_add (φ : E →L[ℝ] ℝ) (x y : E) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    dualModulusPos φ (x + y) (add_nonneg hx hy) =
      dualModulusPos φ x hx + dualModulusPos φ y hy := by
  have hmx := dualModulusPos_isLUB φ x hx
  have hmy := dualModulusPos_isLUB φ y hy
  have hmxy := dualModulusPos_isLUB φ (x + y) (add_nonneg hx hy)
  apply le_antisymm
  · apply hmxy.2
    rintro _ ⟨d, rfl⟩
    obtain ⟨a, b, hd⟩ := d.exists_split_value φ hx hy
    exact hd.trans (add_le_add (hmx.1 ⟨a, rfl⟩) (hmy.1 ⟨b, rfl⟩))
  · have hinner (b : PositiveDecomposition y) :
        dualModulusPos φ x hx + b.value φ ≤ dualModulusPos φ (x + y) (add_nonneg hx hy) := by
      apply le_sub_iff_add_le.mp
      apply hmx.2
      rintro _ ⟨a, rfl⟩
      apply le_sub_iff_add_le.mpr
      have h := hmxy.1 (show (a.append b).value φ ∈ modulusCandidates φ (x + y) from ⟨_, rfl⟩)
      rwa [PositiveDecomposition.value_append] at h
    apply le_sub_iff_add_le'.mp
    apply hmy.2
    rintro _ ⟨b, rfl⟩
    exact le_sub_iff_add_le'.mpr (hinner b)

/-- Every continuous real linear functional has an actual continuous modulus. -/
def dualModulus (φ : E →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  positiveConeExtension (dualModulusPos φ) (dualModulusPos_add φ)
    (norm_nonneg φ) (norm_dualModulusPos_le φ)

theorem dualModulus_apply_of_nonneg (φ : E →L[ℝ] ℝ) (x : E) (hx : 0 ≤ x) :
    dualModulus φ x = dualModulusPos φ x hx :=
  positiveConeExtension_apply_of_nonneg _ _ _ _ x hx

theorem dualModulus_nonneg (φ : E →L[ℝ] ℝ) : 0 ≤ dualModulus φ := by
  intro x hx
  change 0 ≤ dualModulus φ x
  rw [dualModulus_apply_of_nonneg φ x hx]
  exact dualModulusPos_nonneg φ x hx

theorem dualModulus_dominates (φ : E →L[ℝ] ℝ) (x : E) (hx : 0 ≤ x) :
    |φ x| ≤ dualModulus φ x := by
  rw [dualModulus_apply_of_nonneg φ x hx]
  exact dualModulusPos_dominates φ x hx

theorem dualModulus_least (φ R : E →L[ℝ] ℝ)
    (hR : ∀ x : E, 0 ≤ x → |φ x| ≤ R x) : dualModulus φ ≤ R := by
  intro x hx
  rw [dualModulus_apply_of_nonneg φ x hx]
  apply (dualModulusPos_isLUB φ x hx).2
  rintro _ ⟨d, rfl⟩
  calc
    d.value φ ≤ ∑ i, R (d.part i) := sum_le_sum fun i _ => hR _ (d.nonneg i)
    _ = R x := by rw [← map_sum, d.sum_eq]

theorem positive_functional_abs_apply_le {φ : E →L[ℝ] ℝ} (hφ : 0 ≤ φ) (x : E) :
    |φ x| ≤ φ |x| := by
  apply abs_le.mpr
  constructor
  · have h := positive_operator_monotone hφ (neg_le_abs x)
    rw [map_neg] at h
    linarith
  · exact positive_operator_monotone hφ (le_abs_self x)

theorem dualModulus_abs_dominates (φ : E →L[ℝ] ℝ) (x : E) :
    |φ x| ≤ dualModulus φ |x| := by
  calc
    |φ x| = |φ x⁺ - φ x⁻| := by rw [← map_sub, posPart_sub_negPart]
    _ ≤ |φ x⁺| + |φ x⁻| := abs_sub _ _
    _ ≤ dualModulus φ x⁺ + dualModulus φ x⁻ :=
      add_le_add (dualModulus_dominates φ _ (posPart_nonneg x))
        (dualModulus_dominates φ _ (negPart_nonneg x))
    _ = dualModulus φ |x| := by rw [← map_add, posPart_add_negPart]

theorem norm_dualModulus (φ : E →L[ℝ] ℝ) : ‖dualModulus φ‖ = ‖φ‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
    intro x
    rw [Real.norm_eq_abs]
    calc
      |dualModulus φ x| ≤ dualModulus φ |x| := positive_functional_abs_apply_le (dualModulus_nonneg φ) x
      _ = dualModulusPos φ |x| (abs_nonneg x) := dualModulus_apply_of_nonneg φ _ _
      _ ≤ ‖φ‖ * ‖|x|‖ := dualModulusPos_le φ _ _
      _ = ‖φ‖ * ‖x‖ := by rw [norm_abs_eq_norm]
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [Real.norm_eq_abs]
    calc
      |φ x| ≤ dualModulus φ |x| := dualModulus_abs_dominates φ x
      _ ≤ ‖dualModulus φ |x|‖ := le_abs_self _
      _ ≤ ‖dualModulus φ‖ * ‖|x|‖ := (dualModulus φ).le_opNorm _
      _ = ‖dualModulus φ‖ * ‖x‖ := by rw [norm_abs_eq_norm]

end ThesisCommon
