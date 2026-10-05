import ThesisCommon.Analysis.OperatorModulusSup

/-! Additivity of the constructed operator modulus on the positive cone. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
variable [IsOrderedAddMonoid E] [HasSolidNorm E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [Lattice F]
variable [IsOrderedAddMonoid F] [HasSolidNorm F] [CompleteSpace F] [OrderClosedTopology F]

/-- The actual Riesz--Kantorovich modulus value on a positive input. -/
def operatorModulusPos
    (hALE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (hALF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (T : E →L[ℝ] F) (x : E) (hx : 0 ≤ x) : F :=
  (exists_operatorModulus_value hALE hALF T x hx).choose

variable (hALE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
variable (hALF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
variable (T : E →L[ℝ] F)

theorem operatorModulusPos_isLUB (x : E) (hx : 0 ≤ x) :
    IsLUB (modulusCandidates T x) (operatorModulusPos hALE hALF T x hx) :=
  (exists_operatorModulus_value hALE hALF T x hx).choose_spec.1

theorem operatorModulusPos_nonneg (x : E) (hx : 0 ≤ x) :
    0 ≤ operatorModulusPos hALE hALF T x hx :=
  (exists_operatorModulus_value hALE hALF T x hx).choose_spec.2.1

theorem norm_operatorModulusPos_le (x : E) (hx : 0 ≤ x) :
    ‖operatorModulusPos hALE hALF T x hx‖ ≤ ‖T‖ * ‖x‖ :=
  (exists_operatorModulus_value hALE hALF T x hx).choose_spec.2.2

theorem operatorModulusPos_zero : operatorModulusPos hALE hALF T 0 (le_refl 0) = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using norm_operatorModulusPos_le hALE hALF T 0 (le_refl 0)) (norm_nonneg _)

theorem abs_apply_le_operatorModulusPos (x : E) (hx : 0 ≤ x) :
    |T x| ≤ operatorModulusPos hALE hALF T x hx := by
  have h := (operatorModulusPos_isLUB hALE hALF T x hx).1
    (show (PositiveDecomposition.single x hx).value T ∈ modulusCandidates T x from ⟨_, rfl⟩)
  simpa [PositiveDecomposition.value_single] using h

/-- The modulus is additive on positive inputs. Both inequalities are proved
using finite decomposition splitting and concatenation. -/
theorem operatorModulusPos_add (x y : E) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    operatorModulusPos hALE hALF T (x + y) (add_nonneg hx hy) =
      operatorModulusPos hALE hALF T x hx + operatorModulusPos hALE hALF T y hy := by
  let M := operatorModulusPos hALE hALF T
  have hmx := operatorModulusPos_isLUB hALE hALF T x hx
  have hmy := operatorModulusPos_isLUB hALE hALF T y hy
  have hmxy := operatorModulusPos_isLUB hALE hALF T (x + y) (add_nonneg hx hy)
  apply le_antisymm
  · apply hmxy.2
    rintro _ ⟨d, rfl⟩
    obtain ⟨a, b, hd⟩ := d.exists_split_value T hx hy
    exact hd.trans (add_le_add (hmx.1 ⟨a, rfl⟩) (hmy.1 ⟨b, rfl⟩))
  · have hinner (b : PositiveDecomposition y) :
        M x hx + b.value T ≤ M (x + y) (add_nonneg hx hy) := by
      apply le_sub_iff_add_le.mp
      apply hmx.2
      rintro _ ⟨a, rfl⟩
      apply le_sub_iff_add_le.mpr
      have h := hmxy.1 (show (a.append b).value T ∈ modulusCandidates T (x + y) from ⟨_, rfl⟩)
      rwa [PositiveDecomposition.value_append] at h
    apply le_sub_iff_add_le'.mp
    apply hmy.2
    rintro _ ⟨b, rfl⟩
    exact le_sub_iff_add_le'.mpr (hinner b)

end ThesisCommon
