import BanachIsometric.HomotopyRepetition

/-! Actual affine half-cube coordinates for the literal cubical concatenation.
Their inverse identities include the clamping operation in Mathlib's
`GenLoop.transAt`; no quotient-level multiplication law replaces these maps. -/

noncomputable section
namespace BanachIsometric
open scoped unitInterval
variable {N : Type*} [DecidableEq N]

def leftHalfCube (i : N) (u : N → unitInterval) : N → unitInterval :=
  Function.update u i ⟨(u i : ℝ) / 2, by constructor <;> linarith [(u i).property.1, (u i).property.2]⟩

def rightHalfCube (i : N) (u : N → unitInterval) : N → unitInterval :=
  Function.update u i ⟨((u i : ℝ) + 1) / 2, by constructor <;> linarith [(u i).property.1, (u i).property.2]⟩

def leftExpandCube (i : N) (u : N → unitInterval) : N → unitInterval :=
  Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))

def rightExpandCube (i : N) (u : N → unitInterval) : N → unitInterval :=
  Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1))

theorem leftExpand_leftHalfCube (i : N) (u : N → unitInterval) :
    leftExpandCube i (leftHalfCube i u) = u := by
  funext j
  by_cases hj : j = i
  · subst j
    apply Subtype.ext
    simp only [leftExpandCube, leftHalfCube, Function.update_self]
    have he : 2 * ((u i : ℝ) / 2) = (u i : ℝ) := by ring
    rw [he, Set.projIcc_of_mem zero_le_one (u i).property]
  · simp [leftExpandCube, leftHalfCube, Function.update_of_ne hj]

theorem rightExpand_rightHalfCube (i : N) (u : N → unitInterval) :
    rightExpandCube i (rightHalfCube i u) = u := by
  funext j
  by_cases hj : j = i
  · subst j
    apply Subtype.ext
    simp only [rightExpandCube, rightHalfCube, Function.update_self]
    have he : 2 * (((u i : ℝ) + 1) / 2) - 1 = (u i : ℝ) := by ring
    rw [he, Set.projIcc_of_mem zero_le_one (u i).property]
  · simp [rightExpandCube, rightHalfCube, Function.update_of_ne hj]

theorem leftHalf_leftExpandCube (i : N) (u : N → unitInterval) (hu : (u i : ℝ) ≤ 1 / 2) :
    leftHalfCube i (leftExpandCube i u) = u := by
  funext j
  by_cases hj : j = i
  · subst j
    apply Subtype.ext
    simp only [leftHalfCube, leftExpandCube, Function.update_self]
    have hmem : 2 * (u i : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [(u i).property.1], by linarith⟩
    rw [Set.projIcc_of_mem zero_le_one hmem]
    ring
  · simp [leftHalfCube, leftExpandCube, Function.update_of_ne hj]

theorem rightHalf_rightExpandCube (i : N) (u : N → unitInterval) (hu : 1 / 2 ≤ (u i : ℝ)) :
    rightHalfCube i (rightExpandCube i u) = u := by
  funext j
  by_cases hj : j = i
  · subst j
    apply Subtype.ext
    simp only [rightHalfCube, rightExpandCube, Function.update_self]
    have hmem : 2 * (u i : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith, by linarith [(u i).property.2]⟩
    rw [Set.projIcc_of_mem zero_le_one hmem]
    ring
  · simp [rightHalfCube, rightExpandCube, Function.update_of_ne hj]

end BanachIsometric
