import BanachIsometric.SingularKunnethAssociativity
import BanachIsometric.SingularCrossComponents

/-! The two successive Künneth components of an iterated pure
crossproduct are supported in exactly the expected triple degree. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularAW
open scoped TensorProduct

variable (X Y Z : Type u) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem rawLeftTripleComponent_cross_of_ne {n p q r i j k u₁ : ℕ}
    (h : p + q + r = n) (hinner : i + j = u₁) (houter : u₁ + k = n)
    (hne : ¬ (i = p ∧ j = q ∧ k = r))
    (a : RawHomology X p) (b : RawHomology Y q) (c : RawHomology Z r) :
    TensorProduct.map (rawKunnethHomologyComponent X Y hinner) LinearMap.id
      (rawKunnethHomologyComponent (X × Y) Z houter
        (rawHomologyCross (X × Y) Z h (rawHomologyCross X Y rfl a b) c)) = 0 := by
  by_cases ho : (p + q, r) = (u₁, k)
  · have hu : u₁ = p + q := (congrArg Prod.fst ho).symm
    have hk : k = r := (congrArg Prod.snd ho).symm
    cases hu
    cases hk
    have hi : (p, q) ≠ (i, j) := by
      intro he
      exact hne ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm, rfl⟩
    rw [rawKunnethHomologyComponent_cross, TensorProduct.map_tmul,
      rawKunnethHomologyComponent_cross_of_ne X Y hinner rfl hi, TensorProduct.zero_tmul]
  · rw [rawKunnethHomologyComponent_cross_of_ne (X × Y) Z houter h ho, map_zero]

theorem rawRightTripleComponent_cross_of_ne {n p q r i j k u₁ : ℕ}
    (h : p + (q + r) = n) (hinner : j + k = u₁) (houter : i + u₁ = n)
    (hne : ¬ (i = p ∧ j = q ∧ k = r))
    (a : RawHomology X p) (b : RawHomology Y q) (c : RawHomology Z r) :
    TensorProduct.map LinearMap.id (rawKunnethHomologyComponent Y Z hinner)
      (rawKunnethHomologyComponent X (Y × Z) houter
        (rawHomologyCross X (Y × Z) h a (rawHomologyCross Y Z rfl b c))) = 0 := by
  by_cases ho : (p, q + r) = (i, u₁)
  · have hi : i = p := (congrArg Prod.fst ho).symm
    have hu : u₁ = q + r := (congrArg Prod.snd ho).symm
    cases hi
    cases hu
    have hj : (q, r) ≠ (j, k) := by
      intro he
      exact hne ⟨rfl, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
    rw [rawKunnethHomologyComponent_cross, TensorProduct.map_tmul,
      rawKunnethHomologyComponent_cross_of_ne Y Z hinner rfl hj, TensorProduct.tmul_zero]
  · rw [rawKunnethHomologyComponent_cross_of_ne X (Y × Z) houter h ho, map_zero]

end BanachIsometric.SingularEZ
