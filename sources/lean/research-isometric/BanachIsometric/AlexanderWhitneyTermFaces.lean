import BanachIsometric.AlexanderWhitneyFaces

/-! Actual tensor-valued face identities for the front/back singular-chain
terms. These provide all entries in the signed cancellation calculation. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def awLeftFaceTerm {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) (i : Fin (p + 2)) : RawTensorChains X Y p q :=
  Finsupp.single ((simplexFrontProjection σ (p + 1) (by omega)).comp (face i)) 1 ⊗ₜ[ℚ]
    Finsupp.single (simplexBackProjection σ (p + 1) q (by omega)) 1

def awRightFaceTerm {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) (j : Fin (q + 2)) : RawTensorChains X Y p q :=
  Finsupp.single (simplexFrontProjection σ p (by omega)) 1 ⊗ₜ[ℚ]
    Finsupp.single ((simplexBackProjection σ p (q + 1) (by omega)).comp (face j)) 1

theorem awPureTerm_face_before {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) (i : Fin (p + 1)) :
    awPureTerm (σ.comp (face (⟨i.val, by omega⟩ : Fin (n + 2)))) p q h =
      awLeftFaceTerm h σ i.castSucc := by
  unfold awPureTerm awLeftFaceTerm
  have hi : (intervalFaceIndex (s := 0) (by omega : 0 + p ≤ n) i.castSucc) =
      (⟨i.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [intervalFaceIndex, Fin.coe_castSucc, zero_add]
  rw [← hi, simplexFrontProjection_face (by omega)]
  rw [hi, simplexBackProjection_face_before h σ i]

theorem awPureTerm_face_after {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) (j : Fin (q + 1)) :
    awPureTerm (σ.comp (face (⟨p + 1 + j.val, by omega⟩ : Fin (n + 2)))) p q h =
      awRightFaceTerm h σ j.succ := by
  unfold awPureTerm awRightFaceTerm
  rw [simplexFrontProjection_face_after h σ j]
  have hj : intervalFaceIndex h.le j.succ =
      (⟨p + 1 + j.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [intervalFaceIndex, Fin.val_succ]
    omega
  rw [← hj, simplexBackProjection_face h σ j.succ]

theorem aw_middle_face_terms {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) :
    awLeftFaceTerm h σ (Fin.last (p + 1)) = awRightFaceTerm h σ 0 := by
  unfold awLeftFaceTerm awRightFaceTerm
  rw [simplexFrontProjection_face_last (by omega), simplexBackProjection_face_zero (by omega)]

end BanachIsometric.SingularAW
