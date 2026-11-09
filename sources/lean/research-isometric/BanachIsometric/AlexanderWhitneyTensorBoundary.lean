import BanachIsometric.AlexanderWhitneyTermFaces
import BanachIsometric.AlexanderWhitneyCancellation

/-! The actual tensor-boundary expansion and its signed face cancellation
on each singular simplex, before assembling the full bigraded chain map. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct BigOperators

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem awPureTerm_leftBoundary {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) :
    TensorProduct.map (rawBoundary p) LinearMap.id (awPureTerm σ (p + 1) q (by omega)) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • awLeftFaceTerm h σ i := by
  rw [awPureTerm, TensorProduct.map_tmul, LinearMap.id_apply, rawBoundary_single, TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl
  intro i _
  exact map_zsmul ((TensorProduct.mk ℚ (RawRationalChains X p) (RawRationalChains Y q)).flip
    (Finsupp.single (simplexBackProjection σ (p + 1) q (by omega)) 1))
      ((-1 : ℤ) ^ i.val)
      (Finsupp.single ((simplexFrontProjection σ (p + 1) (by omega)).comp (face i)) 1)

theorem awPureTerm_rightBoundary {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) :
    TensorProduct.map LinearMap.id (rawBoundary q) (awPureTerm σ p (q + 1) (by omega)) =
      ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val • awRightFaceTerm h σ j := by
  rw [awPureTerm, TensorProduct.map_tmul, LinearMap.id_apply, rawBoundary_single, TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact map_zsmul (TensorProduct.mk ℚ (RawRationalChains X p) (RawRationalChains Y q)
    (Finsupp.single (simplexFrontProjection σ p (by omega)) 1))
      ((-1 : ℤ) ^ j.val)
      (Finsupp.single ((simplexBackProjection σ p (q + 1) (by omega)).comp (face j)) 1)

theorem rat_neg_one_pow_smul {M : Type*} [AddCommGroup M] [Module ℚ M]
    (p : ℕ) (x : M) : (-1 : ℚ) ^ p • x = (-1 : ℤ) ^ p • x := by
  have h := Int.cast_smul_eq_zsmul ℚ ((-1 : ℤ) ^ p) x
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using h

theorem aw_signed_tensor_boundary (p q : ℕ)
    (σ : RawSingularSimplex (X × Y) (p + q + 1)) :
    (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • awLeftFaceTerm rfl σ i) +
        (-1 : ℤ) ^ p • (∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val • awRightFaceTerm rfl σ j) =
      ∑ r : Fin (p + q + 2), (-1 : ℤ) ^ r.val •
        awPureTerm (σ.comp (face r)) p q rfl := by
  have hsize : (p + 1) + (q + 1) = p + q + 2 := by omega
  let v : Fin ((p + 1) + (q + 1)) → RawTensorChains X Y p q := fun r =>
    awPureTerm (σ.comp (face (Fin.cast hsize r))) p q rfl
  have hleft (i : Fin (p + 1)) : awLeftFaceTerm rfl σ i.castSucc = v (i.castAdd (q + 1)) := by
    have hi : Fin.cast hsize (i.castAdd (q + 1)) = (⟨i.val, by omega⟩ : Fin (p + q + 2)) := by
      apply Fin.ext
      rfl
    change awLeftFaceTerm rfl σ i.castSucc =
      awPureTerm (σ.comp (face (Fin.cast hsize (i.castAdd (q + 1))))) p q rfl
    rw [hi]
    exact (awPureTerm_face_before rfl σ i).symm
  have hright (j : Fin (q + 1)) : awRightFaceTerm rfl σ j.succ = v (Fin.natAdd (p + 1) j) := by
    have hj : Fin.cast hsize (Fin.natAdd (p + 1) j) =
        (⟨p + 1 + j.val, by omega⟩ : Fin (p + q + 2)) := by
      apply Fin.ext
      rfl
    change awRightFaceTerm rfl σ j.succ =
      awPureTerm (σ.comp (face (Fin.cast hsize (Fin.natAdd (p + 1) j)))) p q rfl
    rw [hj]
    exact (awPureTerm_face_after rfl σ j).symm
  have hc := aw_signed_face_cancellation p q (awLeftFaceTerm rfl σ) (awRightFaceTerm rfl σ)
    v hleft hright (aw_middle_face_terms rfl σ)
  refine hc.trans ?_
  apply Fintype.sum_equiv (finCongr hsize)
  intro r
  rfl

end BanachIsometric.SingularAW
