import JLMS.ContinuityIdeal
import JLMS.OrthogonalContinuityExceptions
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Orthogonal projections and the continuity ideal

Only finitely many members of an orthogonal family of projections can lie
outside either the left or the right continuity space. If every projection
generates a fixed element algebraically, that element belongs to the continuity
ideal. This is the consequence of Bade--Curtis needed in Ogden Lemma 6.15.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {B : Type*} [NormedRing B] [NormedSpace 𝕜 B] [CompleteSpace B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]
variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]

theorem orthogonalProjections_leftExceptions_finite (θ : B →ₙₐ[𝕜] A)
    (p : ℕ → B) (hp : ∀ n m, p n * p m = if n = m then p n else 0) :
    {n | p n ∉ leftContinuitySpace θ}.Finite := by
  let f : B →ₗ[𝕜] A := { toFun := θ, map_add' := θ.map_add, map_smul' := θ.map_smul }
  let P (n : ℕ) : B →L[𝕜] B := ContinuousLinearMap.mul 𝕜 B (p n)
  have hP (n m : ℕ) (x : B) : P n (P m x) = if n = m then P n x else 0 := by
    change p n * (p m * x) = _
    rw [← mul_assoc, hp]
    by_cases h : n = m <;> simp [h, P]
  change {n | ¬ Continuous (f.comp (P n).toLinearMap)}.Finite
  exact orthogonalExtraction_exceptions_finite f P hP
    (fun n => ‖θ (p n)‖) (fun n => norm_nonneg _) (fun n x => by
      change ‖θ (p n * x)‖ ≤ _
      rw [map_mul]
      exact norm_mul_le _ _)

theorem orthogonalProjections_rightExceptions_finite (θ : B →ₙₐ[𝕜] A)
    (p : ℕ → B) (hp : ∀ n m, p n * p m = if n = m then p n else 0) :
    {n | p n ∉ rightContinuitySpace θ}.Finite := by
  let f : B →ₗ[𝕜] A := { toFun := θ, map_add' := θ.map_add, map_smul' := θ.map_smul }
  let P (n : ℕ) : B →L[𝕜] B := (ContinuousLinearMap.mul 𝕜 B).flip (p n)
  have hP (n m : ℕ) (x : B) : P n (P m x) = if n = m then P n x else 0 := by
    change (x * p m) * p n = _
    rw [mul_assoc, hp]
    by_cases h : n = m
    · subst m; simp [P]
    · simp [h, Ne.symm h]
  change {n | ¬ Continuous (f.comp (P n).toLinearMap)}.Finite
  exact orthogonalExtraction_exceptions_finite f P hP
    (fun n => ‖θ (p n)‖) (fun n => norm_nonneg _) (fun n x => by
      change ‖θ (x * p n)‖ ≤ _
      rw [map_mul]
      exact (norm_mul_le _ _).trans_eq (mul_comm _ _))

theorem exists_continuityIdeal_orthogonalProjection (θ : B →ₙₐ[𝕜] A)
    (p : ℕ → B) (hp : ∀ n m, p n * p m = if n = m then p n else 0) :
    ∃ n, p n ∈ continuityIdeal θ := by
  have hL := orthogonalProjections_leftExceptions_finite θ p hp
  have hR := orthogonalProjections_rightExceptions_finite θ p hp
  obtain ⟨n, hn⟩ := (hL.union hR).exists_notMem
  refine ⟨n, ?_, ?_⟩
  · by_contra h
    exact hn (Or.inl h)
  · by_contra h
    exact hn (Or.inr h)

theorem continuityIdeal_of_orthogonalProjection_copies (θ : B →ₙₐ[𝕜] A)
    (p : ℕ → B) (hp : ∀ n m, p n * p m = if n = m then p n else 0)
    (q : B) (hq : ∀ n, ∃ a b : B, a * p n * b = q) : q ∈ continuityIdeal θ := by
  obtain ⟨n, hn⟩ := exists_continuityIdeal_orthogonalProjection θ p hp
  obtain ⟨a, b, hab⟩ := hq n
  rw [← hab]
  exact continuityIdeal_mul_right θ b (continuityIdeal_mul_left θ a hn)

end JLMS
