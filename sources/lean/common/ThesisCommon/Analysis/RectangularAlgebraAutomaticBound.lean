import ThesisCommon.Analysis.HomogeneousAutomaticBound

/-! Automatic bounds on the two rectangular modules through a fixed
complemented copy. No topology or completeness is required of the algebra
seminorm; the convergent series live in the original operator spaces. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 E Z : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem exists_left_rectangular_algebra_bound [CompleteSpace Z]
    (J : Z →L[𝕜] E) (P : E →L[𝕜] Z) (hPJ : P.comp J = ContinuousLinearMap.id 𝕜 Z)
    (I Q : ℕ → Z →L[𝕜] Z)
    (hd : ∀ n, (Q n).comp (I n) = ContinuousLinearMap.id 𝕜 Z)
    (ho : ∀ n m, n ≠ m → (Q n).comp (I m) = 0)
    (α : (E →L[𝕜] E) → ℝ) (hn : ∀ T, 0 ≤ α T) (hz : α 0 = 0)
    (hs : ∀ (a : 𝕜) T, α (a • T) = ‖a‖ * α T)
    (hm : ∀ S T, α (S.comp T) ≤ α S * α T) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : E →L[𝕜] Z, α (J.comp U) ≤ C * ‖U‖ := by
  let IL n := ContinuousLinearMap.compL 𝕜 E Z Z (I n)
  let QL n := ContinuousLinearMap.compL 𝕜 E Z Z (Q n)
  let β : (E →L[𝕜] Z) → ℝ := fun U => α (J.comp U)
  apply exists_homogeneous_bound_of_orthogonal_embeddings IL QL
    (fun n => by ext U x; exact congrArg (fun R : Z →L[𝕜] Z => R (U x)) (hd n))
    (fun n m hnm => by
      ext U x
      exact congrArg (fun R : Z →L[𝕜] Z => R (U x)) (ho n m hnm))
    β (fun U => hn _) (by dsimp [β]; simpa using hz)
    (fun a U => by dsimp [β]; rw [ContinuousLinearMap.comp_smul, hs])
    (fun n => α (J.comp ((Q n).comp P))) (fun n => hn _)
  intro n U
  change α (J.comp ((Q n).comp U)) ≤ α (J.comp ((Q n).comp P)) * α (J.comp U)
  have heq : J.comp ((Q n).comp U) = (J.comp ((Q n).comp P)).comp (J.comp U) := by
    simp only [ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc P J U, hPJ, ContinuousLinearMap.id_comp]
  rw [heq]
  exact hm _ _

theorem exists_right_rectangular_algebra_bound [CompleteSpace E]
    (J : Z →L[𝕜] E) (P : E →L[𝕜] Z) (hPJ : P.comp J = ContinuousLinearMap.id 𝕜 Z)
    (I Q : ℕ → Z →L[𝕜] Z)
    (hd : ∀ n, (Q n).comp (I n) = ContinuousLinearMap.id 𝕜 Z)
    (ho : ∀ n m, n ≠ m → (Q n).comp (I m) = 0)
    (α : (E →L[𝕜] E) → ℝ) (hn : ∀ T, 0 ≤ α T) (hz : α 0 = 0)
    (hs : ∀ (a : 𝕜) T, α (a • T) = ‖a‖ * α T)
    (hm : ∀ S T, α (S.comp T) ≤ α S * α T) :
    ∃ D : ℝ, 0 < D ∧ ∀ V : Z →L[𝕜] E, α (V.comp P) ≤ D * ‖V‖ := by
  let IL n := (ContinuousLinearMap.compL 𝕜 Z Z E).flip (Q n)
  let QL n := (ContinuousLinearMap.compL 𝕜 Z Z E).flip (I n)
  let β : (Z →L[𝕜] E) → ℝ := fun V => α (V.comp P)
  apply exists_homogeneous_bound_of_orthogonal_embeddings IL QL
    (fun n => by ext V x; exact congrArg V (congrArg (fun R : Z →L[𝕜] Z => R x) (hd n)))
    (fun n m hnm => by
      ext V x
      change V (((Q m).comp (I n)) x) = 0
      rw [ho m n (Ne.symm hnm)]
      exact map_zero V)
    β (fun V => hn _) (by dsimp [β]; simpa using hz)
    (fun a V => by dsimp [β]; exact hs a (V.comp P))
    (fun n => α (J.comp ((I n).comp P))) (fun n => hn _)
  intro n V
  change α ((V.comp (I n)).comp P) ≤ α (J.comp ((I n).comp P)) * α (V.comp P)
  have heq : (V.comp (I n)).comp P = (V.comp P).comp (J.comp ((I n).comp P)) := by
    simp only [ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc P J _, hPJ, ContinuousLinearMap.id_comp]
  rw [heq]
  exact (hm _ _).trans_eq (mul_comm _ _)

end ThesisCommon
