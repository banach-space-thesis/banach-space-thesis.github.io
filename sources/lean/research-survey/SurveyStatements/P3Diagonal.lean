import SurveyStatements.P3FiniteInterpolation
import SurveyStatements.P3ExtractionGeometry
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! The finite inductive step in the preadjoint extraction construction. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000

namespace SurveyStatements.P3

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A finite stage of the diagonal construction records all cross-pairings. -/
structure DiagonalStage (J : E →ₗᵢ[𝕜] (X →L[𝕜] 𝕜)) (U : E →L[𝕜] (Y →L[𝕜] 𝕜))
    (y : ℕ → Y) (n : ℕ) where
  vectors : Fin n → E
  representatives : Fin n → X
  independent : LinearIndependent 𝕜 vectors
  pairing : ∀ i j : Fin n, U (vectors i) (y j.val) = J (vectors i) (representatives j)
  norm_representative : ∀ j : Fin n, ‖representatives j‖ ≤ 2 * ‖U‖ * ‖y j.val‖

/-- Interpolation controls the new representative, and finite-codimension
kernel escape chooses the new independent vector. -/
theorem diagonal_step_data (J : E →ₗᵢ[𝕜] (X →L[𝕜] 𝕜))
    (U : E →L[𝕜] (Y →L[𝕜] 𝕜)) (hE : ¬ FiniteDimensional 𝕜 E)
    (y : ℕ → Y) {n : ℕ} (s : DiagonalStage J U y n) :
    ∃ (x : X) (e : E),
      ‖x‖ ≤ 2 * ‖U‖ * ‖y n‖ ∧
      e ∉ Submodule.span 𝕜 (Set.range s.vectors) ∧
      (∀ i : Fin n, U (s.vectors i) (y n) = J (s.vectors i) x) ∧
      (∀ j : Fin (n + 1), U e (y j.val) = J e
        ((Fin.snoc s.representatives x : Fin (n + 1) → X) j)) := by
  let F : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range s.vectors)
  letI : FiniteDimensional 𝕜 F := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  let j : F →ₗᵢ[𝕜] (X →L[𝕜] 𝕜) := J.comp F.subtypeₗᵢ
  let φ : F →L[𝕜] 𝕜 :=
    ((ContinuousLinearMap.apply 𝕜 𝕜 (y n)).comp U).comp F.subtypeL
  have hφ : ‖φ‖ ≤ ‖U‖ * ‖y n‖ := by
    apply φ.opNorm_le_bound (mul_nonneg (norm_nonneg U) (norm_nonneg (y n)))
    intro f
    calc
      ‖φ f‖ = ‖U f.val (y n)‖ := rfl
      _ ≤ ‖U f.val‖ * ‖y n‖ := (U f.val).le_opNorm (y n)
      _ ≤ (‖U‖ * ‖f‖) * ‖y n‖ :=
        mul_le_mul_of_nonneg_right (U.le_opNorm f.val) (norm_nonneg _)
      _ = (‖U‖ * ‖y n‖) * ‖f‖ := by rw [mul_right_comm]
  obtain ⟨x, hx, hxnorm⟩ := finite_interpolation_norm_le_two j φ
  have hxbound : ‖x‖ ≤ 2 * ‖U‖ * ‖y n‖ := by
    calc
      ‖x‖ ≤ 2 * ‖φ‖ := hxnorm
      _ ≤ 2 * (‖U‖ * ‖y n‖) := mul_le_mul_of_nonneg_left hφ (by norm_num)
      _ = 2 * ‖U‖ * ‖y n‖ := by rw [mul_assoc]
  let H : E →ₗ[𝕜] (Fin (n + 1) → 𝕜) := LinearMap.pi fun i =>
    (((ContinuousLinearMap.apply 𝕜 𝕜 (y i.val)).comp U) -
      ((ContinuousLinearMap.apply 𝕜 𝕜
        ((Fin.snoc s.representatives x : Fin (n + 1) → X) i)).comp
        J.toContinuousLinearMap)).toLinearMap
  obtain ⟨e, he, heF⟩ := exists_kernel_vector_outside_finite_subspace hE H F
  refine ⟨x, e, hxbound, heF, ?_, ?_⟩
  · intro i
    exact (hx ⟨s.vectors i, Submodule.subset_span (Set.mem_range_self i)⟩).symm
  · intro i
    have h := congrFun he i
    exact sub_eq_zero.mp h

theorem exists_diagonal_stage_extension (J : E →ₗᵢ[𝕜] (X →L[𝕜] 𝕜))
    (U : E →L[𝕜] (Y →L[𝕜] 𝕜)) (hE : ¬ FiniteDimensional 𝕜 E)
    (y : ℕ → Y) {n : ℕ} (s : DiagonalStage J U y n) :
    ∃ t : DiagonalStage J U y (n + 1),
      (∀ i : Fin n, t.vectors i.castSucc = s.vectors i) ∧
      (∀ i : Fin n, t.representatives i.castSucc = s.representatives i) := by
  obtain ⟨x, e, hx, he, hold, hnew⟩ := diagonal_step_data J U hE y s
  let t : DiagonalStage J U y (n + 1) := {
    vectors := Fin.snoc s.vectors e
    representatives := Fin.snoc s.representatives x
    independent := linearIndependent_fin_snoc.mpr ⟨s.independent, he⟩
    pairing := by
      intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Fin.snoc_last] using hnew j
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last] using hold i
        · simpa only [Fin.snoc_castSucc, Fin.coe_castSucc] using s.pairing i j
    norm_representative := by
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Fin.snoc_last, Fin.val_last] using hx
      · simpa only [Fin.snoc_castSucc, Fin.coe_castSucc] using s.norm_representative i }
  refine ⟨t, ?_, ?_⟩
  · intro i
    simp only [t, Fin.snoc_castSucc]
  · intro i
    simp only [t, Fin.snoc_castSucc]

def extendDiagonalStage (J : E →ₗᵢ[𝕜] (X →L[𝕜] 𝕜))
    (U : E →L[𝕜] (Y →L[𝕜] 𝕜)) (hE : ¬ FiniteDimensional 𝕜 E)
    (y : ℕ → Y) {n : ℕ} (s : DiagonalStage J U y n) : DiagonalStage J U y (n + 1) :=
  Classical.choose (exists_diagonal_stage_extension J U hE y s)

theorem extendDiagonalStage_vectors (J : E →ₗᵢ[𝕜] (X →L[𝕜] 𝕜))
    (U : E →L[𝕜] (Y →L[𝕜] 𝕜)) (hE : ¬ FiniteDimensional 𝕜 E)
    (y : ℕ → Y) {n : ℕ} (s : DiagonalStage J U y n) (i : Fin n) :
    (extendDiagonalStage J U hE y s).vectors i.castSucc = s.vectors i :=
  (Classical.choose_spec (exists_diagonal_stage_extension J U hE y s)).1 i

theorem extendDiagonalStage_representatives (J : E →ₗᵢ[𝕜] (X →L[𝕜] 𝕜))
    (U : E →L[𝕜] (Y →L[𝕜] 𝕜)) (hE : ¬ FiniteDimensional 𝕜 E)
    (y : ℕ → Y) {n : ℕ} (s : DiagonalStage J U y n) (i : Fin n) :
    (extendDiagonalStage J U hE y s).representatives i.castSucc = s.representatives i :=
  (Classical.choose_spec (exists_diagonal_stage_extension J U hE y s)).2 i

def diagonalStages (J : E →ₗᵢ[𝕜] (X →L[𝕜] 𝕜))
    (U : E →L[𝕜] (Y →L[𝕜] 𝕜)) (hE : ¬ FiniteDimensional 𝕜 E)
    (y : ℕ → Y) : (n : ℕ) → DiagonalStage J U y n
  | 0 => {
      vectors := Fin.elim0
      representatives := Fin.elim0
      independent := linearIndependent_empty_type
      pairing := fun i => Fin.elim0 i
      norm_representative := fun i => Fin.elim0 i }
  | n + 1 => extendDiagonalStage J U hE y (diagonalStages J U hE y n)

theorem diagonalStages_vectors_coherent (J : E →ₗᵢ[𝕜] (X →L[𝕜] 𝕜))
    (U : E →L[𝕜] (Y →L[𝕜] 𝕜)) (hE : ¬ FiniteDimensional 𝕜 E)
    (y : ℕ → Y) (n : ℕ) (i : Fin n) :
    (diagonalStages J U hE y n).vectors i =
      (diagonalStages J U hE y (i.val + 1)).vectors (Fin.last i.val) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rfl
    · exact (extendDiagonalStage_vectors J U hE y _ k).trans (ih k)

theorem diagonalStages_representatives_coherent (J : E →ₗᵢ[𝕜] (X →L[𝕜] 𝕜))
    (U : E →L[𝕜] (Y →L[𝕜] 𝕜)) (hE : ¬ FiniteDimensional 𝕜 E)
    (y : ℕ → Y) (n : ℕ) (i : Fin n) :
    (diagonalStages J U hE y n).representatives i =
      (diagonalStages J U hE y (i.val + 1)).representatives (Fin.last i.val) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rfl
    · exact (extendDiagonalStage_representatives J U hE y _ k).trans (ih k)

/-- The diagonal recursion produces an independent infinite sequence with
all desired interpolation identities simultaneously. -/
theorem exists_diagonal_sequences (J : E →ₗᵢ[𝕜] (X →L[𝕜] 𝕜))
    (U : E →L[𝕜] (Y →L[𝕜] 𝕜)) (hE : ¬ FiniteDimensional 𝕜 E) (y : ℕ → Y) :
    ∃ (e : ℕ → E) (x : ℕ → X), LinearIndependent 𝕜 e ∧
      (∀ n, ‖x n‖ ≤ 2 * ‖U‖ * ‖y n‖) ∧
      (∀ i j, U (e i) (y j) = J (e i) (x j)) := by
  let e : ℕ → E := fun n => (diagonalStages J U hE y (n + 1)).vectors (Fin.last n)
  let x : ℕ → X := fun n =>
    (diagonalStages J U hE y (n + 1)).representatives (Fin.last n)
  refine ⟨e, x, ?_, ?_, ?_⟩
  · apply linearIndependent_iff_finset_linearIndependent.mpr
    intro t
    let m := t.sup id + 1
    let f : t → Fin m := fun i =>
      ⟨i.val, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact congrArg Fin.val hab
    have hi := (diagonalStages J U hE y m).independent.comp f hf
    have he : (fun i : t => e i.val) = (diagonalStages J U hE y m).vectors ∘ f := by
      funext i
      exact (diagonalStages_vectors_coherent J U hE y m (f i)).symm
    change LinearIndependent 𝕜 (fun i : t => e i.val)
    rw [he]
    exact hi
  · intro n
    exact (diagonalStages J U hE y (n + 1)).norm_representative (Fin.last n)
  · intro i j
    let m := max i j + 1
    let ii : Fin m := ⟨i, Nat.lt_succ_of_le (Nat.le_max_left i j)⟩
    let jj : Fin m := ⟨j, Nat.lt_succ_of_le (Nat.le_max_right i j)⟩
    have hp := (diagonalStages J U hE y m).pairing ii jj
    have he : (diagonalStages J U hE y m).vectors ii = e i :=
      diagonalStages_vectors_coherent J U hE y m ii
    have hx : (diagonalStages J U hE y m).representatives jj = x j :=
      diagonalStages_representatives_coherent J U hE y m jj
    rw [he, hx] at hp
    exact hp

end SurveyStatements.P3
