import ThesisCommon.Analysis.MatrixHilbertSchmidtBounds
import Mathlib.Logic.Equiv.Fin.Basic

/-! Disjoint finite matrix blocks and the Hilbert--Schmidt averaging step
for the finite-dimensional block projection lemma. All block maps are the
canonical maps on the actual finite ℓp operator spaces. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem lpExtend_single_between {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (e : ι ↪ κ) (i : ι) (a : 𝕜) :
    lpExtend (𝕜 := 𝕜) p e (lp.single p i a) = lp.single p (e i) a := by
  classical
  apply lp.ext
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨k, rfl⟩ := hj
    rw [lpExtend_apply_image]
    by_cases hki : k = i
    · subst k; simp
    · have he : e k ≠ e i := fun h => hki (e.injective h)
      simp [hki, he]
  · have hji : j ≠ e i := fun heq => hj ⟨i, heq.symm⟩
    simp [lpExtend, Function.extend_apply' _ _ _ hj, hji]

@[simp] theorem matrixEntry_restrict (p : BanachExponent) {k N : ℕ}
    (α τ : Fin k ↪ Fin N) (A : FiniteMatrixBlock 𝕜 p N) (i j : Fin k) :
    matrixEntry p i j (matrixRestrict p α τ A) = matrixEntry p (α i) (τ j) A := by
  change A (lpExtend (𝕜 := 𝕜) p.val τ (lp.single p.val j (1 : 𝕜))) (α i) = _
  exact congrArg (fun z : FiniteLpSpace 𝕜 p N => A z (α i))
    (lpExtend_single_between (𝕜 := 𝕜) p.val τ j (1 : 𝕜))

def matrixBlockCoordinateEmbedding {m k N : ℕ} (e : Fin m × Fin k ↪ Fin N)
    (s : Fin m) : Fin k ↪ Fin N :=
  ⟨fun i => e (s, i), fun _ _ h => (Prod.mk.inj (e.injective h)).2⟩

def consecutiveMatrixEmbedding {m k N : ℕ} (hmk : m * k ≤ N) : Fin m × Fin k ↪ Fin N :=
  finProdFinEquiv.toEmbedding.trans (Fin.castLEOrderEmb hmk).toEmbedding

def consecutiveMatrixBlock {m k N : ℕ} (hmk : m * k ≤ N) (s : Fin m) : Fin k ↪o Fin N :=
  OrderEmbedding.ofStrictMono (fun i => consecutiveMatrixEmbedding hmk (s, i)) (by
    intro i j hij
    change i.val + k * s.val < j.val + k * s.val
    exact Nat.add_lt_add_right hij _)

theorem consecutiveMatrixBlock_toEmbedding {m k N : ℕ} (hmk : m * k ≤ N) (s : Fin m) :
    (consecutiveMatrixBlock hmk s).toEmbedding =
      matrixBlockCoordinateEmbedding (consecutiveMatrixEmbedding hmk) s := rfl

theorem matrixBlock_hilbertSchmidt_sum_sq_le (p : BanachExponent) {m k N : ℕ}
    (e : Fin m × Fin k ↪ Fin N) (A : FiniteMatrixBlock 𝕜 p N) :
    ∑ s : Fin m, ∑ t : Fin m,
      matrixHilbertSchmidtNorm p (matrixRestrict p (matrixBlockCoordinateEmbedding e s)
        (matrixBlockCoordinateEmbedding e t) A) ^ 2 ≤ matrixHilbertSchmidtNorm p A ^ 2 := by
  classical
  let f (z : Fin N × Fin N) : ℝ := ‖matrixEntry p z.1 z.2 A‖ ^ 2
  have h := Finset.sum_le_univ_sum_of_nonneg
    (s := Finset.univ.map (e.prodMap e)) (f := f) (fun z => sq_nonneg (‖matrixEntry p z.1 z.2 A‖))
  simp only [Finset.sum_map, Fintype.sum_prod_type, f] at h
  simp only [matrixHilbertSchmidtNorm_sq, matrixEntry_restrict, matrixBlockCoordinateEmbedding]
  convert h using 1
  apply Finset.sum_congr rfl
  intro s _
  exact Finset.sum_comm

theorem exists_small_matrixBlock_finite_family (p : BanachExponent) {m k N L : ℕ}
    (hm : 0 < m) (e : Fin m × Fin k ↪ Fin N) (x : Fin L → FiniteMatrixBlock 𝕜 p N)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbudget : (∑ r : Fin L, matrixHilbertSchmidtNorm p (x r) ^ 2) ≤ (m : ℝ) ^ 2 * δ ^ 2) :
    ∃ s t : Fin m, ∀ r : Fin L,
      matrixHilbertSchmidtNorm p (matrixRestrict p (matrixBlockCoordinateEmbedding e s)
        (matrixBlockCoordinateEmbedding e t) (x r)) ≤ δ := by
  classical
  let F (z : Fin m × Fin m) := ∑ r : Fin L,
    matrixHilbertSchmidtNorm p (matrixRestrict p (matrixBlockCoordinateEmbedding e z.1)
      (matrixBlockCoordinateEmbedding e z.2) (x r)) ^ 2
  have hsum : ∑ z : Fin m × Fin m, F z ≤ ∑ _z : Fin m × Fin m, δ ^ 2 := by
    calc
      _ = ∑ r : Fin L, ∑ s : Fin m, ∑ t : Fin m,
          matrixHilbertSchmidtNorm p (matrixRestrict p (matrixBlockCoordinateEmbedding e s)
            (matrixBlockCoordinateEmbedding e t) (x r)) ^ 2 := by
        simp only [F, Fintype.sum_prod_type]
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))
          (t := (Finset.univ : Finset (Fin L)))]
      _ ≤ ∑ r : Fin L, matrixHilbertSchmidtNorm p (x r) ^ 2 :=
        Finset.sum_le_sum (fun r _ => matrixBlock_hilbertSchmidt_sum_sq_le p e (x r))
      _ ≤ (m : ℝ) ^ 2 * δ ^ 2 := hbudget
      _ = _ := by simp [pow_two, Nat.cast_mul]
  have hne : (Finset.univ : Finset (Fin m × Fin m)).Nonempty :=
    ⟨(⟨0, hm⟩, ⟨0, hm⟩), Finset.mem_univ _⟩
  obtain ⟨z, _, hz⟩ := Finset.exists_le_of_sum_le hne hsum
  refine ⟨z.1, z.2, ?_⟩
  intro r
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hδ).mp
  exact (Finset.single_le_sum (fun i _ => sq_nonneg
    (matrixHilbertSchmidtNorm p (matrixRestrict p (matrixBlockCoordinateEmbedding e z.1)
      (matrixBlockCoordinateEmbedding e z.2) (x i)))) (Finset.mem_univ r)).trans hz

end ThesisCommon
