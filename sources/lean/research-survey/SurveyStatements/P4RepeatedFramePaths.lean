import SurveyStatements.P4FinitePath
import SurveyStatements.P4PeriodicFiniteSums

/-! Repeated basis frames inside the actual finite coefficient-path norm. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set Finset Module

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [FiniteDimensional 𝕜 E]
variable {N : ℕ}

def periodicFinIndex (hN : 0 < N) (i : ℕ) : Fin N := ⟨i % N, Nat.mod_lt _ hN⟩

lemma periodicFinIndex_add (hN : 0 < N) (i : ℕ) :
    periodicFinIndex hN (i + N) = periodicFinIndex hN i := by
  apply Fin.ext
  simp [periodicFinIndex]

def repeatedPathVectors (b : Basis (Fin N) 𝕜 E) (m : ℕ) (hN : 0 < N) :
    Fin (m * N) → E := fun i => b (periodicFinIndex hN i.val)

def repeatedPathCoefficients (b : Basis (Fin N) 𝕜 E) (m : ℕ) (hN : 0 < N) :
    E →ₗ[𝕜] (Fin (m * N) → 𝕜) :=
  LinearMap.pi fun i => (↑(1 / m : ℝ) : 𝕜) • b.coord (periodicFinIndex hN i.val)

def repeatedPathLinearMap (b : Basis (Fin N) 𝕜 E) (m : ℕ) (hN : 0 < N) :
    E →ₗ[𝕜] (Fin (m * N + 1) → E) :=
  (finitePrefixPath (repeatedPathVectors b m hN)).comp (repeatedPathCoefficients b m hN)

lemma sum_range_cutoff {A : Type*} [AddCommMonoid A] (f : ℕ → A) {k L : ℕ}
    (hk : k ≤ L) : (∑ i ∈ range L, if i < k then f i else 0) = ∑ i ∈ range k, f i := by
  rw [← sum_filter]
  have heq : (range L).filter (fun i => i < k) = range k := by
    ext i
    simp only [mem_filter, Finset.mem_range]
    omega
  rw [heq]

lemma repeatedPathLinearMap_apply (b : Basis (Fin N) 𝕜 E) (m : ℕ) (hN : 0 < N)
    (x : E) (k : Fin (m * N + 1)) :
    repeatedPathLinearMap b m hN x k =
      (1 / m : ℝ) • ∑ i ∈ range k.val, basisRankOne b (periodicFinIndex hN i) x := by
  change (∑ i : Fin (m * N), if i.val < k.val then
      ((↑(1 / m : ℝ) : 𝕜) * b.repr x (periodicFinIndex hN i.val)) •
        b (periodicFinIndex hN i.val) else 0) = _
  simp only [mul_smul, ← RCLike.real_smul_eq_coe_smul, smul_assoc]
  change (∑ i : Fin (m * N), if i.val < k.val then
      (1 / m : ℝ) • basisRankOne b (periodicFinIndex hN i.val) x else 0) = _
  have heq : (∑ i : Fin (m * N), if i.val < k.val then
      (1 / m : ℝ) • basisRankOne b (periodicFinIndex hN i.val) x else 0) =
      (1 / m : ℝ) • ∑ i : Fin (m * N),
        if i.val < k.val then basisRankOne b (periodicFinIndex hN i.val) x else 0 := by
    rw [Finset.smul_sum]
    apply sum_congr rfl
    intro i hi
    by_cases h : i.val < k.val <;> simp [h]
  rw [heq, Fin.sum_univ_eq_sum_range
    (fun i => if i < k.val then basisRankOne b (periodicFinIndex hN i) x else 0),
    sum_range_cutoff _ (by omega : k.val ≤ m * N)]

lemma sum_periodic_basisRankOne_block (b : Basis (Fin N) 𝕜 E) (hN : 0 < N) (x : E) :
    (∑ i ∈ range N, basisRankOne b (periodicFinIndex hN i) x) = x := by
  rw [← Fin.sum_univ_eq_sum_range]
  have heq : (fun i : Fin N => basisRankOne b (periodicFinIndex hN i.val) x) =
      (fun i : Fin N => basisRankOne b i x) := by
    funext i
    have hi : periodicFinIndex hN i.val = i := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt i.isLt
    rw [hi]
  rw [heq]
  simpa using b.sum_repr x

lemma repeatedPathLinearMap_last (b : Basis (Fin N) 𝕜 E) {m : ℕ}
    (hm : 0 < m) (hN : 0 < N) (x : E) :
    repeatedPathLinearMap b m hN x (Fin.last (m * N)) = x := by
  rw [repeatedPathLinearMap_apply]
  have hp : ∀ i, basisRankOne b (periodicFinIndex hN (i + N)) x =
      basisRankOne b (periodicFinIndex hN i) x := by
    intro i
    rw [periodicFinIndex_add]
  rw [Fin.val_last, sum_periodic_nat_blocks _ hp, sum_periodic_basisRankOne_block]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp [hm']

lemma sum_periodic_basisRankOne_tail (b : Basis (Fin N) 𝕜 E) (hN : 0 < N)
    {t : ℕ} (ht : t ≤ N) (x : E) :
    (∑ i ∈ range t, basisRankOne b (periodicFinIndex hN i) x) =
      ∑ i ∈ univ.filter (fun i : Fin N => i.val < t), basisRankOne b i x := by
  rw [sum_filter]
  rw [← sum_range_cutoff (fun i => basisRankOne b (periodicFinIndex hN i) x) ht,
    ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  have heq : periodicFinIndex hN i.val = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  rw [heq]

/-- Repeating the identity frame sufficiently often gives an embedding into
the coefficient-path norm with one uniform bound, independent of dimension. -/
lemma repeatedPathLinearMap_norm_le (b : Basis (Fin N) 𝕜 E) {m : ℕ}
    (hm : 0 < m) (hN : 0 < N) (hbound : basisFrameBound b ≤ m) (x : E) :
    ‖repeatedPathLinearMap b m hN x‖ ≤ 2 * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  rw [repeatedPathLinearMap_apply]
  have hp : ∀ i, basisRankOne b (periodicFinIndex hN (i + N)) x =
      basisRankOne b (periodicFinIndex hN i) x := by
    intro i
    rw [periodicFinIndex_add]
  have hk : k.val ≤ m * N := Nat.le_of_lt_succ k.isLt
  have hr : k.val / N ≤ m := by
    calc
      k.val / N ≤ (m * N) / N := Nat.div_le_div_right hk
      _ = m := Nat.mul_div_cancel m hN
  have hsplit : k.val = (k.val / N) * N + k.val % N := by
    exact (Nat.div_add_mod k.val N).symm.trans (by rw [Nat.mul_comm])
  rw [hsplit, sum_periodic_nat_prefix _ hp, sum_periodic_basisRankOne_block,
    sum_periodic_basisRankOne_tail b hN (Nat.le_of_lt (Nat.mod_lt _ hN)), smul_add]
  have heq : (1 / m : ℝ) • ((k.val / N) • x) = (↑(k.val / N) / m : ℝ) • x := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    ring
  rw [heq]
  simpa only [repeatedFramePrefix, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.sum_apply] using repeatedFramePrefix_norm_le b hm hr hbound
      (univ.filter (fun i : Fin N => i.val < k.val % N)) x

end SurveyStatements.P4
