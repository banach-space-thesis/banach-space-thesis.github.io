import ThesisCommon.Analysis.StrictlySingularFiniteCoordinates
import ThesisCommon.Analysis.GowersMaureySubspaceBlockSequence
import ThesisCommon.Analysis.GowersMaureyBlockCoefficients

/-! A gliding-hump sequence chosen from the small vectors of an actual
strictly singular operator. The vectors in the given subspace are close
to successive finite blocks and have independently prescribed small images. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem strictlySingular_tail_approximation (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (hT : IsStrictlySingularOperator T)
    (E : Submodule 𝕜 (ShiftSpace D)) (hE : ¬ FiniteDimensional 𝕜 E)
    (B : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ x : C00 𝕜, ∃ y : ShiftSpace D, x ∈ afterCutoff B ∧ y ∈ E ∧
      ‖y‖ = 1 ∧ ‖denseEmbedding D x-y‖ < ε ∧ ‖T y‖ < η := by
  obtain ⟨y, hy, hyn, hyT, hz⟩ := hT.exists_unit_small_annihilating E hE
    (fun i : Fin (B+1) => completedCoordinate D i.val) hη
  obtain ⟨N, hN⟩ := ((initialSum_tendsto D y).eventually
    (Metric.ball_mem_nhds y hε)).exists
  refine ⟨initialCoefficients D N y, y, ?_, hy, hyn, ?_, hyT⟩
  · intro k hk
    rw [initialCoefficients_apply]
    split_ifs <;> simp [hz ⟨k, by omega⟩]
  · simpa only [Metric.mem_ball, dist_eq_norm, denseEmbedding_initialCoefficients] using hN

theorem exists_strictlySingular_block_sequence (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (hT : IsStrictlySingularOperator T)
    (E : Submodule 𝕜 (ShiftSpace D)) (hE : ¬ FiniteDimensional 𝕜 E)
    (ε η : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (hη : ∀ i, 0 < η i)
    (hεanti : Antitone ε) (hηanti : Antitone η) :
    ∃ u : ℕ → C00 𝕜, ∃ v : ℕ → ShiftSpace D,
      (∀ i j, i < j → Before (u i) (u j)) ∧
      (∀ i, v i ∈ E) ∧ (∀ i, ‖v i‖ = 1) ∧
      (∀ i, ‖denseEmbedding D (u i)-v i‖ < ε i) ∧
      (∀ i, (1 : ℝ)/2 ≤ implicitNorm D (u i)) ∧
      (∀ i, ‖T (v i)‖ < η i) := by
  classical
  let P (a : ℕ × C00 𝕜 × ShiftSpace D) :=
    a.2.2 ∈ E ∧ ‖a.2.2‖ = 1 ∧ ‖denseEmbedding D a.2.1-a.2.2‖ < ε a.1 ∧
      (1 : ℝ)/2 ≤ implicitNorm D a.2.1 ∧ ‖T a.2.2‖ < η a.1
  let R (a b : ℕ × C00 𝕜 × ShiftSpace D) := a.1 < b.1 ∧ Before a.2.1 b.2.1
  have hselect : ∀ s : Finset (ℕ × C00 𝕜 × ShiftSpace D), (∀ a ∈ s, P a) →
      ∃ b, P b ∧ ∀ a ∈ s, R a b := by
    intro s _
    let n := s.sup Prod.fst+1
    let B := s.sup (fun a => a.2.1.support.sup id)
    obtain ⟨x, y, hxB, hy, hyn, herr, hyT⟩ :=
      strictlySingular_tail_approximation D T hT E hE B
        (lt_min (by norm_num : (0 : ℝ) < 1/2) (hε n)) (hη n)
    have hxnorm : (1 : ℝ)/2 ≤ implicitNorm D x := by
      have hh := norm_le_insert' y (denseEmbedding D x)
      rw [hyn, norm_sub_rev, denseEmbedding_norm] at hh
      change 1 ≤ implicitNorm D x + ‖denseEmbedding D x-y‖ at hh
      have he := herr.trans_le (min_le_left _ _)
      linarith
    refine ⟨(n,x,y), ⟨hy, hyn, herr.trans_le (min_le_right _ _), hxnorm, hyT⟩, ?_⟩
    intro a ha
    refine ⟨(Finset.le_sup (f := Prod.fst) ha).trans_lt (Nat.lt_succ_self _), ?_⟩
    apply before_of_mem_afterCutoff (K := B) _ hxB
    intro k hk
    exact (Finset.le_sup (f := id) hk).trans
      (Finset.le_sup (f := fun a : ℕ × C00 𝕜 × ShiftSpace D => a.2.1.support.sup id) ha)
  obtain ⟨w, hw, hwr⟩ := exists_seq_of_forall_finset_exists P R hselect
  have hindex : ∀ i : ℕ, i ≤ (w i).1 := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have hh := (hwr i (i+1) (Nat.lt_succ_self i)).1; omega
  exact ⟨fun i => (w i).2.1, fun i => (w i).2.2,
    fun i j hij => (hwr i j hij).2, fun i => (hw i).1,
    fun i => (hw i).2.1, fun i => (hw i).2.2.1.trans_le (hεanti (hindex i)),
    fun i => (hw i).2.2.2.1, fun i => (hw i).2.2.2.2.trans_le (hηanti (hindex i))⟩

theorem restrict_finite_scalar_block_sum {u : ℕ → C00 𝕜}
    (hu : ∀ i j, i < j → Before (u i) (u j)) (s : Finset ℕ) (c : ℕ → 𝕜)
    {i : ℕ} (hi : i ∈ s) :
    restrict (supportInterval (u i)) (∑ j ∈ s, c j • u j) = c i • u i := by
  classical
  rw [map_sum]
  simp_rw [map_smul]
  rw [Finset.sum_eq_single i]
  · rw [restrict_supportInterval]
  · intro j _ hji
    rw [restrict_eq_zero_of_disjoint_supportInterval
      (successive_support_intervals_disjoint_nat hu hji.symm), smul_zero]
  · exact fun h => (h hi).elim

theorem scalar_block_coefficient_le_twice (D : ConstructionData 𝕜)
    {u : ℕ → C00 𝕜} (hu : ∀ i j, i < j → Before (u i) (u j))
    (s : Finset ℕ) (c : ℕ → 𝕜) {i : ℕ} (hi : i ∈ s)
    (hiNorm : (1 : ℝ)/2 ≤ implicitNorm D (u i)) :
    ‖c i‖ ≤ 2 * implicitNorm D (∑ j ∈ s, c j • u j) := by
  have hh := implicitNorm_restrict_le D (supportInterval (u i)) (∑ j ∈ s, c j • u j)
  rw [restrict_finite_scalar_block_sum hu s c hi, map_smul_eq_mul] at hh
  nlinarith [mul_le_mul_of_nonneg_left hiNorm (norm_nonneg (c i))]

end ThesisCommon.GowersMaurey
