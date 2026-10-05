import ThesisCommon.Analysis.GowersMaureyBlockEigenObstruction

/-! A nonzero scalar minus a strictly singular operator is bounded below
on an actual finite-coordinate tail. Failure would provide successive unit
blocks with summable scalar-eigenvector errors and hence an infinite-
dimensional lower bound for the strictly singular operator itself. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem normalize_tail_scalar_error (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (a : 𝕜)
    (B : ℕ) (x : C00 𝕜) (hx : x ∈ afterCutoff B) {ε : ℝ} (hε : 0 < ε)
    (he : ‖T (denseEmbedding D x)-a • denseEmbedding D x‖ < ε*implicitNorm D x) :
    ∃ y : C00 𝕜, y ∈ afterCutoff B ∧ implicitNorm D y = 1 ∧
      ‖T (denseEmbedding D y)-a • denseEmbedding D y‖ < ε := by
  have hn : 0 < implicitNorm D x := by
    nlinarith [norm_nonneg (T (denseEmbedding D x)-a • denseEmbedding D x)]
  let r : ℝ := (implicitNorm D x)⁻¹
  have hr : 0 < r := inv_pos.mpr hn
  refine ⟨(r : 𝕜) • x, ?_, ?_, ?_⟩
  · intro k hk
    simp [hx k hk]
  · rw [map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos hr]
    exact inv_mul_cancel₀ hn.ne'
  · simp only [map_smul]
    rw [smul_comm a, ← smul_sub, norm_smul, RCLike.norm_ofReal, abs_of_pos hr]
    have hh := mul_lt_mul_of_pos_left he hr
    have heq : r*(ε*implicitNorm D x) = ε := by
      dsimp only [r]
      rw [mul_left_comm, inv_mul_cancel₀ hn.ne', mul_one]
    exact hh.trans_eq heq

theorem strictlySingular_finite_tail_lower_bound (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (hT : IsStrictlySingularOperator T)
    (a : 𝕜) (ha : a ≠ 0) :
    ∃ B : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ x : C00 𝕜, x ∈ afterCutoff B →
      c*implicitNorm D x ≤ ‖T (denseEmbedding D x)-a • denseEmbedding D x‖ := by
  classical
  by_contra h
  push_neg at h
  let η : ℕ → ℝ := fun i => (‖a‖/8)*((1 : ℝ)/2)^i
  have hη : ∀ i, 0 < η i := fun i =>
    mul_pos (div_pos (norm_pos_iff.mpr ha) (by norm_num)) (pow_pos (by norm_num) i)
  have hanti : Antitone η := by
    apply antitone_nat_of_succ_le
    intro i
    dsimp only [η]
    rw [pow_succ]
    have hh : 0 ≤ (‖a‖/8)*((1 : ℝ)/2)^i := (hη i).le
    nlinarith
  let P (b : ℕ × C00 𝕜) := implicitNorm D b.2 = 1 ∧
    ‖T (denseEmbedding D b.2)-a • denseEmbedding D b.2‖ < η b.1
  let R (b c : ℕ × C00 𝕜) := b.1 < c.1 ∧ Before b.2 c.2
  have hselect : ∀ s : Finset (ℕ × C00 𝕜), (∀ b ∈ s, P b) →
      ∃ c, P c ∧ ∀ b ∈ s, R b c := by
    intro s _
    let n := s.sup Prod.fst+1
    let B := s.sup (fun b => b.2.support.sup id)
    obtain ⟨x,hxB,hxerr⟩ := h B (η n) (hη n)
    obtain ⟨y,hyB,hyn,hyerr⟩ := normalize_tail_scalar_error D T a B x hxB (hη n) hxerr
    refine ⟨(n,y),⟨hyn,hyerr⟩,?_⟩
    intro b hb
    refine ⟨(Finset.le_sup (f := Prod.fst) hb).trans_lt (Nat.lt_succ_self _),?_⟩
    apply before_of_mem_afterCutoff (K := B) _ hyB
    intro k hk
    exact (Finset.le_sup (f := id) hk).trans
      (Finset.le_sup (f := fun b : ℕ × C00 𝕜 => b.2.support.sup id) hb)
  obtain ⟨w,hw,hwr⟩ := exists_seq_of_forall_finset_exists P R hselect
  have hindex : ∀ i : ℕ, i ≤ (w i).1 := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have hh := (hwr i (i+1) (Nat.lt_succ_self i)).1; omega
  have hs : HasSum η (‖a‖/4) := by
    convert hasSum_geometric_two.mul_left (‖a‖/8) using 1
    ring
  exact not_strictlySingular_of_block_eigen_errors D T a ha (fun i => (w i).2)
    (fun i j hij => (hwr i j hij).2) (fun i => (hw i).1) η (fun i => (hη i).le)
    (fun i => ((hw i).2.trans_le (hanti (hindex i))).le)
    (fun s => (hs.summable.sum_le_tsum s (fun i _ => (hη i).le)).trans_eq hs.tsum_eq) hT

theorem strictlySingular_completed_tail_lower_bound (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (hT : IsStrictlySingularOperator T)
    (a : 𝕜) (ha : a ≠ 0) :
    ∃ B : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ x : ShiftSpace D,
      (∀ k ≤ B, completedCoordinate D k x = 0) → c*‖x‖ ≤ ‖T x-a • x‖ := by
  obtain ⟨B,c,hc,hbound⟩ := strictlySingular_finite_tail_lower_bound D T hT a ha
  refine ⟨B,c,hc,?_⟩
  intro x hx
  have hclosed : IsClosed {y : ShiftSpace D | c*‖y‖ ≤ ‖T y-a • y‖} :=
    isClosed_le (continuous_const.mul continuous_norm)
      (T.continuous.sub (continuous_const.smul continuous_id)).norm
  apply hclosed.mem_of_tendsto (initialSum_tendsto D x)
  apply Filter.Eventually.of_forall
  intro N
  have hn : initialCoefficients D N x ∈ afterCutoff B := by
    intro k hk
    rw [initialCoefficients_apply]
    split_ifs <;> simp [hx k hk]
  have hh := hbound (initialCoefficients D N x) hn
  have hnorm : ‖denseEmbedding D (initialCoefficients D N x)‖ =
      implicitNorm D (initialCoefficients D N x) := denseEmbedding_norm D _
  rw [← hnorm, denseEmbedding_initialCoefficients] at hh
  exact hh

end ThesisCommon.GowersMaurey
