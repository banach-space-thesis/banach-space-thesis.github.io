import PL1.IntrinsicWalsh
import PL1.WalshBlocks

/-! # Exact dimensions of the intrinsic finite-coordinate projections and blocks -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PL1.Noise

open Walsh WalshExpectations IntrinsicGraph

variable (𝕜 : Type*) [RCLike 𝕜] (rates : ℕ → ℝ≥0)

/-- Each Walsh character is an actual vector of the intrinsic space. The
zeroth resolvent column supplies it after multiplication by its inverse eigenvalue. -/
def intrinsicCharacter (F : Finset ℕ) : (dyadicSystem 𝕜 rates).IntrinsicSpace :=
  (((1 + rateSum rates F : ℝ) : 𝕜)) •
    (dyadicSystem 𝕜 rates).column 0 (scalarCharacterLp 𝕜 1 F)

@[simp] theorem evalZero_intrinsicCharacter (F : Finset ℕ) :
    evalZero (dyadicSystem 𝕜 rates).analysis (intrinsicCharacter 𝕜 rates F) =
      scalarCharacterLp 𝕜 1 F := by
  rw [intrinsicCharacter, map_smul, DyadicSystem.evalZero_column]
  change ((1 + rateSum rates F : ℝ) : 𝕜) •
    resolventL1 𝕜 rates (dyadicTime 0) (scalarCharacterLp 𝕜 1 F) = _
  rw [resolventL1_scalarCharacter]
  simp only [dyadicTime, pow_zero, one_mul, smul_smul]
  rw [← RCLike.ofReal_mul, mul_inv_cancel₀
    (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (rateSum_nonneg rates F))),
    RCLike.ofReal_one, one_smul]

theorem linearIndependent_intrinsicCharacter : LinearIndependent 𝕜 (intrinsicCharacter 𝕜 rates) := by
  apply LinearIndependent.of_comp (evalZero (dyadicSystem 𝕜 rates).analysis).toLinearMap
  simpa only [Function.comp_def, ContinuousLinearMap.coe_coe, evalZero_intrinsicCharacter] using
    WalshBlocks.linearIndependent_characterL1 𝕜

theorem intrinsicExpectation_character (m : ℕ) (F : Finset ℕ) :
    intrinsicExpectation 𝕜 rates m (intrinsicCharacter 𝕜 rates F) =
      if F ⊆ Finset.range m then intrinsicCharacter 𝕜 rates F else 0 := by
  apply evalZero_injective (dyadicSystem 𝕜 rates).analysis
  rw [evalZero_intrinsicExpectation, evalZero_intrinsicCharacter, expectationL1_character]
  split_ifs <;> simp only [evalZero_intrinsicCharacter, map_zero]

theorem finrank_intrinsicExpectation (m : ℕ) :
    Module.finrank 𝕜 (intrinsicExpectation 𝕜 rates m).range = 2 ^ m := by
  have hu : Module.finrank 𝕜 (intrinsicExpectation 𝕜 rates m).range ≤ 2 ^ m := by
    have h := finrank_commutingLift_range_le (dyadicSystem 𝕜 rates).analysis rfl
      (expectationL1 𝕜 m) (expectation_analysis_commute 𝕜 rates m)
    exact h.trans_eq (WalshBlocks.finrank_range_expectationL1 𝕜 m)
  let v : (Finset.range m).powerset → (intrinsicExpectation 𝕜 rates m).range := fun F =>
    ⟨intrinsicCharacter 𝕜 rates F, ⟨intrinsicCharacter 𝕜 rates F, by
      change intrinsicExpectation 𝕜 rates m (intrinsicCharacter 𝕜 rates F) = _
      simp only [intrinsicExpectation_character, Finset.mem_powerset.mp F.property, ite_true]⟩⟩
  have hi : LinearIndependent 𝕜 v := by
    apply LinearIndependent.of_comp (intrinsicExpectation 𝕜 rates m).range.subtype
    exact (linearIndependent_intrinsicCharacter 𝕜 rates).comp
      (fun F : (Finset.range m).powerset => (F : Finset ℕ)) Subtype.val_injective
  have hl : 2 ^ m ≤ Module.finrank 𝕜 (intrinsicExpectation 𝕜 rates m).range := by
    simpa using hi.fintype_card_le_finrank
  exact le_antisymm hu hl

theorem block_analysis_commute (m n : ℕ) (f : Lp 𝕜 1 haar) :
    WalshBlocks.blockL1 𝕜 m ((dyadicSystem 𝕜 rates).analysis n f) =
      (dyadicSystem 𝕜 rates).analysis n (WalshBlocks.blockL1 𝕜 m f) := by
  simp only [WalshBlocks.blockL1, sub_apply, map_sub, expectation_analysis_commute]

/-- The next-coordinate difference projection in the actual intrinsic norm. -/
theorem intrinsicAnalysis_zero :
    (dyadicSystem 𝕜 rates).analysis 0 = ContinuousLinearMap.id 𝕜 (Lp 𝕜 1 haar) := rfl

def intrinsicBlock (m : ℕ) :
    (dyadicSystem 𝕜 rates).IntrinsicSpace →L[𝕜] (dyadicSystem 𝕜 rates).IntrinsicSpace :=
  commutingLift (dyadicSystem 𝕜 rates).analysis (intrinsicAnalysis_zero 𝕜 rates) (WalshBlocks.blockL1 𝕜 m)
    (block_analysis_commute 𝕜 rates m)

@[simp] theorem evalZero_intrinsicBlock (m : ℕ) (x : (dyadicSystem 𝕜 rates).IntrinsicSpace) :
    evalZero (dyadicSystem 𝕜 rates).analysis (intrinsicBlock 𝕜 rates m x) =
      WalshBlocks.blockL1 𝕜 m (evalZero (dyadicSystem 𝕜 rates).analysis x) :=
  evalZero_commutingLift _ _ _ _ _

theorem intrinsicBlock_eq_sub (m : ℕ) :
    intrinsicBlock 𝕜 rates m = intrinsicExpectation 𝕜 rates (m + 1) - intrinsicExpectation 𝕜 rates m := by
  ext1 x
  apply evalZero_injective (dyadicSystem 𝕜 rates).analysis
  simp only [evalZero_intrinsicBlock, sub_apply, map_sub,
    evalZero_intrinsicExpectation, WalshBlocks.blockL1]

instance intrinsicBlock_range_finiteDimensional (m : ℕ) :
    FiniteDimensional 𝕜 (intrinsicBlock 𝕜 rates m).range := by
  let : FiniteDimensional 𝕜 (WalshBlocks.blockL1 𝕜 m).range := by
    rw [WalshBlocks.range_blockL1_eq]
    infer_instance
  exact commutingLift_range_finiteDimensional _ _ _ _

theorem intrinsicBlock_character (m : ℕ) (F : Finset ℕ) :
    intrinsicBlock 𝕜 rates m (intrinsicCharacter 𝕜 rates F) =
      if m ∈ F ∧ F ⊆ Finset.range (m + 1) then intrinsicCharacter 𝕜 rates F else 0 := by
  apply evalZero_injective (dyadicSystem 𝕜 rates).analysis
  rw [evalZero_intrinsicBlock, evalZero_intrinsicCharacter, WalshBlocks.blockL1_character]
  split_ifs <;> simp only [evalZero_intrinsicCharacter, map_zero]

theorem finrank_intrinsicBlock (m : ℕ) :
    Module.finrank 𝕜 (intrinsicBlock 𝕜 rates m).range = 2 ^ m := by
  let : FiniteDimensional 𝕜 (WalshBlocks.blockL1 𝕜 m).range := by
    rw [WalshBlocks.range_blockL1_eq]
    infer_instance
  have hu : Module.finrank 𝕜 (intrinsicBlock 𝕜 rates m).range ≤ 2 ^ m := by
    have h := finrank_commutingLift_range_le (dyadicSystem 𝕜 rates).analysis rfl
      (WalshBlocks.blockL1 𝕜 m) (block_analysis_commute 𝕜 rates m)
    exact h.trans_eq (WalshBlocks.finrank_range_blockL1 𝕜 m)
  let v : (Finset.range m).powerset → (intrinsicBlock 𝕜 rates m).range := fun F =>
    ⟨intrinsicCharacter 𝕜 rates (insert m F), ⟨intrinsicCharacter 𝕜 rates (insert m F), by
      change intrinsicBlock 𝕜 rates m (intrinsicCharacter 𝕜 rates (insert m F)) = _
      rw [intrinsicBlock_character]
      apply ite_eq_left
      exact ⟨Finset.mem_insert_self _ _, Finset.insert_subset_iff.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_self m),
          (Finset.mem_powerset.mp F.property).trans (Finset.range_mono (Nat.le_succ m))⟩⟩⟩⟩
  have hi : LinearIndependent 𝕜 v := by
    apply LinearIndependent.of_comp (intrinsicBlock 𝕜 rates m).range.subtype
    exact (linearIndependent_intrinsicCharacter 𝕜 rates).comp _
      (WalshBlocks.blockSupport_injective m)
  have hl : 2 ^ m ≤ Module.finrank 𝕜 (intrinsicBlock 𝕜 rates m).range := by
    simpa using hi.fintype_card_le_finrank
  exact le_antisymm hu hl

theorem intrinsicExpectation_commute (m n : ℕ) :
    (intrinsicExpectation 𝕜 rates m).comp (intrinsicExpectation 𝕜 rates n) =
      (intrinsicExpectation 𝕜 rates n).comp (intrinsicExpectation 𝕜 rates m) := by
  ext1 x
  apply evalZero_injective (dyadicSystem 𝕜 rates).analysis
  simp only [ContinuousLinearMap.comp_apply, evalZero_intrinsicExpectation]
  exact DFunLike.congr_fun (expectationL1_commute 𝕜 m (tailMeasure n))
    (evalZero (dyadicSystem 𝕜 rates).analysis x)

theorem intrinsicExpectation_comp_min (m n : ℕ) :
    (intrinsicExpectation 𝕜 rates m).comp (intrinsicExpectation 𝕜 rates n) =
      intrinsicExpectation 𝕜 rates (min m n) := by
  rcases le_total m n with h | h
  · rw [min_eq_left h, intrinsicExpectation_comp_of_le 𝕜 rates m n h]
  · rw [intrinsicExpectation_commute, min_eq_right h,
      intrinsicExpectation_comp_of_le 𝕜 rates n m h]

/-- Distinct Walsh blocks annihilate one another, and each block is a projection. -/
theorem intrinsicBlock_comp (m n : ℕ) :
    (intrinsicBlock 𝕜 rates m).comp (intrinsicBlock 𝕜 rates n) =
      if m = n then intrinsicBlock 𝕜 rates m else 0 := by
  simp only [intrinsicBlock_eq_sub, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    intrinsicExpectation_comp_min]
  rcases lt_trichotomy m n with h | h | h
  · have h1 : min (m + 1) (n + 1) = m + 1 := min_eq_left (by omega)
    have h2 : min (m + 1) n = m + 1 := min_eq_left (by omega)
    have h3 : min m (n + 1) = m := min_eq_left (by omega)
    have h4 : min m n = m := min_eq_left (by omega)
    simp only [h.ne, ite_false, h1, h2, h3, h4]
    ext1 x
    simp only [sub_apply, zero_apply]
    abel
  · subst n
    simp only [min_self, min_eq_left (Nat.le_succ m), min_eq_right (Nat.le_succ m), ite_true]
    ext1 x
    simp only [sub_apply]
    abel
  · have h1 : min (m + 1) (n + 1) = n + 1 := min_eq_right (by omega)
    have h2 : min (m + 1) n = n := min_eq_right (by omega)
    have h3 : min m (n + 1) = n + 1 := min_eq_right (by omega)
    have h4 : min m n = n := min_eq_right (by omega)
    simp only [h.ne', ite_false, h1, h2, h3, h4]
    ext1 x
    simp only [sub_apply, zero_apply]
    abel

theorem intrinsicBlock_isProjection (m : ℕ) : IsProjection (intrinsicBlock 𝕜 rates m) := by
  change (intrinsicBlock 𝕜 rates m).comp (intrinsicBlock 𝕜 rates m) = _
  simpa only [ite_true] using intrinsicBlock_comp 𝕜 rates m m

theorem intrinsicExpectation_zero_comp_block (m : ℕ) :
    (intrinsicExpectation 𝕜 rates 0).comp (intrinsicBlock 𝕜 rates m) = 0 := by
  rw [intrinsicBlock_eq_sub, ContinuousLinearMap.comp_sub]
  simp only [intrinsicExpectation_comp_min, zero_min]
  ext1 x
  simp only [sub_apply, zero_apply]
  abel

theorem intrinsicBlock_comp_expectation_zero (m : ℕ) :
    (intrinsicBlock 𝕜 rates m).comp (intrinsicExpectation 𝕜 rates 0) = 0 := by
  rw [intrinsicBlock_eq_sub, ContinuousLinearMap.sub_comp]
  simp only [intrinsicExpectation_comp_min, min_zero]
  ext1 x
  simp only [sub_apply, zero_apply]
  abel

theorem norm_intrinsicBlock_le_two (m : ℕ) : ‖intrinsicBlock 𝕜 rates m‖ ≤ 2 := by
  rw [intrinsicBlock_eq_sub]
  calc
    _ ≤ ‖intrinsicExpectation 𝕜 rates (m + 1)‖ + ‖intrinsicExpectation 𝕜 rates m‖ :=
      norm_sub_le (intrinsicExpectation 𝕜 rates (m + 1)) (intrinsicExpectation 𝕜 rates m)
    _ ≤ 1 + 1 := add_le_add (norm_intrinsicExpectation_le 𝕜 rates (m + 1))
      (norm_intrinsicExpectation_le 𝕜 rates m)
    _ = 2 := by norm_num

/-- The partial sums of the block expansion are exactly the contractive expectations. -/
theorem intrinsicBlock_partialSum (N : ℕ) :
    intrinsicExpectation 𝕜 rates 0 + ∑ m ∈ Finset.range N, intrinsicBlock 𝕜 rates m =
      intrinsicExpectation 𝕜 rates N := by
  ext1 x
  simp only [add_apply, sum_apply]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih, intrinsicBlock_eq_sub, sub_apply]
    abel

theorem intrinsicBlock_partialSum_apply (N : ℕ) (x : (dyadicSystem 𝕜 rates).IntrinsicSpace) :
    intrinsicExpectation 𝕜 rates 0 x + ∑ m ∈ Finset.range N, intrinsicBlock 𝕜 rates m x =
      intrinsicExpectation 𝕜 rates N x := by
  have h := DFunLike.congr_fun (intrinsicBlock_partialSum 𝕜 rates N) x
  simpa only [add_apply, sum_apply] using h

/-- Every intrinsic vector has its Walsh block expansion converging in the actual intrinsic norm. -/
theorem tendsto_intrinsicBlock_partialSum (x : (dyadicSystem 𝕜 rates).IntrinsicSpace) :
    Tendsto (fun N => intrinsicExpectation 𝕜 rates 0 x +
      ∑ m ∈ Finset.range N, intrinsicBlock 𝕜 rates m x) atTop (𝓝 x) := by
  simpa only [intrinsicBlock_partialSum_apply] using tendsto_intrinsicExpectation 𝕜 rates x

/-- Convergent expansions into the constant space and successive Walsh blocks are unique. -/
theorem intrinsicBlock_expansion_unique
    (x a₀ : (dyadicSystem 𝕜 rates).IntrinsicSpace)
    (a : ℕ → (dyadicSystem 𝕜 rates).IntrinsicSpace)
    (ha₀ : a₀ ∈ (intrinsicExpectation 𝕜 rates 0).range)
    (ha : ∀ m, a m ∈ (intrinsicBlock 𝕜 rates m).range)
    (hconv : Tendsto (fun N => a₀ + ∑ m ∈ Finset.range N, a m) atTop (𝓝 x)) :
    a₀ = intrinsicExpectation 𝕜 rates 0 x ∧ ∀ m, a m = intrinsicBlock 𝕜 rates m x := by
  have h₀₀ : intrinsicExpectation 𝕜 rates 0 a₀ = a₀ := by
    obtain ⟨y, rfl⟩ := ha₀
    exact DFunLike.congr_fun (intrinsicExpectation_isProjection 𝕜 rates 0) y
  have h₀a (m : ℕ) : intrinsicExpectation 𝕜 rates 0 (a m) = 0 := by
    obtain ⟨y, hy⟩ := ha m
    rw [← hy]
    exact DFunLike.congr_fun (intrinsicExpectation_zero_comp_block 𝕜 rates m) y
  have hm₀ (m : ℕ) : intrinsicBlock 𝕜 rates m a₀ = 0 := by
    obtain ⟨y, rfl⟩ := ha₀
    exact DFunLike.congr_fun (intrinsicBlock_comp_expectation_zero 𝕜 rates m) y
  have hma (m n : ℕ) : intrinsicBlock 𝕜 rates m (a n) = if m = n then a n else 0 := by
    obtain ⟨y, hy⟩ := ha n
    change intrinsicBlock 𝕜 rates n y = a n at hy
    have h := DFunLike.congr_fun (intrinsicBlock_comp 𝕜 rates m n) y
    change intrinsicBlock 𝕜 rates m (intrinsicBlock 𝕜 rates n y) = _ at h
    by_cases hmn : m = n
    · subst n
      simpa only [ite_true, hy] using h
    · simpa only [hmn, ite_false, zero_apply, hy] using h
  constructor
  · have h := ((intrinsicExpectation 𝕜 rates 0).continuous.tendsto x).comp hconv
    simp only [Function.comp_def, map_add, map_sum, h₀₀, h₀a, Finset.sum_const_zero, add_zero] at h
    exact tendsto_nhds_unique tendsto_const_nhds h
  · intro m
    have h := ((intrinsicBlock 𝕜 rates m).continuous.tendsto x).comp hconv
    have heq : (fun N => intrinsicBlock 𝕜 rates m (a₀ + ∑ n ∈ Finset.range N, a n))
        =ᶠ[atTop] (fun _ => a m) := by
      filter_upwards [eventually_ge_atTop (m + 1)] with N hN
      simp only [map_add, map_sum, hm₀, hma, zero_add]
      simp [show m < N by omega]
    exact tendsto_nhds_unique tendsto_const_nhds (h.congr' heq)

end PL1.Noise
