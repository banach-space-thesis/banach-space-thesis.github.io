import SurveyStatements.P1C0BlockNorm

/-! The actual complex c₀-copy case, proved by stabilized finite blocks. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

theorem c0FinsuppLinear_injective : Function.Injective c0FinsuppLinear := by
  intro a b h
  ext i
  exact congrArg (fun x : ComplexC0 => x i) h

def c0UnitFinsupp (n : ℕ) : ℕ →₀ ℂ :=
  Finsupp.onFinset (Finset.range (n + 2)) (c0UnitSequence n) (by
    intro i hi
    apply Finset.mem_range.mpr
    by_contra h
    have hge : n + 2 ≤ i := Nat.le_of_not_lt h
    have hzero : c0UnitSequence n i = 0 := by
      simp [show ¬ i ≤ n by omega, show i ≠ n + 1 by omega]
    exact hi hzero)

theorem c0Finsupp_c0UnitFinsupp (n : ℕ) : c0Finsupp (c0UnitFinsupp n) = c0UnitSequence n := by
  ext i
  rfl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem c0_exists_stabilized_successive_blocks (T : ComplexC0 →L[ℂ] X)
    {L : ℝ} (hL : 0 < L) (hlower : ∀ v : ComplexC0, L * ‖v‖ ≤ ‖T v‖) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∃ b : ℕ → ℕ →₀ ℂ,
      c0TailUpperNorm T N < (101 / 100 : ℝ) * B ∧
      (∀ n i, i ∈ (b n).support → N ≤ i) ∧
      (∀ n k, n ≠ k → Disjoint (b n).support (b k).support) ∧
      (∀ n i, ‖b n i‖ ≤ 1) ∧
      (∀ n, (99 / 100 : ℝ) * B < ‖T (c0Finsupp (b n))‖) := by
  classical
  obtain ⟨B, hB, N, hN, hblocks⟩ := c0TailUpperNorm_stabilizes T hL hlower
  choose block hsupp hunit hnorm using hblocks
  let next : ℕ → ℕ := fun M => max (M + 1) ((block M).support.sup id + 1)
  let m : ℕ → ℕ := Nat.rec N (fun _ M => next M)
  have hmnext (n : ℕ) : m (n + 1) = next (m n) := rfl
  have hm : StrictMono m := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hmnext]
    exact (Nat.lt_succ_self _).trans_le (Nat.le_max_left _ _)
  have hmN (n : ℕ) : N ≤ m n := hm.monotone (Nat.zero_le n)
  have hinter (n i : ℕ) (hi : i ∈ (block (m n)).support) :
      m n ≤ i ∧ i < m (n + 1) := by
    refine ⟨hsupp (m n) i hi, ?_⟩
    have hisup : i ≤ (block (m n)).support.sup id := Finset.le_sup (f := id) hi
    have hnext : (block (m n)).support.sup id + 1 ≤ m (n + 1) := by
      rw [hmnext]
      exact Nat.le_max_right _ _
    omega
  refine ⟨B, hB, N, fun n => block (m n), hN,
    fun n i hi => (hmN n).trans (hsupp (m n) i hi), ?_,
    fun n => hunit (m n), fun n => hnorm (m n)⟩
  intro n k hnk
  apply Finset.disjoint_left.mpr
  intro i hin hik
  have hni := hinter n i hin
  have hki := hinter k i hik
  rcases lt_or_gt_of_ne hnk with hlt | hgt
  · have hmk : m (n + 1) ≤ m k := hm.monotone (show n + 1 ≤ k by omega)
    omega
  · have hmn : m (k + 1) ≤ m n := hm.monotone (show k + 1 ≤ n by omega)
    omega

theorem c0_embedding_toroidal_elton_odell (T : ComplexC0 →L[ℂ] X) {L : ℝ}
    (hL : 0 < L) (hlower : ∀ v : ComplexC0, L * ‖v‖ ≤ ‖T v‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  classical
  obtain ⟨B, hB, N, b, hN, hsupp, hdisjoint, hb, hnorm⟩ :=
    c0_exists_stabilized_successive_blocks T hL hlower
  let Q := LinearEquiv.ofInjective c0FinsuppLinear c0FinsuppLinear_injective
  let H : (ℕ →₀ ℂ) →ₗ[ℂ] X :=
    (T.toLinearMap.comp c0FinsuppLinear).comp (Finsupp.linearCombination ℂ b)
  let J : (LinearMap.range c0FinsuppLinear) →ₗ[ℂ] X :=
    (B : ℂ)⁻¹ • (H.comp Q.symm.toLinearMap)
  have hnormH (a : ℕ →₀ ℂ) :
      (97 / 100 : ℝ) * B * ‖c0Finsupp a‖ ≤ ‖H a‖ ∧
        ‖H a‖ ≤ (101 / 100 : ℝ) * B * ‖c0Finsupp a‖ := by
    have hlow := c0_disjointBlocks_finite_lower T N b hsupp hdisjoint hb
      (show 0 < (99 / 100 : ℝ) * B by positivity) (fun n => (hnorm n).le) a
    have hup := c0_disjointBlocks_finite_upper T N b hsupp hdisjoint hb a
    have hmul := mul_le_mul_of_nonneg_right hN.le (norm_nonneg (c0Finsupp a))
    change (97 / 100 : ℝ) * B * ‖c0Finsupp a‖ ≤
        ‖T (c0Finsupp (Finsupp.linearCombination ℂ b a))‖ ∧
      ‖T (c0Finsupp (Finsupp.linearCombination ℂ b a))‖ ≤
        (101 / 100 : ℝ) * B * ‖c0Finsupp a‖
    constructor <;> nlinarith
  have hQ (v : (LinearMap.range c0FinsuppLinear)) : c0Finsupp (Q.symm v) = (v : ComplexC0) :=
    congrArg Subtype.val (Q.apply_symm_apply v)
  have hJnorm (v : (LinearMap.range c0FinsuppLinear)) : ‖J v‖ = ‖H (Q.symm v)‖ / B := by
    simp [J, LinearMap.smul_apply, norm_smul, abs_of_pos hB, div_eq_inv_mul]
  have hJlower (v : (LinearMap.range c0FinsuppLinear)) : (1 - (1 / 20 : ℝ)) * ‖v‖ ≤ ‖J v‖ := by
    rw [hJnorm, le_div_iff₀ hB]
    have hlow := (hnormH (Q.symm v)).1
    rw [hQ] at hlow
    change (1 - (1 / 20 : ℝ)) * ‖(v : ComplexC0)‖ * B ≤ _
    nlinarith [norm_nonneg (v : ComplexC0)]
  have hJupper (v : (LinearMap.range c0FinsuppLinear)) : ‖J v‖ ≤ (1 + (1 / 20 : ℝ)) * ‖v‖ := by
    rw [hJnorm, div_le_iff₀ hB]
    have hup := (hnormH (Q.symm v)).2
    rw [hQ] at hup
    change _ ≤ (1 + (1 / 20 : ℝ)) * ‖(v : ComplexC0)‖ * B
    nlinarith [norm_nonneg (v : ComplexC0)]
  let u : ℕ → (LinearMap.range c0FinsuppLinear) := fun n => Q (c0UnitFinsupp n)
  have hu (n : ℕ) : (u n : ComplexC0) = c0UnitSequence n := c0Finsupp_c0UnitFinsupp n
  have hunorm (n : ℕ) : ‖u n‖ = 1 := by
    change ‖(u n : ComplexC0)‖ = 1
    rw [hu, norm_c0UnitSequence]
  have hphase (n k : ℕ) (hnk : n ≠ k) (θ : ℂ) (hθ : θ ∈ unitScalars) :
      Real.sqrt 2 ≤ ‖u n - θ • u k‖ := by
    change Real.sqrt 2 ≤ ‖(u n : ComplexC0) - θ • (u k : ComplexC0)‖
    rw [hu, hu]
    exact c0UnitSequence_phase_lower hnk hθ
  have hsqrt : (7 / 5 : ℝ) < Real.sqrt 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hδthreshold : (1 / 20 : ℝ) < (Real.sqrt 2 - 1) / (Real.sqrt 2 + 3) := by
    apply (lt_div_iff₀ (by positivity : 0 < Real.sqrt 2 + 3)).mpr
    nlinarith
  have hdist : ∀ n k, n ≠ k → Real.sqrt 2 ≤ toroidalDistance (u n) (u k) :=
    fun n k hnk => (le_toroidalDistance_iff _ _ _).mpr (hphase n k hnk)
  exact almostIsometric_transfer J (δ := 1 / 20) (σ := Real.sqrt 2)
    (by norm_num) (by norm_num) (by linarith) hδthreshold hJlower hJupper hunorm hdist

theorem c0_isomorphicCopy_toroidal_elton_odell (S : Submodule ℂ X)
    (T : ComplexC0 ≃L[ℂ] S) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  let J : ComplexC0 →L[ℂ] X := S.subtypeL.comp T.toContinuousLinearMap
  have hpos : 0 < ‖T.symm.toContinuousLinearMap‖ + 1 := by positivity
  apply c0_embedding_toroidal_elton_odell J (L := (‖T.symm.toContinuousLinearMap‖ + 1)⁻¹)
    (inv_pos.mpr hpos)
  intro v
  change (‖T.symm.toContinuousLinearMap‖ + 1)⁻¹ * ‖v‖ ≤ ‖T v‖
  rw [← div_eq_inv_mul, div_le_iff₀ hpos]
  have hbound := T.symm.toContinuousLinearMap.le_opNorm (T v)
  simp only [ContinuousLinearEquiv.coe_coe, T.symm_apply_apply] at hbound
  nlinarith [norm_nonneg (T v)]

end SurveyStatements.P1
