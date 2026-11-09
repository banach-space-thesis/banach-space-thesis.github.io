import SurveyStatements.P1L1Tail

/-! Toroidal separation for any sequence equivalent to the ℓ₁ unit basis.
The stabilization proof uses actual successive finite blocks. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem l1_exists_stabilized_successive_blocks (e : ℕ → X) {L U : ℝ} (hL : 0 < L)
    (hlower : ∀ b : ℕ →₀ ℂ, L * coefficientL1Mass b ≤ ‖Finsupp.linearCombination ℂ e b‖)
    (hupper : ∀ b : ℕ →₀ ℂ, ‖Finsupp.linearCombination ℂ e b‖ ≤ U * coefficientL1Mass b) :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∃ m : ℕ → ℕ, ∃ b : ℕ → ℕ →₀ ℂ,
      StrictMono m ∧ (∀ n, N ≤ m n) ∧
      (9 / 10 : ℝ) * A < l1TailLowerNorm e N ∧
      (∀ n i, i ∈ (b n).support → m n ≤ i ∧ i < m (n + 1)) ∧
      (∀ n, coefficientL1Mass (b n) = 1) ∧
      (∀ n, ‖Finsupp.linearCombination ℂ e (b n)‖ < (11 / 10 : ℝ) * A) := by
  classical
  obtain ⟨A, hA, N, hN, hblocks⟩ := l1TailLowerNorm_stabilizes e hL hlower hupper
  choose block hsupport hmass hnorm using hblocks
  let next : ℕ → ℕ := fun M => max (M + 1) ((block M).support.sup id + 1)
  let m : ℕ → ℕ := Nat.rec N (fun _ M => next M)
  have hmnext (n : ℕ) : m (n + 1) = next (m n) := rfl
  have hm : StrictMono m := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hmnext]
    exact (Nat.lt_succ_self _).trans_le (Nat.le_max_left _ _)
  have hmN (n : ℕ) : N ≤ m n := by
    exact hm.monotone (Nat.zero_le n)
  refine ⟨A, hA, N, m, fun n => block (m n), hm, hmN, hN, ?_,
    fun n => hmass (m n), fun n => hnorm (m n)⟩
  intro n i hi
  refine ⟨hsupport (m n) i hi, ?_⟩
  have hisup : i ≤ (block (m n)).support.sup id := Finset.le_sup (f := id) hi
  have hnext : (block (m n)).support.sup id + 1 ≤ m (n + 1) := by
    rw [hmnext]
    exact Nat.le_max_right _ _
  omega

/-- The original ℓ₁ isomorphism constants may be arbitrarily poor: finite
tail blocks produce unit vectors with a fixed phase-uniform margin. -/
theorem l1_equivalent_sequence_toroidal_elton_odell (e : ℕ → X) {L U : ℝ} (hL : 0 < L)
    (hlower : ∀ b : ℕ →₀ ℂ, L * coefficientL1Mass b ≤ ‖Finsupp.linearCombination ℂ e b‖)
    (hupper : ∀ b : ℕ →₀ ℂ, ‖Finsupp.linearCombination ℂ e b‖ ≤ U * coefficientL1Mass b) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  classical
  obtain ⟨A, hA, N, m, b, hm, hmN, hN, hsupp, hmass, hnorm⟩ :=
    l1_exists_stabilized_successive_blocks e hL hlower hupper
  have hsuppN (n : ℕ) : ∀ i ∈ (b n).support, N ≤ i :=
    fun i hi => (hmN n).trans (hsupp n i hi).1
  have hnormlower (n : ℕ) : (9 / 10 : ℝ) * A < ‖Finsupp.linearCombination ℂ e (b n)‖ :=
    hN.trans_le (l1TailLowerNorm_le e N (b n) (hsuppN n) (hmass n))
  have hdisjoint (n k : ℕ) (hnk : n ≠ k) : Disjoint (b n).support (b k).support := by
    apply Finset.disjoint_left.mpr
    intro i hin hik
    have hni := hsupp n i hin
    have hki := hsupp k i hik
    rcases lt_or_gt_of_ne hnk with hlt | hgt
    · have hmk : m (n + 1) ≤ m k := hm.monotone (by omega)
      omega
    · have hmn : m (k + 1) ≤ m n := hm.monotone (by omega)
      omega
  let v : ℕ → X := fun n => (A : ℂ)⁻¹ • Finsupp.linearCombination ℂ e (b n)
  have hvnorm (n : ℕ) : ‖v n‖ = A⁻¹ * ‖Finsupp.linearCombination ℂ e (b n)‖ := by
    simp [v, norm_smul, abs_of_pos hA]
  have hvbounds (n : ℕ) : 9 / 10 < ‖v n‖ ∧ ‖v n‖ < 11 / 10 := by
    rw [hvnorm, ← div_eq_inv_mul]
    constructor
    · exact (lt_div_iff₀ hA).mpr (by nlinarith [hnormlower n])
    · exact (div_lt_iff₀ hA).mpr (by nlinarith [hnorm n])
  have hvnz (n : ℕ) : v n ≠ 0 := norm_pos_iff.mp (by linarith [(hvbounds n).1])
  have herror (n : ℕ) : ‖v n - unitNormalize (v n)‖ ≤ 1 / 10 := by
    rw [norm_sub_rev, norm_unitNormalize_sub_self (hvnz n), abs_le]
    constructor <;> linarith [(hvbounds n).1, (hvbounds n).2]
  refine ⟨1 / 2, by norm_num, fun n => unitNormalize (v n),
    fun n => norm_unitNormalize (hvnz n), ?_⟩
  intro n k hnk θ hθ
  have hθnorm : ‖θ‖ = 1 := hθ
  let c : ℕ →₀ ℂ := b n - θ • b k
  have hcsupp : ∀ i ∈ c.support, N ≤ i := by
    intro i hi
    have hi' := Finsupp.support_sub hi
    rcases Finset.mem_union.mp hi' with hin | hik
    · exact hsuppN n i hin
    · exact hsuppN k i (Finsupp.support_smul hik)
  have hcmass : coefficientL1Mass c = 2 := by
    have hcEq : c = b n + (-θ) • b k := by simp [c, sub_eq_add_neg]
    rw [hcEq]
    rw [coefficientL1Mass_add_disjoint]
    · rw [coefficientL1Mass_smul, norm_neg, hθnorm, hmass n, hmass k]
      norm_num
    · exact (hdisjoint n k hnk).mono_right Finsupp.support_smul
  have hscaledmass : coefficientL1Mass ((1 / 2 : ℂ) • c) = 1 := by
    rw [coefficientL1Mass_smul, hcmass]
    norm_num
  have hscalednorm := l1TailLowerNorm_le e N ((1 / 2 : ℂ) • c)
    (fun i hi => hcsupp i (Finsupp.support_smul hi)) hscaledmass
  have hclower : (18 / 10 : ℝ) * A < ‖Finsupp.linearCombination ℂ e c‖ := by
    simp only [map_smul, norm_smul] at hscalednorm
    norm_num at hscalednorm
    linarith
  have hveq : v n - θ • v k = (A : ℂ)⁻¹ • Finsupp.linearCombination ℂ e c := by
    simp only [v, c, map_sub, map_smul, smul_sub]
    rw [smul_comm θ (A : ℂ)⁻¹]
  have hvdiff : (18 / 10 : ℝ) < ‖v n - θ • v k‖ := by
    rw [hveq, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA,
      ← div_eq_inv_mul]
    exact (lt_div_iff₀ hA).mpr (by nlinarith [hclower])
  have hperturb := phase_norm_perturbation (v n) (v k)
    (unitNormalize (v n)) (unitNormalize (v k)) hθ
  linarith [herror n, herror k]

end SurveyStatements.P1
