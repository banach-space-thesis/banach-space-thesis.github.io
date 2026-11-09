import SurveyStatements.P1FlatBlocks
import SurveyStatements.P1FiniteNets

/-!
Finite successive covers of genuine almost-flat unit blocks on tails.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Failure of toroidal separation gives a finite cover by actual sparse
flat coefficients on any chosen tail. -/
theorem finite_sparse_flat_cover (e : ℕ → X) (he : ∀ n, ‖e n‖ = 1)
    (m : ℕ) {η : ℝ} (hη : 0 < η)
    (hno : ∀ ε : ℝ, 0 < ε →
      ¬ ∃ x : ℕ → X, (∀ n, x n ∈ sequenceClosedSpan e ∧ ‖x n‖ = 1) ∧
        ∀ n k, n ≠ k → 1 + ε < toroidalDistance (x n) (x k)) :
    ∃ D : Finset (ℕ →₀ ℂ), D.Nonempty ∧
      (∀ b ∈ D, HasFlatCoefficients b) ∧
      (∀ b ∈ D, ∀ i ∈ b.support, m ≤ i) ∧
      (∀ b ∈ D, |‖Finsupp.linearCombination ℂ e b‖ - 1| ≤ η) ∧
      ∀ z : ℕ →₀ ℂ, HasFlatCoefficients z →
        Finsupp.linearCombination ℂ e z ≠ 0 →
        (∀ i ∈ z.support, m ≤ i) →
        |‖Finsupp.linearCombination ℂ e z‖ - 1| ≤ η →
        ∃ b ∈ D, ∃ θ ∈ unitScalars,
          ‖unitNormalize (Finsupp.linearCombination ℂ e b) -
            θ • unitNormalize (Finsupp.linearCombination ℂ e z)‖ ≤ 1 + η := by
  classical
  let S : Set X := {x | ∃ b : ℕ →₀ ℂ, HasFlatCoefficients b ∧
    Finsupp.linearCombination ℂ e b ≠ 0 ∧
    (∀ i ∈ b.support, m ≤ i) ∧
    |‖Finsupp.linearCombination ℂ e b‖ - 1| ≤ η ∧
    x = unitNormalize (Finsupp.linearCombination ℂ e b)}
  have hunit : ∀ x ∈ S, x ∈ sequenceClosedSpan e ∧ ‖x‖ = 1 := by
    rintro x ⟨b, hb, hb0, _, _, rfl⟩
    refine ⟨?_, norm_unitNormalize hb0⟩
    exact (sequenceClosedSpan e).smul_mem _
      (flatBlock_mem_closedSpan (flatCoefficients_isFlatBlock hb hb0))
  have hnosep : ¬ ∃ x : ℕ → X, (∀ n, x n ∈ S) ∧
      ∀ n k, n ≠ k → 1 + η < toroidalDistance (x n) (x k) := by
    rintro ⟨x, hx, hsep⟩
    exact hno η hη ⟨x, fun n => hunit (x n) (hx n), hsep⟩
  obtain ⟨F, hF⟩ := finite_toroidal_cover S (1 + η) hnosep
  have hrepresent : ∀ y : S, ∃ b : ℕ →₀ ℂ, HasFlatCoefficients b ∧
      Finsupp.linearCombination ℂ e b ≠ 0 ∧
      (∀ i ∈ b.support, m ≤ i) ∧
      |‖Finsupp.linearCombination ℂ e b‖ - 1| ≤ η ∧
      (y : X) = unitNormalize (Finsupp.linearCombination ℂ e b) := fun y => y.property
  choose c hc using hrepresent
  let D := F.image c
  have hcover : ∀ z : ℕ →₀ ℂ, HasFlatCoefficients z →
      Finsupp.linearCombination ℂ e z ≠ 0 →
      (∀ i ∈ z.support, m ≤ i) →
      |‖Finsupp.linearCombination ℂ e z‖ - 1| ≤ η →
      ∃ b ∈ D, ∃ θ ∈ unitScalars,
        ‖unitNormalize (Finsupp.linearCombination ℂ e b) -
          θ • unitNormalize (Finsupp.linearCombination ℂ e z)‖ ≤ 1 + η := by
    intro z hz hz0 hzsup hznorm
    let x : S := ⟨unitNormalize (Finsupp.linearCombination ℂ e z),
      z, hz, hz0, hzsup, hznorm, rfl⟩
    obtain ⟨y, hy, hd⟩ := hF x
    have hd' : toroidalDistance (y : X) (x : X) ≤ 1 + η := by
      rw [toroidalDistance_symm]
      exact hd
    obtain ⟨θ, hθ, hdist⟩ := (toroidalDistance_le_iff_exists_phase _ _ _).mp hd'
    refine ⟨c y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, θ, hθ, ?_⟩
    simpa only [← (hc y).2.2.2.2] using hdist
  refine ⟨D, ?_, ?_, ?_, ?_, hcover⟩
  · have hb0 : Finsupp.linearCombination ℂ e (Finsupp.single m 1) ≠ 0 := by
      simp only [Finsupp.linearCombination_single, one_smul]
      exact norm_ne_zero_iff.mp (by rw [he]; norm_num)
    have hbsup : ∀ i ∈ (Finsupp.single m (1 : ℂ)).support, m ≤ i := by
      intro i hi
      by_cases him : i = m
      · omega
      · simp [Finsupp.mem_support_iff, him] at hi
    obtain ⟨b, hb, _, _, _⟩ := hcover (Finsupp.single m 1)
      (flatCoefficients_single m) hb0 hbsup (by simp [he, hη.le])
    exact ⟨b, hb⟩
  · intro b hb
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
    exact (hc y).1
  · intro b hb
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
    exact (hc y).2.2.1
  · intro b hb
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
    exact (hc y).2.2.2.1

/-- The recursive construction of successive finite covers also arranges
the prescribed asymptotic projection constants on each tail. -/
theorem exists_rapidCoverData (e : ℕ → X) (he : IsAsymptoticallyMonotone e)
    (η γ : ℕ → ℝ) (hη : ∀ j, 0 < η j) (hγ : ∀ j, 0 < γ j)
    (hno : ∀ ε : ℝ, 0 < ε →
      ¬ ∃ x : ℕ → X, (∀ n, x n ∈ sequenceClosedSpan e ∧ ‖x n‖ = 1) ∧
        ∀ n k, n ≠ k → 1 + ε < toroidalDistance (x n) (x k)) :
    Nonempty (RapidCoverData e η γ) := by
  classical
  have hthreshold : ∀ j, ∃ N : ℕ,
      ∀ p q r : ℕ, N ≤ p → p ≤ q → q ≤ r → ∀ a : ℕ → ℂ,
        ‖∑ i ∈ Finset.Icc p q, a i • e i‖ ≤
          (1 + γ j) * ‖∑ i ∈ Finset.Icc p r, a i • e i‖ :=
    fun j => he.2.2 (γ j) (hγ j)
  choose threshold hthreshold using hthreshold
  have hstage : ∀ j n : ℕ, ∃ D : Finset (ℕ →₀ ℂ), D.Nonempty ∧
      (∀ b ∈ D, HasFlatCoefficients b) ∧
      (∀ b ∈ D, ∀ i ∈ b.support, n ≤ i) ∧
      (∀ b ∈ D, |‖Finsupp.linearCombination ℂ e b‖ - 1| ≤ η j) ∧
      ∀ z : ℕ →₀ ℂ, HasFlatCoefficients z →
        Finsupp.linearCombination ℂ e z ≠ 0 →
        (∀ i ∈ z.support, n ≤ i) →
        |‖Finsupp.linearCombination ℂ e z‖ - 1| ≤ η j →
        ∃ b ∈ D, ∃ θ ∈ unitScalars,
          ‖unitNormalize (Finsupp.linearCombination ℂ e b) -
            θ • unitNormalize (Finsupp.linearCombination ℂ e z)‖ ≤ 1 + η j :=
    fun j n => finite_sparse_flat_cover e he.2.1 n (hη j) hno
  choose family hfamily using hstage
  let upper : ℕ → ℕ → ℕ := fun j n => ((family j n).biUnion Finsupp.support).sup id + 1
  let next : ℕ → ℕ → ℕ := fun j n => max (upper j n) (max (n + 1) (threshold (j + 1)))
  let m : ℕ → ℕ := Nat.rec (threshold 0) (fun j n => next j n)
  have hmnext (j : ℕ) : m (j + 1) = next j (m j) := rfl
  have hm : StrictMono m := by
    apply strictMono_nat_of_lt_succ
    intro j
    rw [hmnext]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have hmthreshold : ∀ j, threshold j ≤ m j := by
    intro j
    cases j with
    | zero => exact le_rfl
    | succ j =>
        rw [hmnext]
        exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  refine ⟨{
    m := m
    strictMono := hm
    families := fun j => family j (m j)
    nonempty := fun j => (hfamily j (m j)).1
    flat := fun j => (hfamily j (m j)).2.1
    support := ?_
    norm := fun j => (hfamily j (m j)).2.2.2.1
    projection := ?_
    cover := fun j => (hfamily j (m j)).2.2.2.2 }⟩
  · intro j b hb i hi
    refine ⟨(hfamily j (m j)).2.2.1 b hb i hi, ?_⟩
    have hiunion : i ∈ (family j (m j)).biUnion Finsupp.support :=
      Finset.mem_biUnion.mpr ⟨b, hb, hi⟩
    have hile : i ≤ ((family j (m j)).biUnion Finsupp.support).sup id :=
      Finset.le_sup (f := id) hiunion
    have hupper : upper j (m j) ≤ m (j + 1) := by
      rw [hmnext]
      exact Nat.le_max_left _ _
    dsimp [upper] at hupper
    omega
  · intro j p q r hp hpq hqr a
    exact hthreshold j p q r ((hmthreshold j).trans hp) hpq hqr a

end SurveyStatements.P1
