import Posets.WolfePreservationNecessaryAtomic
import Mathlib.Data.Fintype.EquivFin

/-! Uniform finite overlap of large atomic coordinates can be resolved into
finitely many disjoint coordinate families. This is a set-theoretic partition;
it does not assert that these pieces are open or vary continuously. -/

noncomputable section
open Set Filter Topology
namespace Posets

theorem wolfe_finite_relation_coloring {K L : Type*} (A : L → Set K) (N : ℕ)
    (hA : ∀ y : K, Nonempty ({x : L // y ∈ A x} ↪ Fin N)) :
    ∃ D : Fin N → L → Set K,
      (∀ x, A x = ⋃ i, D i x) ∧
      (∀ i, Pairwise (fun x x' => Disjoint (D i x) (D i x'))) ∧
      (∀ x, Pairwise (fun i j => Disjoint (D i x) (D j x))) := by
  classical
  let e (y : K) := Classical.choice (hA y)
  let D (i : Fin N) (x : L) : Set K := {y | ∃ h : y ∈ A x, e y ⟨x, h⟩ = i}
  refine ⟨D, ?_, ?_, ?_⟩
  · intro x
    ext y
    constructor
    · intro h
      exact mem_iUnion.mpr ⟨e y ⟨x, h⟩, h, rfl⟩
    · intro h
      obtain ⟨i, h, _⟩ := mem_iUnion.mp h
      exact h
  · intro i x x' hxx'
    apply disjoint_left.mpr
    rintro y ⟨hy, hey⟩ ⟨hy', hey'⟩
    exact hxx' (congrArg Subtype.val ((e y).injective (hey.trans hey'.symm)))
  · intro x i j hij
    apply disjoint_left.mpr
    rintro y ⟨hy, hey⟩ ⟨hy', hey'⟩
    exact hij (hey.symm.trans hey')

theorem wolfe_large_coordinates_finite {𝕜 L : Type*} [RCLike 𝕜]
    (a : JLMS.ellOneOn 𝕜 L) {δ : ℝ} (hδ : 0 < δ) :
    {x | δ ≤ ‖a x‖}.Finite := by
  have h := (JLMS.ellOneOn_summable_norm a).tendsto_cofinite_zero.eventually (gt_mem_nhds hδ)
  convert Filter.mem_cofinite.mp h using 1
  ext x
  simp

section Atomic
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]

theorem wolfeAtomicCrossRow_uniform_finite_fibers (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, 0 < m ∧ ∀ y : K,
      Nonempty ({x : L // δ ≤ ‖wolfeAtomicCrossRow N S y x‖} ↪ Fin m) := by
  classical
  obtain ⟨m, hm⟩ := exists_nat_gt (‖S‖ / δ)
  have hmpos : 0 < m := by
    have : 0 ≤ ‖S‖ / δ := by positivity
    exact_mod_cast this.trans_lt hm
  refine ⟨m, hmpos, ?_⟩
  intro y
  let A : Set L := {x | δ ≤ ‖wolfeAtomicCrossRow N S y x‖}
  have hA : A.Finite := wolfe_large_coordinates_finite (wolfeAtomicCrossRow N S y) hδ
  letI : Fintype A := hA.fintype
  have hcard : (hA.toFinset.card : ℝ) * δ ≤ ‖S‖ :=
    wolfeAtomicCrossRow_finset_overlap N S y hA.toFinset
      (fun x hx => hA.mem_toFinset.mp hx)
  have hlt : (hA.toFinset.card : ℝ) < m := by
    exact (mul_lt_mul_iff_left₀ hδ).mp (hcard.trans_lt ((div_lt_iff₀ hδ).mp hm))
  change Nonempty (A ↪ Fin m)
  apply Function.Embedding.nonempty_of_card_le
  rw [Fintype.card_fin]
  have hc : Fintype.card A = hA.toFinset.card := hA.card_toFinset.symm
  rw [hc]
  exact (by exact_mod_cast hlt : hA.toFinset.card < m).le

theorem wolfeAtomicCrossRow_disjoint_colors (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : Fin m → L → Set K,
      (∀ x, {y | δ ≤ ‖wolfeAtomicCrossRow N S y x‖} = ⋃ i, D i x) ∧
      (∀ i, Pairwise (fun x x' => Disjoint (D i x) (D i x'))) ∧
      (∀ x, Pairwise (fun i j => Disjoint (D i x) (D j x))) := by
  obtain ⟨m, hm, he⟩ := wolfeAtomicCrossRow_uniform_finite_fibers N S hδ
  obtain ⟨D, hD⟩ := wolfe_finite_relation_coloring
    (fun x => {y | δ ≤ ‖wolfeAtomicCrossRow N S y x‖}) m he
  exact ⟨m, hm, D, hD⟩

end Atomic

section Mass
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem wolfeMass_iUnion_finite {I : Type*} [Fintype I]
    (M : JLMS.AtomicDualModel 𝕜 K) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (U : I → Set K) (hU : Pairwise (fun i j => Disjoint (U i) (U j))) :
    wolfeMass M μ (⋃ i, U i) = ∑ i, wolfeMass M μ (U i) := by
  classical
  have hsum : ∀ s : Finset I, ∑ i ∈ s, wolfeMass M μ (U i) =
      wolfeMass M μ (⋃ i ∈ s, U i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, ih]
        simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
        symm
        apply wolfeMass_union
        simp only [disjoint_iUnion_right]
        intro j hj
        exact hU (fun hij => hi (hij ▸ hj))
  simpa using (hsum Finset.univ).symm

theorem wolfeMass_exists_large_color
    (M : JLMS.AtomicDualModel 𝕜 K) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    {m : ℕ} (hm : 0 < m) (U : Fin m → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    {d : ℝ} (hd : d ≤ wolfeMass M μ (⋃ i, U i)) :
    ∃ i, d / m ≤ wolfeMass M μ (U i) := by
  classical
  rw [wolfeMass_iUnion_finite M μ U hU] at hd
  by_contra hn
  push_neg at hn
  have hsum : ∑ i : Fin m, wolfeMass M μ (U i) < ∑ _i : Fin m, d / m := by
    apply Finset.sum_lt_sum (fun i _ => (hn i).le)
    exact ⟨⟨0, hm⟩, Finset.mem_univ _, hn _⟩
  have he : (∑ _i : Fin m, d / m) = d := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmn : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [he] at hsum
  exact (not_lt_of_ge hd) hsum

end Mass

section Factorization
variable {𝕜 K L X : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem wolfeFactorizationLift_disjoint_mass_colors (M : JLMS.AtomicDualModel 𝕜 K)
    (N : JLMS.AtomicDualModel 𝕜 L)
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (hc : c ≠ 0) (hn : ‖c‖ * ‖R‖ ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ D : Fin m → L → Set K,
      (∀ i, Pairwise (fun x x' => Disjoint (D i x) (D i x'))) ∧
      (∀ x, ∃ i, ε ≤ wolfeMass M (wolfeFactorizationLift T R c x) (D i x)) := by
  have hd : 0 < ‖c‖ / (2 * (‖T‖ + 1)) := div_pos (norm_pos_iff.mpr hc) (by positivity)
  obtain ⟨m, hm, D, hD, hdisj, hcolors⟩ := wolfeAtomicCrossRow_disjoint_colors N S hd
  let d : ℝ := ‖c‖ / (2 * (‖S‖ + 1))
  have hdp : 0 < d := div_pos (norm_pos_iff.mpr hc) (by positivity)
  refine ⟨m, hm, d / m, div_pos hdp (by exact_mod_cast hm), D, hdisj, ?_⟩
  intro x
  apply wolfeMass_exists_large_color M (wolfeFactorizationLift T R c x) hm (fun i => D i x)
    (hcolors x)
  rw [← hD x]
  exact wolfeFactorizationLift_large_coordinate_mass M N T R S hfactor c hc hn x

end Factorization
end Posets
