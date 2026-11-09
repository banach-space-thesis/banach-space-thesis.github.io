import PL1.FiniteDualDisjointization
import PL1.ALRenorming

/-!
# From disjoint to positive lower-one estimates

All primal disjointizations are finite approximations from Riesz–Kantorovich.
Only the dual uses principal bands, supplied by its existing order completeness.
-/
noncomputable section
open scoped BigOperators
namespace PL1.PositiveLowerOneBridge

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [BanachLattice E]

lemma dual_sup_approx (φ ψ : StrongDual ℝ E) {u : E} (hu : 0 ≤ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y z : E, 0 ≤ y ∧ 0 ≤ z ∧ y+z=u ∧ (φ ⊔ ψ) u - ε < φ y + ψ z := by
  have hL : IsLUB
      {r : ℝ | ∃ y z : E, 0 ≤ y ∧ 0 ≤ z ∧ y+z=u ∧ r=φ y+ψ z}
      ((φ ⊔ ψ) u) := OrderDualSpace.isLUB_sup_apply (φ := φ.toOrderDualSpace)
        (ψ := ψ.toOrderDualSpace) hu
  by_contra! h
  have hle : (φ ⊔ ψ) u ≤ (φ ⊔ ψ) u - ε := hL.2 (by
    rintro r ⟨y,z,hy,hz,hyz,rfl⟩
    exact h y z hy hz hyz)
  linarith

lemma disjoint_dual_sum (n : ℕ) (φ : StrongDual ℝ E) (ψ : Fin n → StrongDual ℝ E)
    (h : ∀ i, IsVLDisjoint φ (ψ i)) : IsVLDisjoint φ (∑ i, ψ i) := by
  classical
  suffices ∀ s : Finset (Fin n), IsVLDisjoint φ (∑ i ∈ s, ψ i) by simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using isVLDisjoint_zero_right φ
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i).add_right ih

/-- A disjoint dual family almost attains its total mass on a positive primal
partition. No primal order supremum is taken. -/
lemma exists_partition_mass (n : ℕ) (ψ : Fin n → StrongDual ℝ E)
    (hψ : ∀ i, 0 ≤ ψ i) (hd : Pairwise fun i j => IsVLDisjoint (ψ i) (ψ j))
    (u : E) (hu : 0 ≤ u) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : Fin n → E, (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ u ∧
      (∑ i, ψ i u) - ε < ∑ i, ψ i (y i) := by
  classical
  induction n generalizing u ε with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, by simpa using hu, by simpa using hε⟩
  | succ n ih =>
    let ψt : Fin n → StrongDual ℝ E := fun i => ψ i.succ
    have hψt : ∀ i, 0 ≤ ψt i := fun i => hψ i.succ
    have hdt : Pairwise fun i j => IsVLDisjoint (ψt i) (ψt j) :=
      fun i j hij => hd (fun h => hij (Fin.succ_injective _ h))
    have hds : IsVLDisjoint (ψ 0) (∑ i, ψt i) := disjoint_dual_sum n (ψ 0) ψt
      (fun i => hd (Fin.succ_ne_zero i).symm)
    have hsum0 : 0 ≤ ∑ i, ψt i := Finset.sum_nonneg fun i _ => hψt i
    obtain ⟨a,b,ha,hb,hab,hm⟩ := dual_sup_approx (ψ 0) (∑ i, ψt i) hu (half_pos hε)
    rw [← add_eq_sup_of_isVLDisjoint_of_nonneg (hψ 0) hsum0 hds] at hm
    obtain ⟨yt,hyt,hytu,hym⟩ := ih ψt hψt hdt b hb (ε/2) (half_pos hε)
    refine ⟨Fin.cons a yt, ?_, ?_, ?_⟩
    · intro i
      exact Fin.cases ha hyt i
    · simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using
        (add_le_add (le_refl a) hytu).trans (le_of_eq hab)
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      change ψ 0 u + ∑ i, ψt i u - ε < ψ 0 a + ∑ i, ψt i (yt i)
      simp only [add_apply, sum_apply] at hm
      linarith

omit [BanachLattice E] in
lemma partition_pair_le (n : ℕ) (y : Fin n → E) (hy : ∀ i, 0 ≤ y i)
    {u : E} (hs : (∑ i, y i) ≤ u) {i j : Fin n} (hij : i ≠ j) :
    y i + y j ≤ u := by
  classical
  calc
    _ = ∑ k ∈ ({i,j} : Finset (Fin n)), y k := by simp [hij]
    _ ≤ ∑ k, y k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => hy k)
    _ ≤ u := hs

omit [BanachLattice E] in
/-- The positive excess over half the total gives a genuine disjoint family. -/
lemma partition_excess_disjoint (n : ℕ) (y : Fin n → E) (hy : ∀ i, 0 ≤ y i)
    {u : E} (hs : (∑ i, y i) ≤ u) :
    Pairwise fun i j => IsVLDisjoint ((y i + y i - u)⁺) ((y j + y j - u)⁺) := by
  intro i j hij
  have hp := partition_pair_le n y hy hs hij
  have hraw : y i + y i - u ≤ -(y j + y j - u) := by
    have h := add_le_add hp hp
    have heq : (y i+y j)+(y i+y j) = (y i+y i)+(y j+y j) := by abel
    rw [heq] at h
    have ht := sub_le_sub_right (sub_le_sub_right h u) (y j+y j)
    convert ht using 1 <;> abel
  apply (isVLDisjoint_comm.mp (isVLDisjoint_posPart_negPart (y j+y j-u))).mono_left
  rw [abs_of_nonneg (posPart_nonneg _), abs_of_nonneg (negPart_nonneg _)]
  change (y i+y i-u) ⊔ 0 ≤ (-(y j+y j-u)) ⊔ 0
  exact sup_le_sup_right hraw 0

lemma sum_disjoint_dual_apply_le {C : ℝ} (hC : 0 ≤ C)
    (hdis : ∀ (n : ℕ) (x : Fin n → E), (∀ i, 0 ≤ x i) →
      (Pairwise fun i j => IsVLDisjoint (x i) (x j)) → ∑ i, ‖x i‖ ≤ C * ‖∑ i, x i‖)
    (n : ℕ) (ψ : Fin n → StrongDual ℝ E) (hψ : ∀ i, 0 ≤ ψ i)
    (hψn : ∀ i, ‖ψ i‖ ≤ 1) (hd : Pairwise fun i j => IsVLDisjoint (ψ i) (ψ j))
    (u : E) (hu : 0 ≤ u) : ∑ i, ψ i u ≤ C * ‖u‖ := by
  classical
  by_contra! hbad
  let ε := ((∑ i, ψ i u) - C*‖u‖)/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨y,hy,hys,hm⟩ := exists_partition_mass n ψ hψ hd u hu ε hε
  let z : Fin n → E := fun i => (y i+y i-u)⁺
  have hz (i) : 0 ≤ z i := posPart_nonneg _
  have hyle (i) : y i ≤ u := (Finset.single_le_sum (fun j _ => hy j) (Finset.mem_univ i)).trans hys
  have hzle (i) : z i ≤ u := by
    change (y i+y i-u) ⊔ 0 ≤ u
    apply sup_le _ hu
    exact (sub_le_iff_le_add).mpr (add_le_add (hyle i) (hyle i))
  have hzd : Pairwise fun i j => IsVLDisjoint (z i) (z j) := partition_excess_disjoint n y hy hys
  have hznorm : ‖∑ i, z i‖ ≤ ‖u‖ := norm_le_norm_of_abs_le_abs
    (ComplementedLattice.abs_disjoint_sum_le n z hzd u (fun i => by
      rw [abs_of_nonneg (hz i), abs_of_nonneg hu]; exact hzle i))
  have hzup : (∑ i, ψ i (z i)) ≤ C*‖u‖ := calc
    _ ≤ ∑ i, ‖z i‖ := Finset.sum_le_sum fun i _ => calc
      ψ i (z i) ≤ ‖ψ i (z i)‖ := le_abs_self _
      _ ≤ ‖ψ i‖*‖z i‖ := (ψ i).le_opNorm _
      _ ≤ ‖z i‖ := by simpa using mul_le_mul_of_nonneg_right (hψn i) (norm_nonneg _)
    _ ≤ C*‖∑ i, z i‖ := hdis n z hz hzd
    _ ≤ C*‖u‖ := mul_le_mul_of_nonneg_left hznorm hC
  have hzlow : 2*(∑ i, ψ i (y i)) - ∑ i, ψ i u ≤ ∑ i, ψ i (z i) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h := StrongDual.apply_le_apply_of_nonneg (hψ i) (le_posPart (y i+y i-u))
    simpa only [map_sub, map_add, two_mul] using h
  dsimp [ε] at hm
  linarith

/-- The norm of a disjoint sum of positive unit dual functionals is controlled
by the primal disjoint lower-one constant. -/
lemma norm_sum_disjoint_dual_le {C : ℝ} (hC : 0 ≤ C)
    (hdis : ∀ (n : ℕ) (x : Fin n → E), (∀ i, 0 ≤ x i) →
      (Pairwise fun i j => IsVLDisjoint (x i) (x j)) → ∑ i, ‖x i‖ ≤ C * ‖∑ i, x i‖)
    (n : ℕ) (ψ : Fin n → StrongDual ℝ E) (hψ : ∀ i, 0 ≤ ψ i)
    (hψn : ∀ i, ‖ψ i‖ ≤ 1) (hd : Pairwise fun i j => IsVLDisjoint (ψ i) (ψ j)) :
    ‖∑ i, ψ i‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hsum : 0 ≤ ∑ i, ψ i := Finset.sum_nonneg fun i _ => hψ i
  calc
    _ ≤ (∑ i, ψ i) |x| := StrongDual.abs_apply_le_apply_abs hsum x
    _ = ∑ i, ψ i |x| := sum_apply _ _ _
    _ ≤ C*‖|x|‖ := sum_disjoint_dual_apply_le hC hdis n ψ hψ hψn hd |x| (abs_nonneg x)
    _ = C*‖x‖ := by rw [norm_abs_eq_norm]

/-- A uniform disjoint lower-one estimate implies the corresponding estimate
for every positive finite family, with exactly the same constant. -/
theorem positiveLowerOne_of_disjoint {C : ℝ} (hC : 0 ≤ C)
    (hdis : ∀ (n : ℕ) (x : Fin n → E), (∀ i, 0 ≤ x i) →
      (Pairwise fun i j => IsVLDisjoint (x i) (x j)) → ∑ i, ‖x i‖ ≤ C * ‖∑ i, x i‖) :
    ALRenorming.PositiveLowerOne (E := E) C := by
  refine ⟨hC, ?_⟩
  intro n x hx
  choose ν hν hνn hνx using fun i => StrongDual.exists_positive_dual_norming (hx i)
  obtain ⟨ψ,hψ,hψle,hψd,hψmaj⟩ :=
    FiniteDualDisjointization.exists_disjoint_majorizing_refinement n ν hν
  have hψn (i) : ‖ψ i‖ ≤ 1 := (norm_le_norm_of_abs_le_abs (by
    rw [abs_of_nonneg (hψ i), abs_of_nonneg (hν i)]
    exact hψle i)).trans (hνn i)
  have hnorm := norm_sum_disjoint_dual_le hC hdis n ψ hψ hψn hψd
  calc
    ∑ i, ‖x i‖ = ∑ i, ν i (x i) := by simp only [hνx]
    _ ≤ ∑ i, (∑ j, ψ j) (x i) := Finset.sum_le_sum fun i _ =>
      StrongDual.le_iff.mp (hψmaj i) (x i) (hx i)
    _ = (∑ j, ψ j) (∑ i, x i) := (map_sum _ _ _).symm
    _ ≤ ‖(∑ j, ψ j) (∑ i, x i)‖ := le_abs_self _
    _ ≤ ‖∑ j, ψ j‖ * ‖∑ i, x i‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C*‖∑ i, x i‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

/-- Uniform finite summing bounds give the positive lower-one estimate. -/
theorem positiveLowerOne_of_summing {C : ℝ} (hC : 0 ≤ C)
    (hOne : ∀ (n : ℕ) (S : E →L[ℝ] EuclideanSpace ℝ (Fin n)),
      ComplementedLattice.OneSummingWith S (C * ‖S‖))
    (hTwo : ∀ (n : ℕ) (T : (Fin n → ℝ) →L[ℝ] E),
      ComplementedLattice.TwoSummingWith T (C * ‖T‖)) :
    ALRenorming.PositiveLowerOne (E := E) (C ^ 2) :=
  positiveLowerOne_of_disjoint (sq_nonneg C)
    (DisjointNormingFunctionals.positive_disjoint_sum_norm_le C hC hOne hTwo)

/-- The positive lower-one estimate for an actual complemented copy, with all
ambient summing hypotheses explicit and no projection-property premise. -/
theorem positiveLowerOne_of_complemented_ambient
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Q : EnfloStarbird.ComplementedCopy ℝ E Y) {G : ℝ} (hG : 0 ≤ G)
    (hOne : ∀ (n : ℕ) (S : Y →L[ℝ] EuclideanSpace ℝ (Fin n)),
      ComplementedLattice.OneSummingWith S (G * ‖S‖))
    (hTwo : ∀ (n : ℕ) (T : (Fin n → ℝ) →L[ℝ] Y),
      ComplementedLattice.TwoSummingWith T (G * ‖T‖)) :
    ALRenorming.PositiveLowerOne (E := E) ((G * ‖Q.embedding‖ * ‖Q.retraction‖) ^ 2) := by
  obtain ⟨hC, hOneE, hTwoE⟩ := ComplementedLattice.uniform_finite_summing_estimates Q hG hOne hTwo
  exact positiveLowerOne_of_summing hC hOneE hTwoE

end PL1.PositiveLowerOneBridge




