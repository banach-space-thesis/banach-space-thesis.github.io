import JLMS.L1Restriction

/-!
# Section 7: recursive selection of large finite atomic pieces

The argument is stated for any operator into ℓ¹(I). Applied to the atomic
coordinates of T*, it is Proposition 7.1 of the paper. The proof removes the
previous finite coordinates by a finite-rank perturbation, chooses a vector in
the unit ball, and then truncates its remaining mass to finitely many atoms.
-/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {I : Type*}

omit [NormedAddCommGroup E] in
/-- A reusable finite-history recursion: if a witness can avoid any finite
forbidden set, an infinite sequence can be chosen with disjoint finite pieces. -/
theorem exists_disjoint_finite_witnesses (P : E → Finset I → Prop)
    (hnext : ∀ s : Finset I, ∃ x : E, ∃ A : Finset I, P x A ∧ Disjoint A s) :
    ∃ x : ℕ → E, ∃ A : ℕ → Finset I,
      (∀ j, P (x j) (A j)) ∧ Pairwise fun i j => Disjoint (A i) (A j) := by
  classical
  choose x A hP havoid using hnext
  let past : ℕ → Finset I := Nat.rec ∅ (fun _ s => s ∪ A s)
  have hstep (j : ℕ) : past (j + 1) = past j ∪ A (past j) := rfl
  have hmono : Monotone past := monotone_nat_of_le_succ (fun j => by
    rw [hstep]
    exact Finset.subset_union_left)
  have hin (j : ℕ) : A (past j) ⊆ past (j + 1) := by
    rw [hstep]
    exact Finset.subset_union_right
  refine ⟨fun j => x (past j), fun j => A (past j), fun j => hP _, ?_⟩
  intro i j hij
  have hforward (a b : ℕ) (hab : a < b) : Disjoint (A (past a)) (A (past b)) := by
    apply (havoid (past b)).symm.mono_left
    exact (hin a).trans (hmono (Nat.succ_le_of_lt hab))
  obtain hlt | hgt := lt_or_gt_of_ne hij
  · exact hforward i j hlt
  · exact (hforward j i hgt).symm

/-- A strict operator-norm bound is witnessed on the unit sphere. -/
theorem exists_unit_norm_image_gt (T : E →L[𝕜] F) {r : ℝ}
    (hr : 0 ≤ r) (hT : r < ‖T‖) : ∃ x : E, ‖x‖ = 1 ∧ r < ‖T x‖ := by
  by_contra h
  push_neg at h
  exact (not_le_of_gt hT) (ContinuousLinearMap.opNorm_le_of_unit_norm hr h)

/-- The next finite piece can avoid any prescribed finite collection of atoms. -/
theorem exists_large_atomic_piece_avoiding (T : E →L[𝕜] ellOneOn 𝕜 I)
    {r : ℝ} (hr : 0 ≤ r) (hT : r < essentialNorm T) (s : Finset I) :
    ∃ x : E, ∃ A : Finset I, ‖x‖ ≤ 1 ∧
      (A : Set I) ⊆ Function.support (T x) ∧ Disjoint A s ∧
      r < ‖restrictionL1 (A : Set I) (T x)‖ := by
  let R := restrictionL1 (𝕜 := 𝕜) (s : Set I)
  let Q := (restrictionL1 (𝕜 := 𝕜) (s : Set I)ᶜ).comp T
  have hcompact : IsCompactOperator (R.comp T) :=
    (restrictionL1_compact (𝕜 := 𝕜) s).comp_clm T
  have heq : T - R.comp T = Q := by
    ext x i
    by_cases hi : i ∈ s <;> simp [R, Q, hi]
  have hnorm : r < ‖Q‖ := by
    have hb := essentialNorm_le_norm_sub T (R.comp T) hcompact
    rw [heq] at hb
    exact hT.trans_le hb
  obtain ⟨x, hx, hlarge⟩ := exists_unit_norm_image_gt Q hr hnorm
  obtain ⟨A, hA, hmass⟩ := exists_finite_restrictionL1_mass (Q x) hlarge
  have havoid : ∀ i ∈ A, i ∉ s := by
    intro i hi his
    have hn := hA hi
    exact hn (by simp [Q, his])
  have hrestrict : restrictionL1 (A : Set I) (Q x) = restrictionL1 (A : Set I) (T x) := by
    ext i
    by_cases hi : i ∈ A
    · simp [Q, hi, havoid i hi]
    · simp [hi]
  refine ⟨x, A, hx.le, ?_, Finset.disjoint_left.mpr havoid, ?_⟩
  · intro i hi
    have hn := hA hi
    simpa [Q, havoid i hi] using hn
  · rwa [hrestrict] at hmass

/-- Proposition 7.1 in reusable ℓ¹ coordinates. The finite pieces are pairwise
disjoint, lie in the actual supports, and each has mass strictly above r. -/
theorem exists_disjoint_large_atomic_pieces (T : E →L[𝕜] ellOneOn 𝕜 I)
    {r : ℝ} (hr : 0 ≤ r) (hT : r < essentialNorm T) :
    ∃ x : ℕ → E, ∃ A : ℕ → Finset I,
      (∀ j, ‖x j‖ ≤ 1) ∧
      (∀ j, (A j : Set I) ⊆ Function.support (T (x j))) ∧
      (Pairwise fun i j => Disjoint (A i) (A j)) ∧
      ∀ j, r < ‖restrictionL1 (A j : Set I) (T (x j))‖ := by
  choose x A hx hsupport havoid hmass using exists_large_atomic_piece_avoiding T hr hT
  let past : ℕ → Finset I := Nat.rec ∅ (fun _ s => s ∪ A s)
  have hstep (j : ℕ) : past (j + 1) = past j ∪ A (past j) := rfl
  have hmono : Monotone past := monotone_nat_of_le_succ (fun j => by
    rw [hstep]
    exact Finset.subset_union_left)
  have hin (j : ℕ) : A (past j) ⊆ past (j + 1) := by
    rw [hstep]
    exact Finset.subset_union_right
  refine ⟨fun j => x (past j), fun j => A (past j), fun j => hx _,
    fun j => hsupport _, ?_, fun j => hmass _⟩
  intro i j hij
  have hforward (a b : ℕ) (hab : a < b) : Disjoint (A (past a)) (A (past b)) := by
    apply (havoid (past b)).symm.mono_left
    exact (hin a).trans (hmono (Nat.succ_le_of_lt hab))
  obtain hlt | hgt := lt_or_gt_of_ne hij
  · exact hforward i j hlt
  · exact (hforward j i hgt).symm

end JLMS
