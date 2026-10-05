import JLMS.EssentialWeight

/-!
# Lemma 6.1: diagonal selection with summable losses

At each stage, the remaining finite atomic pieces avoid a closed region used
by the earlier stages. Corollary 5.5 supplies one neighborhood collection and
a subsequence with small weight there. Shrink the collection away from the
used region, remove it from the remaining pieces, and charge the lost mass to
θ / 2^(n+1). The threshold is r + θ / 2^n, so every selected piece exceeds r.

This coordinate argument keeps the original source vectors. It can therefore
be applied to the Banach adjoint without losing the dual-unit-ball condition.
-/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The recursive invariant: infinitely many large disjoint finite pieces
remain outside the region already assigned to selected neighborhoods. -/
structure AtomicSelectionState (L : E →L[𝕜] ellOneOn 𝕜 K) (q : ℝ) where
  vectors : ℕ → E
  pieces : ℕ → Finset K
  unit : ∀ j, ‖vectors j‖ ≤ 1
  support : ∀ j, (pieces j : Set K) ⊆ Function.support (L (vectors j))
  disjoint : Pairwise fun i j => Disjoint (pieces i) (pieces j)
  large : ∀ j, q < ‖restrictionL1 (pieces j : Set K) (L (vectors j))‖
  used : Set K
  closed_used : IsClosed used
  avoid_used : ∀ j, ∀ k ∈ pieces j, k ∉ used

/-- One selected piece and the next state of the recursion. -/
structure AtomicSelectionStep {L : E →L[𝕜] ellOneOn 𝕜 K} {q : ℝ}
    (S : AtomicSelectionState L q) (q' : ℝ) where
  vector : E
  piece : Finset K
  neighborhoods : NeighborhoodFamily (fun k : ↥piece => (k : K))
  unit : ‖vector‖ ≤ 1
  support : (piece : Set K) ⊆ Function.support (L vector)
  large : q < ‖restrictionL1 (piece : Set K) (L vector)‖
  disjoint_used : Disjoint (⋃ k, neighborhoods.sets k) S.used
  next : AtomicSelectionState L q'
  next_used : next.used = S.used ∪ ⋃ k, neighborhoods.sets k

/-- The induction step in the paper's diagonal argument. -/
theorem exists_atomicSelectionStep (hK : IsScattered K)
    {L : E →L[𝕜] ellOneOn 𝕜 K} {q q' ε : ℝ}
    (S : AtomicSelectionState L q) (hε : 0 < ε) (hqq' : q' = q - ε) :
    Nonempty (AtomicSelectionStep S q') := by
  have hbound (j : ℕ) : ‖L (S.vectors j)‖ ≤ ‖L‖ :=
    (L.le_opNorm _).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (S.unit j) (norm_nonneg L))
  obtain ⟨n, U, s, hs, hsmall⟩ := exists_neighborhood_subsequence_small_weight hK
    (fun j => L (S.vectors j)) S.pieces S.disjoint ‖L‖ hbound hε
  obtain ⟨V, hV⟩ := exists_neighborhoodFamily_shrink hK U S.closed_used.isOpen_compl
    (fun k => S.avoid_used n k.val k.property)
  let C : Set K := ⋃ k, V.sets k
  have hCclosed : IsClosed C := isClosed_iUnion_of_finite (fun k => (V.clopen k).isClosed)
  have hCsub : C ⊆ ⋃ k, U.sets k := by
    intro k hk
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨i, (hV i hi).1⟩
  have hCused : Disjoint C S.used := by
    apply Set.disjoint_left.mpr
    intro k hk hku
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hk
    exact (hV i hi).2 hku
  let A (j : ℕ) := (S.pieces (s j)).filter (fun k => k ∉ C)
  have hAlarge (j : ℕ) : q' < ‖restrictionL1 (A j : Set K) (L (S.vectors (s j)))‖ := by
    have hb := restrictionL1_mass_after_remove (S.pieces (s j)) C (L (S.vectors (s j)))
    have hsm := (restrictionL1_norm_mono hCsub (L (S.vectors (s j)))).trans_lt (hsmall j)
    have hlarge := S.large (s j)
    rw [hqq']
    change q - ε < ‖restrictionL1 ((S.pieces (s j)).filter (fun k => k ∉ C) : Set K)
      (L (S.vectors (s j)))‖
    linarith
  let S' : AtomicSelectionState L q' :=
    { vectors := fun j => S.vectors (s j)
      pieces := A
      unit := fun j => S.unit _
      support := by
        intro j k hk
        exact S.support _ (Finset.mem_of_mem_filter _ hk)
      disjoint := by
        intro i j hij
        exact (S.disjoint (hs.injective.ne hij)).mono (Finset.filter_subset _ _)
          (Finset.filter_subset _ _)
      large := hAlarge
      used := S.used ∪ C
      closed_used := S.closed_used.union hCclosed
      avoid_used := by
        intro j k hk hku
        obtain ⟨hkF, hkC⟩ := Finset.mem_filter.mp hk
        exact hku.elim (S.avoid_used _ k hkF) hkC }
  exact ⟨⟨S.vectors n, S.pieces n, V, S.unit n, S.support n, S.large n, hCused, S', rfl⟩⟩

/-- Lemma 6.1 in coordinates: the infinite diagonal recursion yields globally
disjoint neighborhoods while retaining a strict mass margin above r. -/
theorem exists_separated_atomic_pieces (hK : IsScattered K)
    (L : E →L[𝕜] ellOneOn 𝕜 K) (r θ : ℝ) (hθ : 0 < θ)
    (x : ℕ → E) (A : ℕ → Finset K) (hx : ∀ j, ‖x j‖ ≤ 1)
    (hsupport : ∀ j, (A j : Set K) ⊆ Function.support (L (x j)))
    (hA : Pairwise fun i j => Disjoint (A i) (A j))
    (hlarge : ∀ j, r + θ < ‖restrictionL1 (A j : Set K) (L (x j))‖) :
    ∃ y : ℕ → E, ∃ B : ℕ → Finset K,
      ∃ U : ∀ j, NeighborhoodFamily (fun k : ↥(B j) => (k : K)),
        (∀ j, ‖y j‖ ≤ 1) ∧
        (∀ j, (B j : Set K) ⊆ Function.support (L (y j))) ∧
        (Pairwise fun i j => Disjoint (⋃ k, (U i).sets k) (⋃ k, (U j).sets k)) ∧
        ∀ j, r < ‖restrictionL1 (B j : Set K) (L (y j))‖ := by
  let q (n : ℕ) := r + θ / (2 : ℝ) ^ n
  have hq (n : ℕ) : r < q n := by
    dsimp [q]
    exact lt_add_of_pos_right _ (div_pos hθ (pow_pos (by norm_num) _))
  have hqstep (n : ℕ) : q (n + 1) = q n - θ / (2 : ℝ) ^ (n + 1) := by
    dsimp [q]
    rw [pow_succ]
    field_simp
    ring
  let S₀ : AtomicSelectionState L (q 0) :=
    { vectors := x, pieces := A, unit := hx, support := hsupport, disjoint := hA
      large := by simpa only [q, pow_zero, div_one] using hlarge
      used := ∅, closed_used := isClosed_empty
      avoid_used := by intro j k hk; exact Set.notMem_empty k }
  let step (n : ℕ) (S : AtomicSelectionState L (q n)) : AtomicSelectionStep S (q (n + 1)) :=
    Classical.choice (exists_atomicSelectionStep hK S
      (div_pos hθ (pow_pos (by norm_num) _)) (hqstep n))
  let states : ∀ n : ℕ, AtomicSelectionState L (q n) :=
    fun n => Nat.rec S₀ (fun n S => (step n S).next) n
  let selected (n : ℕ) := step n (states n)
  have hnext (n : ℕ) : (states (n + 1)).used =
      (states n).used ∪ ⋃ k, (selected n).neighborhoods.sets k := (selected n).next_used
  have hmono : Monotone (fun n => (states n).used) := monotone_nat_of_le_succ (fun n => by
    rw [hnext]
    exact Set.subset_union_left)
  have hinside (n : ℕ) : (⋃ k, (selected n).neighborhoods.sets k) ⊆ (states (n + 1)).used := by
    rw [hnext]
    exact Set.subset_union_right
  refine ⟨fun n => (selected n).vector, fun n => (selected n).piece,
    fun n => (selected n).neighborhoods, fun n => (selected n).unit,
    fun n => (selected n).support, ?_, ?_⟩
  · intro i j hij
    have hforward (a b : ℕ) (hab : a < b) :
        Disjoint (⋃ k, (selected a).neighborhoods.sets k)
          (⋃ k, (selected b).neighborhoods.sets k) := by
      exact (selected b).disjoint_used.symm.mono_left
        ((hinside a).trans (hmono (Nat.succ_le_of_lt hab)))
    obtain hlt | hgt := lt_or_gt_of_ne hij
    · exact hforward i j hlt
    · exact (hforward j i hgt).symm
  · intro n
    exact (hq n).trans (selected n).large

end JLMS
