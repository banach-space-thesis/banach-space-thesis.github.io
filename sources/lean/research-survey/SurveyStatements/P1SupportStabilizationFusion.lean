import SurveyStatements.P1SupportStabilizationDeletion

/-! Finite-front refinement and fusion for the support-stabilization lemma. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter Topology

namespace SurveyStatements.P1

theorem support_exists_deletion_finite_family
    (f : Set ℕ → ℕ → ℂ) (hf : SupportAssignmentLocallyConstant f)
    (hcluster : SupportAssignmentSequentialC0Cluster f)
    (A : Finset (Finset ℕ)) (δ : ℝ) (hδ : 0 < δ)
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ L : Set ℕ, L ⊆ M ∧ L.Infinite ∧
      ∀ F ∈ A, ∀ Q : Set ℕ, Q ⊆ L → Q.Infinite →
        SupportDeletionGood f F δ Q := by
  classical
  induction A using Finset.induction_on generalizing M with
  | empty => exact ⟨M, subset_rfl, hM, by simp⟩
  | @insert F A hFA ih =>
    obtain ⟨N, hNM, hN, hA⟩ := ih M hM
    obtain ⟨L, hLN, hL, hF⟩ := support_exists_uniform_deletion f hf hcluster F δ hδ N hN
    refine ⟨L, hLN.trans hNM, hL, ?_⟩
    intro E hE Q hQL hQ
    rcases Finset.mem_insert.mp hE with rfl | hE
    · exact hF Q hQL hQ
    · exact hA E hE Q (hQL.trans hLN) hQ

private structure SupportFusionStage (f : Set ℕ → ℕ → ℂ)
    (δ : ℕ → ℝ) (M : Set ℕ) (n : ℕ) where
  front : Finset ℕ
  tail : Set ℕ
  infinite_tail : tail.Infinite
  tail_subset : tail ⊆ M
  after_prefix : ∀ a ∈ front, ∀ b ∈ tail, a < b
  good : ∀ F ⊆ front, ∀ Q : Set ℕ, Q ⊆ tail → Q.Infinite →
    SupportDeletionGood f F (δ n) Q

private theorem SupportFusionStage.exists_initial
    (f : Set ℕ → ℕ → ℂ) (hf : SupportAssignmentLocallyConstant f)
    (hcluster : SupportAssignmentSequentialC0Cluster f)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ q : SupportFusionStage f δ M 0, q.front = ∅ := by
  obtain ⟨N, hNM, hN, hg⟩ := support_exists_uniform_deletion f hf hcluster ∅ (δ 0) (hδ 0) M hM
  refine ⟨⟨∅, N, hN, hNM, by simp, ?_⟩, rfl⟩
  intro F hF Q hQ hQi
  have h : F = ∅ := Finset.subset_empty.mp hF
  simpa only [h] using hg Q hQ hQi

private theorem SupportFusionStage.exists_next
    (f : Set ℕ → ℕ → ℂ) (hf : SupportAssignmentLocallyConstant f)
    (hcluster : SupportAssignmentSequentialC0Cluster f)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    {M : Set ℕ} {n : ℕ} (q : SupportFusionStage f δ M n) :
    ∃ a : ℕ, ∃ r : SupportFusionStage f δ M (n + 1),
      a ∈ q.tail ∧ r.front = insert a q.front ∧ r.tail ⊆ q.tail := by
  classical
  obtain ⟨a, ha⟩ := q.infinite_tail.nonempty
  obtain ⟨N, hNsub, hNinf, hNgood⟩ := support_exists_deletion_finite_family f hf hcluster
    (insert a q.front).powerset (δ (n + 1)) (hδ (n + 1))
    (q.tail ∩ Ioi a) (infiniteSet_inter_Ioi q.tail q.infinite_tail a)
  let r : SupportFusionStage f δ M (n + 1) :=
    { front := insert a q.front
      tail := N
      infinite_tail := hNinf
      tail_subset := fun b hb => q.tail_subset (hNsub hb).1
      after_prefix := by
        intro b hb c hc
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact (hNsub hc).2
        · exact q.after_prefix b hb c (hNsub hc).1
      good := fun F hF => hNgood F (Finset.mem_powerset.mpr hF) }
  exact ⟨a, r, ha, rfl, fun b hb => (hNsub hb).1⟩

theorem support_exists_deletion_fusion
    (f : Set ℕ → ℕ → ℂ) (hf : SupportAssignmentLocallyConstant f)
    (hcluster : SupportAssignmentSequentialC0Cluster f)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ ν : ℕ → ℕ, ∃ T : ℕ → Set ℕ,
      StrictMono ν ∧ (∀ n, ν n ∈ M) ∧ (∀ n, (T n).Infinite) ∧
      (∀ n, T (n + 1) ⊆ T n) ∧
      (∀ n k, n ≤ k → ν k ∈ T n) ∧
      (∀ n F, F ⊆ (Finset.range n).image ν →
        ∀ Q : Set ℕ, Q ⊆ T n → Q.Infinite → SupportDeletionGood f F (δ n) Q) := by
  classical
  obtain ⟨q₀, hq₀⟩ := SupportFusionStage.exists_initial f hf hcluster δ hδ M hM
  let step (n : ℕ) (q : SupportFusionStage f δ M n) :
      ℕ × SupportFusionStage f δ M (n + 1) :=
    ⟨(SupportFusionStage.exists_next f hf hcluster δ hδ q).choose,
      ((SupportFusionStage.exists_next f hf hcluster δ hδ q).choose_spec).choose⟩
  have hs (n : ℕ) (q : SupportFusionStage f δ M n) :
      (step n q).1 ∈ q.tail ∧ (step n q).2.front = insert (step n q).1 q.front ∧
        (step n q).2.tail ⊆ q.tail :=
    ((SupportFusionStage.exists_next f hf hcluster δ hδ q).choose_spec).choose_spec
  let q : (n : ℕ) → SupportFusionStage f δ M n := Nat.rec q₀ (fun n r => (step n r).2)
  let ν : ℕ → ℕ := fun n => (step n (q n)).1
  have hrec (n : ℕ) : q (n + 1) = (step n (q n)).2 := rfl
  have hmem (n : ℕ) : ν n ∈ (q n).tail := (hs n (q n)).1
  have hprefix (n : ℕ) : (q n).front = (Finset.range n).image ν := by
    induction n with
    | zero => simpa only [q, Finset.range_zero, Finset.image_empty] using hq₀
    | succ n ih =>
      rw [hrec, (hs n (q n)).2.1, ih, Finset.range_add_one, Finset.image_insert]
  have hν : StrictMono ν := by
    apply strictMono_nat_of_lt_succ
    intro n
    apply (q (n + 1)).after_prefix (ν n) _ (ν (n + 1)) (hmem (n + 1))
    rw [hrec, (hs n (q n)).2.1]
    exact Finset.mem_insert_self _ _
  have hnest (n : ℕ) : (q (n + 1)).tail ⊆ (q n).tail := by
    rw [hrec]
    exact (hs n (q n)).2.2
  have hanti : Antitone (fun n => (q n).tail) := antitone_nat_of_succ_le hnest
  refine ⟨ν, fun n => (q n).tail, hν,
    fun n => (q n).tail_subset (hmem n), fun n => (q n).infinite_tail,
    hnest, fun n k hnk => hanti hnk (hmem k), ?_⟩
  intro n F hF
  apply (q n).good F
  simpa only [hprefix] using hF

theorem support_deletion_fusion_coordinate_bound
    (f : Set ℕ → ℕ → ℂ) (δ : ℕ → ℝ) (ν : ℕ → ℕ) (hν : StrictMono ν)
    (T : ℕ → Set ℕ)
    (htail : ∀ n k, n ≤ k → ν k ∈ T n)
    (hgood : ∀ n F, F ⊆ (Finset.range n).image ν →
      ∀ Q : Set ℕ, Q ⊆ T n → Q.Infinite → SupportDeletionGood f F (δ n) Q)
    (P : Set ℕ) (hP : P.Infinite) (hPN : P ⊆ range ν)
    (n : ℕ) (hnP : ν n ∉ P) : ‖f P (ν n)‖ < δ n := by
  classical
  let F : Finset ℕ := ((Finset.range n).image ν).filter (fun i => i ∈ P)
  let R : Set ℕ := P ∩ Ioi (ν n)
  have hR : R.Infinite := infiniteSet_inter_Ioi P hP (ν n)
  have hRT : R ⊆ T n := by
    intro x hx
    obtain ⟨k, rfl⟩ := hPN hx.1
    exact htail n k (hν.lt_iff_lt.mp hx.2).le
  have hFR : (F : Set ℕ) ∪ R = P := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact (Finset.mem_filter.mp hx).2
      · exact hx.1
    · intro hx
      obtain ⟨k, rfl⟩ := hPN hx
      by_cases hkn : k < n
      · exact Or.inl (Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hkn, rfl⟩, hx⟩)
      · have hne : k ≠ n := fun h => hnP (h ▸ hx)
        exact Or.inr ⟨hx, hν (lt_of_le_of_ne (Nat.le_of_not_gt hkn) (Ne.symm hne))⟩
  let Q : Set ℕ := insert (ν n) R
  have hQ : Q.Infinite := hR.mono (subset_insert _ _)
  have hmin : sInf Q = ν n := by
    apply le_antisymm
    · exact Nat.sInf_le (mem_insert _ _)
    · have hx := Nat.sInf_mem hQ.nonempty
      rcases hx with h | h
      · exact h ▸ le_rfl
      · exact h.2.le
  have htailQ : Q \ {sInf Q} = R := by
    ext x
    simp only [Q, hmin, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h | h, hne⟩
      · exact False.elim (hne h)
      · exact h
    · intro h
      refine ⟨Or.inr h, ?_⟩
      intro he
      have hlt : ν n < x := h.2
      rw [he] at hlt
      exact (Nat.lt_irrefl _) hlt
  have hg := hgood n F (Finset.filter_subset _ _) Q (by
    intro x hx
    rcases hx with h | h
    · exact h ▸ htail n n le_rfl
    · exact hRT h) hQ
  change ‖f ((F : Set ℕ) ∪ (Q \ {sInf Q})) (sInf Q)‖ < δ n at hg
  rw [htailQ, hmin, hFR] at hg
  exact hg

end SurveyStatements.P1
