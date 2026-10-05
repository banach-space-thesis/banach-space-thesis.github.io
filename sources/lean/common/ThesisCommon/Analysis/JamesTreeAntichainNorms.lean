import ThesisCommon.Analysis.FinitePiLpRestriction
import ThesisCommon.Analysis.JamesTreeCoordinates

/-! Exact finite antichain norms for the actual tree spaces. Every allowed
segment is required to be a chain; both explicit conventions satisfy this.
No unconditionality of the full tree basis is assumed. -/
noncomputable section
open scoped BigOperators ENNReal
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def IsTreeAntichainEmbedding {ι : Type*} (e : ι ↪ DyadicTreeNode) : Prop :=
  ∀ i j, i ≠ j → ¬ (e i).IsPrefix (e j)

def JamesTreeSegmentsAreChains (S : JamesTreeSegmentFamily) : Prop :=
  ∀ A, S.allows A → IsLiteralTreeSegment A

theorem literalJamesTreeSegmentsAreChains :
    JamesTreeSegmentsAreChains literalTreeSegmentFamily := fun _ h => h

theorem consecutiveJamesTreeSegmentsAreChains :
    JamesTreeSegmentsAreChains consecutiveTreeSegmentFamily := fun _ h => h.1

namespace JamesTreePreSpace

def antichainInsertLinear {n : ℕ} (e : Fin n ↪ DyadicTreeNode) :
    PiLp p.val (fun _ : Fin n => 𝕜) →ₗ[𝕜] JamesTreePreSpace 𝕜 p S where
  toFun a := ∑ i, single (e i) (a i)
  map_add' a b := by
    change (∑ i, Finsupp.single (e i) (a i + b i)) =
      (∑ i, Finsupp.single (e i) (a i)) + ∑ i, Finsupp.single (e i) (b i)
    simp only [Finsupp.single_add, Finset.sum_add_distrib]
  map_smul' c a := by
    change (∑ i, Finsupp.single (e i) (c • a i)) =
      c • ∑ i, Finsupp.single (e i) (a i)
    simp only [Finset.smul_sum, Finsupp.smul_single]

theorem antichainInsertLinear_apply {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (a : PiLp p.val (fun _ : Fin n => 𝕜)) (t : DyadicTreeNode) :
    antichainInsertLinear (S := S) e a t = ∑ i, if e i = t then a i else 0 := by
  change (∑ i, Finsupp.single (e i) (a i)) t = _
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]

@[simp] theorem antichainInsertLinear_apply_image {n : ℕ}
    (e : Fin n ↪ DyadicTreeNode) (a : PiLp p.val (fun _ : Fin n => 𝕜)) (i : Fin n) :
    antichainInsertLinear (S := S) e a (e i) = a i := by
  rw [antichainInsertLinear_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  simp

theorem antichainInsertLinear_test_apply {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (a : PiLp p.val (fun _ : Fin n => 𝕜)) (T : JamesTreeTest S) (j : Fin T.count) :
    jamesTreeTestMap 𝕜 p T (coefficients (antichainInsertLinear (S := S) e a)) j =
      ∑ i, if e i ∈ T.segment j then a i else 0 := by
  change (∑ t ∈ T.segment j, (antichainInsertLinear (S := S) e a) t) = _
  simp only [antichainInsertLinear_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [eq_comm]

theorem norm_antichainInsertLinear {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S)
    (a : PiLp p.val (fun _ : Fin n => 𝕜)) :
    ‖antichainInsertLinear (S := S) e a‖ = ‖a‖ := by
  classical
  apply le_antisymm
  · apply norm_le
    intro T
    have huniq (j : Fin T.count) (i k : Fin n)
        (hi : e i ∈ T.segment j) (hk : e k ∈ T.segment j) : i = k := by
      by_contra hik
      rcases (hS _ (T.allowed j)).2 _ hi _ hk with h | h
      · exact he i k hik h
      · exact he k i (Ne.symm hik) h
    let I := {j : Fin T.count // ∃ i, e i ∈ T.segment j}
    let q : I ↪ Fin n := {
      toFun := fun j => Classical.choose j.property
      inj' := by
        intro j k hjk
        apply Subtype.ext
        by_contra hjkne
        have hj := Classical.choose_spec j.property
        have hk := Classical.choose_spec k.property
        dsimp only at hjk
        rw [← hjk] at hk
        exact Finset.disjoint_left.mp (T.disjoint hjkne) hj hk }
    let inc : I ↪ Fin T.count := ⟨Subtype.val, Subtype.val_injective⟩
    have hq (j : I) : e (q j) ∈ T.segment j.val := Classical.choose_spec j.property
    have hnorm := piLp_norm_eq_of_zero_off_embedding p inc
      (WithLp.toLp p.val (fun j : I => a (q j)))
      (jamesTreeTestMap 𝕜 p T (coefficients (antichainInsertLinear (S := S) e a)))
      (fun j => by
        rw [antichainInsertLinear_test_apply]
        change a (q j) = ∑ i, if e i ∈ T.segment j.val then a i else 0
        rw [Finset.sum_eq_single (q j)]
        · rw [if_pos (hq j)]
        · intro i _ hi
          exact if_neg (fun hit => hi (huniq j.val i (q j) hit (hq j)))
        · simp)
      (fun j hj => by
        rw [antichainInsertLinear_test_apply]
        apply Finset.sum_eq_zero
        intro i _
        exact if_neg (fun hi => hj ⟨⟨j, ⟨i, hi⟩⟩, rfl⟩))
    rw [← hnorm]
    exact piLp_norm_restrict_embedding_le p q a
  · let T : JamesTreeTest S := {
      count := n
      segment := fun i => {e i}
      allowed := fun i => S.singleton_allowed (e i)
      disjoint := by
        intro i j hij
        exact Finset.disjoint_singleton.mpr (e.injective.ne hij) }
    have htest : jamesTreeTestMap 𝕜 p T
        (coefficients (antichainInsertLinear (S := S) e a)) = a := by
      ext i
      change (∑ t ∈ ({e i} : Finset DyadicTreeNode),
        antichainInsertLinear (S := S) e a t) = a i
      simp only [Finset.sum_singleton, antichainInsertLinear_apply_image]
    simpa only [htest] using (antichainInsertLinear (S := S) e a).test_norm_le T

def antichainInsertIsometry {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S) :
    PiLp p.val (fun _ : Fin n => 𝕜) →ₗᵢ[𝕜] JamesTreePreSpace 𝕜 p S :=
  ⟨antichainInsertLinear e, norm_antichainInsertLinear e he hS⟩

end JamesTreePreSpace
end ThesisCommon
