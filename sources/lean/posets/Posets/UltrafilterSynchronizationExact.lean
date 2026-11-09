import Posets.UltrafilterSynchronization

/-! Lemma 8.1 for any family of finite blocks satisfying the printed size
bound. The tagged sums make the blocks disjoint. We transport the synchronized
ultrafilters on the minimal blocks along embeddings that commute with every
selector. Lean index `k` represents the paper's positive index `k + 1`. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter
namespace Posets

abbrev ExactRowDomain (I : ℕ → Type*) := Σ k : ℕ, Fin (k + 1) ↪ I k
abbrev ExactColumnDomain (I : ℕ → Type*) := Σ k : ℕ, I k

def exactSelector {I : ℕ → Type*} (n : ℕ) (x : ExactRowDomain I) : ExactColumnDomain I :=
  ⟨x.1, x.2 (if h : n < x.1 + 1 then ⟨n, h⟩ else ⟨0, Nat.zero_lt_succ _⟩)⟩

def ExactSynchronized {I : ℕ → Type*}
    (U : Ultrafilter (ExactRowDomain I)) (V : Ultrafilter (ExactColumnDomain I)) : Prop :=
  (U : Filter (ExactRowDomain I)) ≤ cofinite ∧ (V : Filter (ExactColumnDomain I)) ≤ cofinite ∧
  (∀ n, Ultrafilter.map (exactSelector n) U = V) ∧
  ∀ n m, n ≠ m → {x | exactSelector n x = exactSelector m x} ∉ U

def Lemma_8_1_exact (I : ℕ → Type*) [∀ k, Finite (I k)] : Prop :=
  (∀ k, (k + 1) * 2 ^ (k + 1) ≤ Nat.card (I k)) → ∃ U V, ExactSynchronized (I := I) U V

/-- The selector preserves the block tag, so a point has a finite fibre. -/
theorem exactSelector_finite_fiber {I : ℕ → Type*} [∀ k, Finite (I k)]
    (n : ℕ) (y : ExactColumnDomain I) : (exactSelector n ⁻¹' {y}).Finite := by
  refine (Set.finite_range (@Sigma.mk ℕ (fun k => Fin (k + 1) ↪ I k) y.1)).subset ?_
  intro x hx
  have hk : x.1 = y.1 := congrArg Sigma.fst hx
  rcases x with ⟨k, e⟩
  dsimp only at hk
  subst k
  exact ⟨e, rfl⟩

private def exactRowEmbedding {I : ℕ → Type*} (e : ∀ k, Block k ↪ I k) :
    RowDomain ↪ ExactRowDomain I :=
  Function.Embedding.sigmaMap (Function.Embedding.refl ℕ) fun k =>
    ⟨fun r => r.trans (e k), by
      intro r s h
      apply Function.Embedding.ext
      intro i
      exact (e k).injective (congrArg (fun f : Fin (k + 1) ↪ I k => f i) h)⟩

private def exactColumnEmbedding {I : ℕ → Type*} (e : ∀ k, Block k ↪ I k) :
    ColumnDomain ↪ ExactColumnDomain I :=
  Function.Embedding.sigmaMap (Function.Embedding.refl ℕ) e

private theorem exactSelector_embedding {I : ℕ → Type*} (e : ∀ k, Block k ↪ I k)
    (n : ℕ) (x : RowDomain) :
    exactSelector n (exactRowEmbedding e x) = exactColumnEmbedding e (selector n x) := rfl

theorem lemma_8_1_exact_proof (I : ℕ → Type*) [∀ k, Finite (I k)] : Lemma_8_1_exact I := by
  intro hI
  let e (k : ℕ) : Block k ↪ I k := by
    letI : Fintype (I k) := Fintype.ofFinite (I k)
    apply Classical.choice
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Block, Fintype.card_fin, Nat.card_eq_fintype_card] using hI k
  obtain ⟨U, V, hU, hV, hpush, hdiff⟩ := lemma_8_1_proof
  refine ⟨Ultrafilter.map (exactRowEmbedding e) U, Ultrafilter.map (exactColumnEmbedding e) V,
    ?_, ?_, ?_, ?_⟩
  · exact (Filter.map_mono hU).trans (exactRowEmbedding e).injective.tendsto_cofinite
  · exact (Filter.map_mono hV).trans (exactColumnEmbedding e).injective.tendsto_cofinite
  · intro n
    rw [Ultrafilter.map_map]
    change Ultrafilter.map ((exactColumnEmbedding e) ∘ selector n) U = _
    rw [← Ultrafilter.map_map, hpush n]
  · intro n m hnm hbad
    rw [Ultrafilter.mem_map] at hbad
    apply hdiff n m hnm
    convert hbad using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, exactSelector_embedding,
      (exactColumnEmbedding e).injective.eq_iff]

end Posets
