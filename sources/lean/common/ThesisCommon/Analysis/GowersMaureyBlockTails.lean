import ThesisCommon.Analysis.GowersMaureySmallIntervalVectors

/-! Actual tails of infinite block sequences supply small interval-norm
vectors after any prescribed coordinate cutoff. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def afterCutoff (K : ℕ) : Submodule ℝ (C00 𝕜) where
  carrier := {x | ∀ n, n ≤ K → x n = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy n hn; simp [hx n hn, hy n hn]
  smul_mem' := by intro c x hx n hn; simp [hx n hn]

theorem block_index_le_support (u : ℕ → C00 𝕜)
    (hu : ∀ i j, i < j → Before (u i) (u j)) (hne : ∀ i, u i ≠ 0) :
    ∀ i n, n ∈ (u i).support → i ≤ n := by
  intro i
  induction i with
  | zero => intros; omega
  | succ i ih =>
    intro n hn
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr (hne i)
    have hsi := ih s hs
    have hsn := hu i (i + 1) (Nat.lt_succ_self i) s hs n hn
    omega

theorem block_tail_mem_afterCutoff (u : ℕ → C00 𝕜)
    (hu : ∀ i j, i < j → Before (u i) (u j)) (hne : ∀ i, u i ≠ 0)
    (K i : ℕ) : u (K + 1 + i) ∈ afterCutoff K := by
  intro n hn
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  have hh := block_index_le_support u hu hne (K + 1 + i) n hmem
  omega

theorem exists_small_interval_vector_after (D : ConstructionData 𝕜)
    (Y : Submodule ℝ (C00 𝕜)) (u : ℕ → C00 𝕜)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hY : ∀ i, u i ∈ Y) (hne : ∀ i, u i ≠ 0)
    (K N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Y, x ∈ afterCutoff K ∧ implicitNorm D x = (1 + ε)⁻¹ ∧
      intervalNorm D N x ≤ 1 := by
  obtain ⟨x, hx, hnorm, hsmall⟩ := exists_vector_intervalNorm_le_one D
    (Y ⊓ afterCutoff K) (fun i => u (K + 1 + i))
    (fun i j hij => hu _ _ (by omega))
    (fun i => ⟨hY _, block_tail_mem_afterCutoff u hu hne K i⟩)
    (fun i => hne _) N hε
  exact ⟨x, hx.1, hx.2, hnorm, hsmall⟩

theorem before_of_mem_afterCutoff {x y : C00 𝕜} {K : ℕ}
    (hx : ∀ n ∈ x.support, n ≤ K) (hy : y ∈ afterCutoff K) : Before x y := by
  intro s hs t ht
  have ht' : K < t := by
    by_contra hh
    exact Finsupp.mem_support_iff.mp ht (hy t (by omega))
  exact (hx s hs).trans_lt ht'

end ThesisCommon.GowersMaurey
