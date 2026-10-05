import Posets.OrdinalIdealTransportCofinalMaps

/-! Isometric coordinate maps and coordinate insertion on actual c₀ sums. -/
noncomputable section
open Set Filter Topology
namespace Posets
universe u v w
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

def cZeroSum_mapIsometry {I : Type u} {E : I → Type v} {F : I → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    (V : ∀ i, E i →ₗᵢ[𝕜] F i) : JLMS.CZeroSum 𝕜 E →ₗᵢ[𝕜] JLMS.CZeroSum 𝕜 F where
  toFun x := JLMS.CZeroSum.mk (fun i => V i (x i))
    (by simpa only [LinearIsometry.norm_map] using x.tendsto_norm)
  map_add' x y := by apply JLMS.CZeroSum.ext; intro i; exact (V i).map_add _ _
  map_smul' a x := by apply JLMS.CZeroSum.ext; intro i; exact (V i).map_smul a _
  norm_map' x := by
    apply le_antisymm
    · apply JLMS.CZeroSum.norm_le (norm_nonneg x)
      intro i
      change ‖V i (x i)‖ ≤ ‖x‖
      rw [(V i).norm_map]
      exact x.norm_apply_le_norm i
    · apply JLMS.CZeroSum.norm_le (norm_nonneg _)
      intro i
      have h := (JLMS.CZeroSum.mk (𝕜 := 𝕜) (fun i => V i (x i))
        (by simpa only [LinearIsometry.norm_map] using x.tendsto_norm)).norm_apply_le_norm i
      change ‖V i (x i)‖ ≤ _ at h
      rwa [(V i).norm_map] at h

def cZeroSum_insertIsometry {I J : Type u} {E : J → Type v}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
    (k : I → J) (hk : Function.Injective k) :
    JLMS.CZeroSum 𝕜 (fun i => E (k i)) →ₗᵢ[𝕜] JLMS.CZeroSum 𝕜 E where
  __ := (cZeroSum_insertCLM (𝕜 := 𝕜) (E := E) k hk).toLinearMap
  norm_map' x := by
    apply le_antisymm
    · exact ((cZeroSum_insertCLM (𝕜 := 𝕜) (E := E) k hk).le_opNorm x).trans
        (by simpa using mul_le_mul_of_nonneg_right (norm_cZeroSum_insertCLM_le (E := E) k hk) (norm_nonneg x))
    · apply JLMS.CZeroSum.norm_le (norm_nonneg _)
      intro i
      rw [← cZeroSum_insertCLM_apply_selected (E := E) k hk x i]
      exact (cZeroSum_insertCLM (𝕜 := 𝕜) (E := E) k hk x).norm_apply_le_norm (k i)

/-- A distinct sufficiently high target coordinate can be assigned to every
member of any prescribed countable family of lower ordinal exponents. -/
theorem exists_strictMono_cofinal_block_selection {γ : Ordinal.{0}}
    (β δ : ℕ → Ordinal.{0}) (hβ : Monotone β)
    (hcof : ∀ α < γ, ∃ n, α ≤ β n) (hδ : ∀ n, δ n < γ) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ n, δ n ≤ β (k n) := by
  classical
  choose s hs using fun n => hcof (δ n) (hδ n)
  let k : ℕ → ℕ := Nat.rec (s 0) (fun n prev => max (prev + 1) (s (n + 1)))
  refine ⟨k, strictMono_nat_of_lt_succ (fun n => ?_), ?_⟩
  · exact (Nat.lt_succ_self (k n)).trans_le (le_max_left _ _)
  · intro n
    apply (hs n).trans (hβ ?_)
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_right _ _

end Posets
