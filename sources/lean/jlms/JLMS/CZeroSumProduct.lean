import JLMS.CZeroSum

/-!
# Distributing c₀ sums over coordinate products

The supremum norm of a family of pairs is the maximum of the two family
norms. This gives the distributive identity used in Kislyakov's absorption
arguments.
-/

noncomputable section
open Filter Topology
namespace JLMS.CZeroSum
universe u v v' w
variable {𝕜 : Type w} [RCLike 𝕜] {I : Type u} {E : I → Type v} {F : I → Type v'}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

def fst (x : CZeroSum 𝕜 (fun i => E i × F i)) : CZeroSum 𝕜 E :=
  CZeroSum.mk (fun i => (x i).1) (squeeze_zero (fun i => norm_nonneg _)
    (fun i => norm_fst_le (x i)) x.tendsto_norm)

def snd (x : CZeroSum 𝕜 (fun i => E i × F i)) : CZeroSum 𝕜 F :=
  CZeroSum.mk (fun i => (x i).2) (squeeze_zero (fun i => norm_nonneg _)
    (fun i => norm_snd_le (x i)) x.tendsto_norm)

def pair (x : CZeroSum 𝕜 E) (y : CZeroSum 𝕜 F) : CZeroSum 𝕜 (fun i => E i × F i) :=
  CZeroSum.mk (fun i => (x i, y i)) (by
    simpa only [Prod.norm_def, max_self] using x.tendsto_norm.max y.tendsto_norm)

@[simp] theorem fst_apply (x : CZeroSum 𝕜 (fun i => E i × F i)) (i : I) : fst x i = (x i).1 := rfl
@[simp] theorem snd_apply (x : CZeroSum 𝕜 (fun i => E i × F i)) (i : I) : snd x i = (x i).2 := rfl
@[simp] theorem pair_apply (x : CZeroSum 𝕜 E) (y : CZeroSum 𝕜 F) (i : I) : pair x y i = (x i, y i) := rfl

theorem norm_fst_le (x : CZeroSum 𝕜 (fun i => E i × F i)) : ‖fst x‖ ≤ ‖x‖ :=
  norm_le (norm_nonneg x) (fun i => (_root_.norm_fst_le (x i)).trans (x.norm_apply_le_norm i))

theorem norm_snd_le (x : CZeroSum 𝕜 (fun i => E i × F i)) : ‖snd x‖ ≤ ‖x‖ :=
  norm_le (norm_nonneg x) (fun i => (_root_.norm_snd_le (x i)).trans (x.norm_apply_le_norm i))

def productIsometry : CZeroSum 𝕜 (fun i => E i × F i) ≃ₗᵢ[𝕜]
    CZeroSum 𝕜 E × CZeroSum 𝕜 F where
  toFun x := (fst x, snd x)
  invFun p := pair p.1 p.2
  left_inv x := by ext i <;> rfl
  right_inv p := by apply Prod.ext <;> ext i <;> rfl
  map_add' x y := by apply Prod.ext <;> ext i <;> rfl
  map_smul' c x := by apply Prod.ext <;> ext i <;> rfl
  norm_map' x := by
    rw [Prod.norm_def]
    apply le_antisymm (max_le (norm_fst_le x) (norm_snd_le x))
    apply norm_le (le_trans (norm_nonneg _) (le_max_left _ _))
    intro i
    change max ‖(x i).1‖ ‖(x i).2‖ ≤ max ‖fst x‖ ‖snd x‖
    exact max_le_max ((fst x).norm_apply_le_norm i) ((snd x).norm_apply_le_norm i)

end JLMS.CZeroSum
