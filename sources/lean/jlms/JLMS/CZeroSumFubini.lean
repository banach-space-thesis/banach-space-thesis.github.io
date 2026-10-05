import JLMS.CZeroSumEquiv

/-!
# Fubini identities for Banach c₀ sums

Kislyakov Lemma 1.2 identifies an iterated c₀ sum with the sum indexed by
the product, and hence permits interchange of the two index sets. The key
finite-level argument is proved explicitly for the concrete Banach sums.
-/

noncomputable section
open Filter Topology
namespace JLMS.CZeroSum
universe u u' v w
variable {𝕜 : Type w} [RCLike 𝕜] {I : Type u} {J : Type u'}
  {E : I → J → Type v} [∀ i j, NormedAddCommGroup (E i j)]
  [∀ i j, NormedSpace 𝕜 (E i j)]

def flatten (x : CZeroSum 𝕜 (fun i => CZeroSum 𝕜 (E i))) :
    CZeroSum 𝕜 (fun p : I × J => E p.1 p.2) := by
  apply CZeroSum.mk (𝕜 := 𝕜) (fun p : I × J => x p.1 p.2)
  apply (tendsto_norm_cofinite_iff_finite _).mpr
  intro ε hε
  have hfinite : Set.Finite (⋃ i ∈ {i | ε ≤ ‖x i‖},
      (Prod.mk i) '' {j | ε ≤ ‖x i j‖}) :=
    (x.finite_norm_ge hε).biUnion fun i _ => ((x i).finite_norm_ge hε).image (Prod.mk i)
  apply hfinite.subset
  intro p hp
  apply Set.mem_iUnion_of_mem p.1
  apply Set.mem_iUnion_of_mem (hp.trans ((x p.1).norm_apply_le_norm p.2))
  exact ⟨p.2, hp, rfl⟩

@[simp] theorem flatten_apply (x : CZeroSum 𝕜 (fun i => CZeroSum 𝕜 (E i))) (i : I) (j : J) :
    flatten x (i, j) = x i j := rfl

def row (x : CZeroSum 𝕜 (fun p : I × J => E p.1 p.2)) (i : I) : CZeroSum 𝕜 (E i) :=
  comap (Prod.mk i) (fun _ _ h => congrArg Prod.snd h) x

@[simp] theorem row_apply (x : CZeroSum 𝕜 (fun p : I × J => E p.1 p.2)) (i : I) (j : J) :
    row x i j = x (i, j) := rfl

def unflatten (x : CZeroSum 𝕜 (fun p : I × J => E p.1 p.2)) :
    CZeroSum 𝕜 (fun i => CZeroSum 𝕜 (E i)) := by
  apply CZeroSum.mk (row x)
  apply (tendsto_norm_cofinite_iff_finite _).mpr
  intro ε hε
  apply ((x.finite_norm_ge (half_pos hε)).image Prod.fst).subset
  intro i hi
  have hex : ∃ j, ε / 2 ≤ ‖x (i, j)‖ := by
    by_contra h
    push_neg at h
    have hnorm : ‖row x i‖ ≤ ε / 2 := norm_le (half_pos hε).le (fun j => (h j).le)
    exact (half_lt_self hε).not_ge (hi.trans hnorm)
  obtain ⟨j, hj⟩ := hex
  exact ⟨(i, j), hj, rfl⟩

@[simp] theorem unflatten_apply (x : CZeroSum 𝕜 (fun p : I × J => E p.1 p.2)) (i : I) (j : J) :
    unflatten x i j = x (i, j) := rfl

/-- Flattening preserves the supremum norm exactly. -/
def prodIsometry : CZeroSum 𝕜 (fun i => CZeroSum 𝕜 (E i)) ≃ₗᵢ[𝕜]
    CZeroSum 𝕜 (fun p : I × J => E p.1 p.2) where
  toFun := flatten
  invFun := unflatten
  left_inv x := by apply CZeroSum.ext; intro i; apply CZeroSum.ext; intro j; rfl
  right_inv x := by apply CZeroSum.ext; intro p; rfl
  map_add' x y := by apply CZeroSum.ext; intro p; rfl
  map_smul' c x := by apply CZeroSum.ext; intro p; rfl
  norm_map' x := by
    apply le_antisymm
    · apply norm_le (norm_nonneg x)
      intro p
      exact ((x p.1).norm_apply_le_norm p.2).trans (x.norm_apply_le_norm p.1)
    · apply norm_le (norm_nonneg _)
      intro i
      apply norm_le (norm_nonneg _)
      intro j
      exact (flatten x).norm_apply_le_norm (i, j)

@[simp] theorem prodIsometry_apply (x : CZeroSum 𝕜 (fun i => CZeroSum 𝕜 (E i))) (i : I) (j : J) :
    prodIsometry (𝕜 := 𝕜) (E := E) x (i, j) = x i j := rfl

/-- The two iterated sums can be interchanged (Kislyakov Lemma 1.2). -/
def commuteIsometry : CZeroSum 𝕜 (fun i => CZeroSum 𝕜 (E i)) ≃ₗᵢ[𝕜]
    CZeroSum 𝕜 (fun j => CZeroSum 𝕜 (fun i => E i j)) :=
  (prodIsometry (𝕜 := 𝕜) (E := E)).trans
    ((reindex (𝕜 := 𝕜) (E := fun p : I × J => E p.1 p.2) (Equiv.prodComm J I)).trans
      (prodIsometry (𝕜 := 𝕜) (E := fun j i => E i j)).symm)

end JLMS.CZeroSum
