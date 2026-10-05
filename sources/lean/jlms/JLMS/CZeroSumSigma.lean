import JLMS.CZeroSumEquiv

/-!
# Dependent Fubini theorem for Banach c₀ sums

The inner index sets may vary with the outer index. This form is useful for
Kislyakov's singular-cardinal argument, where different cofinal blocks have
different cardinalities.
-/

noncomputable section
open Filter Topology
namespace JLMS.CZeroSum
universe u u' v w
variable {𝕜 : Type w} [RCLike 𝕜] {I : Type u} {J : I → Type u'}
  {E : (i : I) → J i → Type v} [∀ i j, NormedAddCommGroup (E i j)]
  [∀ i j, NormedSpace 𝕜 (E i j)]

def sigmaFlatten (x : CZeroSum 𝕜 (fun i => CZeroSum 𝕜 (E i))) :
    CZeroSum 𝕜 (fun p : Sigma J => E p.1 p.2) := by
  apply CZeroSum.mk (𝕜 := 𝕜) (fun p : Sigma J => x p.1 p.2)
  apply (tendsto_norm_cofinite_iff_finite _).mpr
  intro ε hε
  have hfinite : Set.Finite (⋃ i ∈ {i | ε ≤ ‖x i‖},
      (Sigma.mk i) '' {j | ε ≤ ‖x i j‖}) :=
    (x.finite_norm_ge hε).biUnion fun i _ => ((x i).finite_norm_ge hε).image (Sigma.mk i)
  apply hfinite.subset
  intro p hp
  apply Set.mem_iUnion_of_mem p.1
  apply Set.mem_iUnion_of_mem (hp.trans ((x p.1).norm_apply_le_norm p.2))
  exact ⟨p.2, hp, rfl⟩

@[simp] theorem sigmaFlatten_apply (x : CZeroSum 𝕜 (fun i => CZeroSum 𝕜 (E i)))
    (i : I) (j : J i) : sigmaFlatten x ⟨i, j⟩ = x i j := rfl

def sigmaRow (x : CZeroSum 𝕜 (fun p : Sigma J => E p.1 p.2)) (i : I) : CZeroSum 𝕜 (E i) :=
  comap (Sigma.mk i) sigma_mk_injective x

@[simp] theorem sigmaRow_apply (x : CZeroSum 𝕜 (fun p : Sigma J => E p.1 p.2))
    (i : I) (j : J i) : sigmaRow x i j = x ⟨i, j⟩ := rfl

def sigmaUnflatten (x : CZeroSum 𝕜 (fun p : Sigma J => E p.1 p.2)) :
    CZeroSum 𝕜 (fun i => CZeroSum 𝕜 (E i)) := by
  apply CZeroSum.mk (sigmaRow x)
  apply (tendsto_norm_cofinite_iff_finite _).mpr
  intro ε hε
  apply ((x.finite_norm_ge (half_pos hε)).image Sigma.fst).subset
  intro i hi
  have hex : ∃ j : J i, ε / 2 ≤ ‖x ⟨i, j⟩‖ := by
    by_contra h
    push_neg at h
    have hnorm : ‖sigmaRow x i‖ ≤ ε / 2 := norm_le (half_pos hε).le (fun j => (h j).le)
    exact (half_lt_self hε).not_ge (hi.trans hnorm)
  obtain ⟨j, hj⟩ := hex
  exact ⟨⟨i, j⟩, hj, rfl⟩

@[simp] theorem sigmaUnflatten_apply (x : CZeroSum 𝕜 (fun p : Sigma J => E p.1 p.2))
    (i : I) (j : J i) : sigmaUnflatten x i j = x ⟨i, j⟩ := rfl

/-- Flattening dependent c₀ sums is a linear isometry onto the sigma-indexed sum. -/
def sigmaIsometry : CZeroSum 𝕜 (fun i => CZeroSum 𝕜 (E i)) ≃ₗᵢ[𝕜]
    CZeroSum 𝕜 (fun p : Sigma J => E p.1 p.2) where
  toFun := sigmaFlatten
  invFun := sigmaUnflatten
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
      exact (sigmaFlatten x).norm_apply_le_norm ⟨i, j⟩

@[simp] theorem sigmaIsometry_apply (x : CZeroSum 𝕜 (fun i => CZeroSum 𝕜 (E i)))
    (i : I) (j : J i) : sigmaIsometry (𝕜 := 𝕜) (E := E) x ⟨i, j⟩ = x i j := rfl

end JLMS.CZeroSum
