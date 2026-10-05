import ThesisCommon.Analysis.BoundedScalarChargeVariation
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! Full-cardinality Rosenthal selection by finite descent through disjoint
annuli. The argument uses only infinite-cardinal multiplication, so includes
singular cardinals. The finite-descent mechanism follows the Kupka approach,
also presented in Drewnowski, Extracta Mathematicae 36 (2021), Theorem 2.1.
https://doi.org/10.17398/2605-5686.36.2.147
-/
noncomputable section
open Set
open scoped Cardinal BigOperators
namespace ThesisCommon
universe u
variable {Γ : Type u} [Infinite Γ]

/-- Any full-cardinality subset splits into a family of full-cardinality
pairwise disjoint subsets indexed by the original index set. -/
theorem fullCardinality_disjoint_family (A : Set Γ)
    (hA : Cardinal.mk A = Cardinal.mk Γ) :
    ∃ B : Γ → Set Γ, (∀ i, B i ⊆ A) ∧
      (∀ i, Cardinal.mk (B i) = Cardinal.mk Γ) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) := by
  classical
  have hc : Cardinal.mk (Γ × Γ) = Cardinal.mk A := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mul_eq_self
      (Cardinal.aleph0_le_mk Γ), hA]
  obtain ⟨e⟩ := Cardinal.eq.mp hc
  let B : Γ → Set Γ := fun i => Set.range (fun j => (e (i, j)).val)
  have hinj (i : Γ) : Function.Injective (fun j => (e (i, j)).val) := by
    intro j k h
    exact congrArg Prod.snd (e.injective (Subtype.ext h))
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i x hx
    obtain ⟨j, rfl⟩ := hx
    exact (e (i, j)).property
  · intro i
    exact Cardinal.mk_range_eq _ (hinj i)
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨k, rfl⟩ ⟨l, h⟩
    exact hij (congrArg Prod.fst (e.injective (Subtype.ext h))).symm

/-- A bounded family of nonnegative additive set functions has a large set
whose every large subset contains a row small on its relative complement.
Only the finite disjoint-family bound is needed for this intermediate step. -/
theorem exists_fullCardinality_small_complement
    (ν : Γ → Set Γ → ℝ) (M η : ℝ) (hη : 0 < η)
    (hbound : ∀ γ (n : ℕ) (B : Fin n → Set Γ),
      Pairwise (fun i j => Disjoint (B i) (B j)) → ∑ i, ν γ (B i) ≤ M) :
    ∃ A : Set Γ, Cardinal.mk A = Cardinal.mk Γ ∧
      ∀ B : Set Γ, B ⊆ A → Cardinal.mk B = Cardinal.mk Γ →
        ∃ γ ∈ B, ν γ (A \ B) < η := by
  classical
  by_contra hn
  push_neg at hn
  let S := {A : Set Γ // Cardinal.mk A = Cardinal.mk Γ}
  have hstep (A : S) :
      ∃ B : S, B.val ⊆ A.val ∧ ∀ γ ∈ B.val, η ≤ ν γ (A.val \ B.val) := by
    obtain ⟨B, hBA, hB, hv⟩ := hn A.val A.property
    exact ⟨⟨B, hB⟩, hBA, hv⟩
  choose f hf using hstep
  let D : ℕ → S := fun n => f^[n] ⟨Set.univ, Cardinal.mk_univ⟩
  have hsucc (n : ℕ) : D (n + 1) = f (D n) := by
    exact Function.iterate_succ_apply' f n _
  have hmono : Antitone (fun n => (D n).val) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [hsucc]
    exact (hf (D n)).1
  obtain ⟨N, hN⟩ := exists_nat_gt (M / η)
  have hN' : M < (N : ℝ) * η := (div_lt_iff₀ hη).mp hN
  obtain ⟨e⟩ := Cardinal.eq.mp (D N).property
  let γ : Γ := (e.symm (Classical.arbitrary Γ)).val
  have hγ : γ ∈ (D N).val := (e.symm (Classical.arbitrary Γ)).property
  let B : Fin N → Set Γ := fun i => (D i.val).val \ (D (i.val + 1)).val
  have hdis : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · apply Set.disjoint_left.mpr
      intro x hx hy
      exact hx.2 (hmono (Nat.succ_le_of_lt h) hy.1)
    · apply Set.disjoint_right.mpr
      intro x hx hy
      exact hx.2 (hmono (Nat.succ_le_of_lt h) hy.1)
  have hlo (i : Fin N) : η ≤ ν γ (B i) := by
    have hγi : γ ∈ (D (i.val + 1)).val := hmono i.isLt hγ
    have hh := (hf (D i.val)).2 γ
    simpa only [B, hsucc] using hh (by simpa only [hsucc] using hγi)
  have hsum : (N : ℝ) * η ≤ ∑ i, ν γ (B i) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlo i)
  linarith [hbound γ N B hdis]

/-- Rosenthal thinning for monotone set functions with vanishing diagonal
atoms and a uniform finite disjoint-family bound. -/
theorem rosenthal_fullCardinality_of_disjoint_bound
    (ν : Γ → Set Γ → ℝ) (M : ℝ)
    (hmono : ∀ γ, Monotone (ν γ))
    (hremove : ∀ γ A, ν γ (A \ {γ}) = ν γ A)
    (hbound : ∀ γ (n : ℕ) (B : Fin n → Set Γ),
      Pairwise (fun i j => Disjoint (B i) (B j)) → ∑ i, ν γ (B i) ≤ M)
    (η : ℝ) (hη : 0 < η) :
    ∃ A : Set Γ, Cardinal.mk A = Cardinal.mk Γ ∧ ∀ γ ∈ A, ν γ A < η := by
  classical
  obtain ⟨D, hD, hsmall⟩ := exists_fullCardinality_small_complement ν M η hη hbound
  obtain ⟨B, hBD, hcard, hdis⟩ := fullCardinality_disjoint_family D hD
  choose a ha hν using fun i => hsmall (B i) (hBD i) (hcard i)
  have hinj : Function.Injective a := by
    intro i j h
    by_contra hij
    exact Set.disjoint_left.mp (hdis hij) (ha i) (h ▸ ha j)
  refine ⟨Set.range a, Cardinal.mk_range_eq _ hinj, ?_⟩
  rintro γ ⟨i, rfl⟩
  rw [← hremove]
  apply lt_of_le_of_lt (hmono (a i) ?_) (hν i)
  rintro x ⟨⟨j, rfl⟩, hne⟩
  refine ⟨hBD j (ha j), ?_⟩
  intro hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hne (Set.mem_singleton _)
  exact Set.disjoint_left.mp (hdis hji) (ha j) hj

/-- Full Rosenthal selection for actual finitely additive scalar charges on
an arbitrary infinite index set, including singular-cardinal index sets. -/
theorem rosenthal_charge_selection {𝕜 : Type*} [RCLike 𝕜]
    (μ : Γ → BoundedScalarCharge 𝕜 Γ)
    (hμ : BoundedScalarCharge.UniformlyBounded μ)
    (hdiag : ∀ γ, μ γ {γ} = 0) (η : ℝ) (hη : 0 < η) :
    ∃ A : Set Γ, Cardinal.mk A = Cardinal.mk Γ ∧
      ∀ γ ∈ A, (μ γ).variation A < η := by
  obtain ⟨M, hM⟩ := hμ
  apply rosenthal_fullCardinality_of_disjoint_bound
    (fun γ => (μ γ).variation) M
  · intro γ A B hAB
    exact (μ γ).variation_mono hAB
  · intro γ A
    exact (μ γ).variation_sdiff_singleton (hdiag γ) A
  · intro γ n B hB
    exact ((μ γ).sum_variation_le B hB).trans (hM γ)
  · exact hη

end ThesisCommon
