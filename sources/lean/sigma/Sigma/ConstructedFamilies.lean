import Sigma.TransfiniteConstruction
import Sigma.Splitting

/-! The recursion gives actual infinite almost-disjoint split families, and
therefore the compacta and JL spaces used in the analytic part of the paper. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

theorem exists_continuum_stock : ∃ R : ConstructionIndex → Set ℕ,
    (∀ i, (R i).Infinite) ∧ Pairwise (fun i j => (R i ∩ R j).Finite) := by
  obtain ⟨S,hcard,hS,hpair⟩ := continuum_almostDisjoint_subsets Set.univ Set.infinite_univ
  obtain ⟨e⟩ := Cardinal.eq.mp (constructionIndex_cardinal.trans hcard.symm)
  refine ⟨fun i => (e i).val, fun i => (hS _ (e i).property).2, ?_⟩
  intro i j hij
  exact hpair (e i).property (e j).property (fun h => hij (e.injective (Subtype.ext h)))

theorem Splits.other {A : Set ℕ} {Z : Set Point} (h : Splits A Z) :
    Splits A (cylinder A \ Z) := by
  refine ⟨Set.diff_subset, ?_⟩
  intro n hn
  have hfalse : (n,false) ∈ cylinder A := hn
  have htrue : (n,true) ∈ cylinder A := hn
  simp only [Set.mem_diff, hfalse, htrue, true_and, not_not]
  exact (not_congr (h.2 n hn)).trans not_not

theorem Splits.infinite {A : Set ℕ} {Z : Set Point} (h : Splits A Z) (hA : A.Infinite) : Z.Infinite := by
  have hcover : A ⊆ Prod.fst '' Z := by
    intro n hn
    by_cases hf : (n,false) ∈ Z
    · exact ⟨(n,false),hf,rfl⟩
    · have ht : (n,true) ∈ Z := by
        by_contra ht
        exact hf ((h.2 n hn).mpr ht)
      exact ⟨(n,true),ht,rfl⟩
  intro hZ
  exact hA ((hZ.image Prod.fst).subset hcover)

theorem splitFamily_almostDisjoint {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hinf : ∀ i, (J i).Infinite) (hsplit : ∀ i, Splits (J i) (b i))
    (hpair : Pairwise (fun i j => (J i ∩ J j).Finite)) : AlmostDisjoint (splitFamily J b) := by
  have hcc (i j : I) (hij : i ≠ j) : (cylinder (J i) ∩ cylinder (J j)).Finite := by
    exact cylinder_finite (hpair hij)
  have hbb (i j : I) (hij : i ≠ j) : (b i ∩ b j).Finite :=
    (hcc i j hij).subset (Set.inter_subset_inter (hsplit i).1 (hsplit j).1)
  have hbo (i j : I) : (b i ∩ (cylinder (J j) \ b j)).Finite := by
    by_cases hij : i = j
    · subst j
      have heq : b i ∩ (cylinder (J i) \ b i) = ∅ := by ext x; simp
      rw [heq]
      exact Set.finite_empty
    · exact (hcc i j hij).subset (Set.inter_subset_inter (hsplit i).1 Set.diff_subset)
  have hoo (i j : I) (hij : i ≠ j) :
      ((cylinder (J i) \ b i) ∩ (cylinder (J j) \ b j)).Finite :=
    (hcc i j hij).subset (Set.inter_subset_inter Set.diff_subset Set.diff_subset)
  constructor
  · rintro A (⟨i,rfl⟩ | ⟨i,rfl⟩)
    · exact (hsplit i).infinite (hinf i)
    · exact (hsplit i).other.infinite (hinf i)
  · rintro A (⟨i,rfl⟩ | ⟨i,rfl⟩) D (⟨j,rfl⟩ | ⟨j,rfl⟩) hAD
    · exact hbb i j (fun h => hAD (h ▸ rfl))
    · exact hbo i j
    · simpa only [Set.inter_comm] using hbo j i
    · exact hoo i j (fun h => hAD (h ▸ rfl))

theorem splitFamily_infinite {I : Type} [Infinite I] (J : I → Set ℕ) (b : I → Set Point)
    (hinf : ∀ i, (J i).Infinite) (hsplit : ∀ i, Splits (J i) (b i))
    (hpair : Pairwise (fun i j => (J i ∩ J j).Finite)) : (splitFamily J b).Infinite := by
  have hbinj : Function.Injective b := by
    intro i j heq
    by_contra hij
    have hf : (b i ∩ b j).Finite := (cylinder_finite (hpair hij)).subset
      (Set.inter_subset_inter (hsplit i).1 (hsplit j).1)
    rw [← heq, Set.inter_self] at hf
    exact (hsplit i).infinite (hinf i) hf
  exact (Set.infinite_range_of_injective hbinj).mono Set.subset_union_left

theorem threeLevelChoice_family_properties {I : Type} [Infinite I]
    (μ : I → AtomicRows) (R : I → Set ℕ) (d : ∀ i, ThreeLevelChoice (μ i) (R i))
    (hpair : Pairwise (fun i j => (R i ∩ R j).Finite)) :
    AlmostDisjoint (splitFamily (fun i => (d i).J₁) (fun i => (d i).Z)) ∧
      (splitFamily (fun i => (d i).J₁) (fun i => (d i).Z)).Infinite := by
  have hinf (i : I) : (d i).J₁.Infinite := (d i).infinite_J₂.mono (d i).J₂_subset
  have hsub (i : I) : (d i).J₁ ⊆ R i := (d i).J₁_subset.trans (d i).J₀_subset
  have hJ : Pairwise (fun i j => ((d i).J₁ ∩ (d j).J₁).Finite) := by
    intro i j hij
    exact (hpair hij).subset (Set.inter_subset_inter (hsub i) (hsub j))
  exact ⟨splitFamily_almostDisjoint _ _ hinf (fun i => (d i).splits) hJ,
    splitFamily_infinite _ _ hinf (fun i => (d i).splits) hJ⟩

theorem exists_almostDisjoint_construction
    (μ μtilde : ConstructionIndex → AtomicRows) (ρ σ : ConstructionIndex → ℕ → PairedMeasure)
    (hμ : ∀ a, Admissible (μ a)) (hμt : ∀ a, Admissible (μtilde a)) :
    ∃ (R : ConstructionIndex → Set ℕ) (d : ConstructionData μ μtilde R R),
      GoodConstruction ρ σ d Set.univ ∧
      (AlmostDisjoint (splitFamily (fun i => (d i).1.J₁) (fun i => (d i).1.Z)) ∧
        (splitFamily (fun i => (d i).1.J₁) (fun i => (d i).1.Z)).Infinite) ∧
      (AlmostDisjoint (splitFamily (fun i => (d i).2.J₁) (fun i => (d i).2.Z)) ∧
        (splitFamily (fun i => (d i).2.J₁) (fun i => (d i).2.Z)).Infinite) := by
  haveI : Infinite ConstructionIndex := Cardinal.infinite_iff.mpr (by
    rw [constructionIndex_cardinal]
    exact Cardinal.aleph0_le_continuum)
  obtain ⟨R,hR,hpair⟩ := exists_continuum_stock
  obtain ⟨d,hd,_⟩ := exists_continuum_construction μ μtilde R R ρ σ hμ hμt hR hR
  exact ⟨R,d,hd, threeLevelChoice_family_properties μ R (fun i => (d i).1) hpair,
    threeLevelChoice_family_properties μtilde R (fun i => (d i).2) hpair⟩

end SigmaNonprimarity
