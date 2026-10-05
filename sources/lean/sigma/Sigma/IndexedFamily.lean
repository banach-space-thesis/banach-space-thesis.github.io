import Sigma.ConstructedFamilies

/-! The two split pieces at every index give a bijective labelling of the
actual almost-disjoint family. This supplies the missing coordinate relabelling
between the construction's indices and the family atoms of its compactum. -/
noncomputable section
open Set
namespace SigmaNonprimarity

def splitPiece {I : Type} (J : I → Set ℕ) (b : I → Set Point) (q : I × Bool) : Set Point :=
  if q.2 then cylinder (J q.1) \ b q.1 else b q.1

theorem splitPiece_subset {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hs : ∀ i, Splits (J i) (b i)) (q : I × Bool) : splitPiece J b q ⊆ cylinder (J q.1) := by
  rcases q with ⟨i,bit⟩
  cases bit
  · exact (hs i).1
  · exact Set.diff_subset

theorem splitPiece_infinite {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hi : ∀ i, (J i).Infinite) (hs : ∀ i, Splits (J i) (b i)) (q : I × Bool) :
    (splitPiece J b q).Infinite := by
  rcases q with ⟨i,bit⟩
  cases bit
  · exact (hs i).infinite (hi i)
  · exact (hs i).other.infinite (hi i)

theorem splitPiece_pairwise {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hs : ∀ i, Splits (J i) (b i)) (hpair : Pairwise (fun i j => (J i ∩ J j).Finite)) :
    Pairwise (fun p q : I × Bool => (splitPiece J b p ∩ splitPiece J b q).Finite) := by
  intro p q hpq
  by_cases h : p.1 = q.1
  · rcases p with ⟨i,bit⟩
    rcases q with ⟨j,bit'⟩
    dsimp only at h
    subst j
    cases bit <;> cases bit' <;> simp_all [splitPiece]
  · exact (cylinder_finite (hpair h)).subset
      (Set.inter_subset_inter (splitPiece_subset J b hs p) (splitPiece_subset J b hs q))

theorem splitPiece_injective {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hi : ∀ i, (J i).Infinite) (hs : ∀ i, Splits (J i) (b i))
    (hpair : Pairwise (fun i j => (J i ∩ J j).Finite)) : Function.Injective (splitPiece J b) := by
  intro p q heq
  by_contra hpq
  have hf := splitPiece_pairwise J b hs hpair hpq
  dsimp only at hf
  rw [heq,Set.inter_self] at hf
  exact splitPiece_infinite J b hi hs q hf

theorem splitPiece_range {I : Type} (J : I → Set ℕ) (b : I → Set Point) :
    Set.range (splitPiece J b) = splitFamily J b := by
  ext A
  constructor
  · rintro ⟨⟨i,bit⟩,rfl⟩
    cases bit
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr ⟨i,rfl⟩
  · rintro (⟨i,rfl⟩ | ⟨i,rfl⟩)
    · exact ⟨(i,false),rfl⟩
    · exact ⟨(i,true),rfl⟩

def splitFamilyEquiv {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hi : ∀ i, (J i).Infinite) (hs : ∀ i, Splits (J i) (b i))
    (hpair : Pairwise (fun i j => (J i ∩ J j).Finite)) : (I × Bool) ≃ splitFamily J b :=
  (Equiv.ofInjective (splitPiece J b) (splitPiece_injective J b hi hs hpair)).trans
    (Equiv.setCongr (splitPiece_range J b))

@[simp] theorem splitFamilyEquiv_apply {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hi : ∀ i, (J i).Infinite) (hs : ∀ i, Splits (J i) (b i))
    (hpair : Pairwise (fun i j => (J i ∩ J j).Finite)) (q : I × Bool) :
    (splitFamilyEquiv J b hi hs hpair q).val = splitPiece J b q := rfl

end SigmaNonprimarity
