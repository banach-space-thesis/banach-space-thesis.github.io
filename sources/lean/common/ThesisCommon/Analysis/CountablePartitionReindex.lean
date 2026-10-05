import ThesisCommon.Analysis.CountableBlockIsometries

/-! A nonempty countable partition becomes a coordinate partition after
each block has been paired with the natural numbers. -/
noncomputable section
namespace ThesisCommon
variable {Γ ι : Type*}

def partitionPairMap (B : ι → Set Γ) (φ : ∀ i, B i × ℕ ≃ ℕ) :
    ι × ℕ → Γ × ℕ := fun z => ((φ z.1).symm z.2).1.val |> fun γ =>
      (γ, ((φ z.1).symm z.2).2)

theorem partitionPairMap_injective (B : ι → Set Γ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (φ : ∀ i, B i × ℕ ≃ ℕ) :
    Function.Injective (partitionPairMap B φ) := by
  rintro ⟨i, n⟩ ⟨j, m⟩ h
  have hfst : ((φ i).symm n).1.val = ((φ j).symm m).1.val := congrArg Prod.fst h
  have hsnd : ((φ i).symm n).2 = ((φ j).symm m).2 := congrArg Prod.snd h
  have hij : i = j := by
    by_contra hne
    exact Set.disjoint_left.mp (hB hne) (((φ i).symm n).1.property)
      (hfst ▸ (((φ j).symm m).1.property))
  subst j
  have hpair : (φ i).symm n = (φ i).symm m := by
    apply Prod.ext
    · exact Subtype.ext hfst
    · exact hsnd
  exact Prod.ext rfl ((φ i).symm.injective hpair)

theorem partitionPairMap_surjective (B : ι → Set Γ)
    (hcover : (⋃ i, B i) = Set.univ) (φ : ∀ i, B i × ℕ ≃ ℕ) :
    Function.Surjective (partitionPairMap B φ) := by
  rintro ⟨γ, n⟩
  have hγ : γ ∈ ⋃ i, B i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hγ
  refine ⟨(i, φ i (⟨γ, hi⟩, n)), ?_⟩
  simp only [partitionPairMap, Equiv.symm_apply_apply]

def partitionPairEquiv (B : ι → Set Γ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcover : (⋃ i, B i) = Set.univ) (φ : ∀ i, B i × ℕ ≃ ℕ) :
    ι × ℕ ≃ Γ × ℕ :=
  Equiv.ofBijective (partitionPairMap B φ)
    ⟨partitionPairMap_injective B hB φ, partitionPairMap_surjective B hcover φ⟩

@[simp] theorem partitionPairEquiv_apply (B : ι → Set Γ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcover : (⋃ i, B i) = Set.univ) (φ : ∀ i, B i × ℕ ≃ ℕ) (i : ι) (n : ℕ) :
    partitionPairEquiv B hB hcover φ (i, n) =
      (((φ i).symm n).1.val, ((φ i).symm n).2) := rfl

theorem partitionPairEquiv_fst_mem_iff (B : ι → Set Γ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcover : (⋃ i, B i) = Set.univ) (φ : ∀ i, B i × ℕ ≃ ℕ)
    (i j : ι) (n : ℕ) :
    (partitionPairEquiv B hB hcover φ (j, n)).1 ∈ B i ↔ j = i := by
  constructor
  · intro h
    by_contra hne
    exact Set.disjoint_left.mp (hB hne) (((φ j).symm n).1.property) h
  · rintro rfl
    exact ((φ j).symm n).1.property

end ThesisCommon
