import Posets.MainWitnessConstruction
import Posets.ClosedAlmostDisjointFamily
import Posets.MainMatrixSelection

/-! Converting the acceptance/rejection dichotomy into the finite pools used
in Section 5. The dichotomy is an explicit hypothesis in this module. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
open Cardinal
variable {𝕜 : Type} [RCLike 𝕜]

local instance mainPoolMeasurable : MeasurableSpace (ℕ → Bool) := borel (ℕ → Bool)
local instance mainPoolBorel : BorelSpace (ℕ → Bool) := ⟨rfl⟩

def closedTreeFamilyEquiv : Set ℕ ≃ closedTreeFamily :=
  Classical.choice (Cardinal.eq.mp (Cardinal.mk_set_nat.trans closedTreeFamily_card.symm))

def treeSingletonPool : FiniteWitnessPool closedTreeFamily where
  cover i := {(closedTreeFamilyEquiv i).val}
  member i A h := by
    have he : A = (closedTreeFamilyEquiv i).val := Finset.mem_singleton.mp h
    exact he ▸ (closedTreeFamilyEquiv i).property
  witness i := (closedTreeFamilyEquiv i).val
  infinite i := closedTreeFamily_almostDisjoint.1 _ (closedTreeFamilyEquiv i).property
  subset i := by
    intro n hn
    exact Set.mem_iUnion₂.mpr ⟨_, Finset.mem_singleton_self _, hn⟩
  disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro A hi hj
    apply hij
    apply closedTreeFamilyEquiv.injective
    apply Subtype.ext
    exact (Finset.mem_singleton.mp hi).symm.trans (Finset.mem_singleton.mp hj)

theorem exists_rejectionPool_of_dichotomy {𝒞 : Set (Set ℕ)} (M : ScalarMatrix 𝕜)
    (h𝒞 : IsAlmostDisjoint 𝒞) (hunc : ¬ 𝒞.Countable)
    (hborel : @MeasurableSet (ℕ → Bool) (borel (ℕ → Bool)) (cantorCode '' 𝒞))
    (hdich : Lemma_5_2 𝕜 𝒞 M) (hM : HasBoundedRows 𝕜 M)
    (hbad : ¬ ScalarShiftAcceptedOffCountable 𝒞 M) :
    ∃ pool : FiniteWitnessPool 𝒞, ∀ i, Rejects 𝕜 (pool.witness i) (pool.witness i) M := by
  rcases hdich h𝒞 hunc hborel hM with hgood | ⟨A, A', B, h, hd⟩
  · exact (hbad ((scalarShiftAcceptedOffCountable_iff_subfamily M).mpr hgood)).elim
  · let pool : FiniteWitnessPool 𝒞 := {
      cover := fun i => {A i, A' i}
      member := by
        intro i X hX
        rcases Finset.mem_insert.mp hX with rfl | hX
        · exact (h i).1
        · exact Finset.mem_singleton.mp hX ▸ (h i).2.1
      witness := B
      infinite := fun i => (h i).2.2.1
      subset := by
        intro i n hn
        rcases (h i).2.2.2.1 hn with hn | hn
        · exact Set.mem_iUnion₂.mpr ⟨A i, by simp, hn⟩
        · exact Set.mem_iUnion₂.mpr ⟨A' i, by simp, hn⟩
      disjoint := by
        intro i j hij
        apply Finset.disjoint_left.mpr
        intro X hi hj
        apply Set.disjoint_left.mp (hd hij)
        · simpa only [Finset.mem_insert, Finset.mem_singleton,
            Set.mem_insert_iff, Set.mem_singleton_iff] using hi
        · simpa only [Finset.mem_insert, Finset.mem_singleton,
            Set.mem_insert_iff, Set.mem_singleton_iff] using hj }
    exact ⟨pool, fun i => (h i).2.2.2.2⟩

def matrixWitnessPool (hdich : ∀ M : ScalarMatrix 𝕜, Lemma_5_2 𝕜 closedTreeFamily M)
    (M : ScalarMatrix 𝕜) : FiniteWitnessPool closedTreeFamily :=
  if h : HasBoundedRows 𝕜 M ∧ ¬ ScalarShiftAcceptedOffCountable closedTreeFamily M then
    Classical.choose (exists_rejectionPool_of_dichotomy M
      closedTreeFamily_almostDisjoint closedTreeFamily_uncountable
      closedTreeFamily_cantorCode_closed.measurableSet (hdich M) h.1 h.2)
  else treeSingletonPool

theorem matrixWitnessPool_rejects
    (hdich : ∀ M : ScalarMatrix 𝕜, Lemma_5_2 𝕜 closedTreeFamily M)
    (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M)
    (hbad : ¬ ScalarShiftAcceptedOffCountable closedTreeFamily M) (i : Set ℕ) :
    Rejects 𝕜 ((matrixWitnessPool hdich M).witness i)
      ((matrixWitnessPool hdich M).witness i) M := by
  unfold matrixWitnessPool
  rw [dif_pos ⟨hM, hbad⟩]
  exact Classical.choose_spec (exists_rejectionPool_of_dichotomy M
    closedTreeFamily_almostDisjoint closedTreeFamily_uncountable
    closedTreeFamily_cantorCode_closed.measurableSet (hdich M) hM hbad) i

theorem exists_main_rejection_witnesses
    (hdich : ∀ M : ScalarMatrix 𝕜, Lemma_5_2 𝕜 closedTreeFamily M) :
    ∃ F : ContinuumStage → Finset (Set ℕ),
    ∃ B : ContinuumStage → Set ℕ,
    ∃ H : Set (Set ℕ), ∃ C : Set ℕ × Set ℕ → Set ℕ,
      (∀ i A, A ∈ F i → A ∈ closedTreeFamily) ∧
      (Pairwise fun i j => Disjoint (F i) (F j)) ∧
      (∀ i, (B i).Infinite) ∧ (∀ i, B i ⊆ ⋃ A ∈ F i, A) ∧
      H ⊆ Set.range B ∧ Set.range C ⊆ Set.range B ∧
      Function.Injective C ∧ (∀ α β, C (α, β) ∉ H) ∧
      (∀ M : ScalarMatrix 𝕜, HasBoundedRows 𝕜 M →
        ¬ ScalarShiftAcceptedOffCountable closedTreeFamily M →
        ¬ {A ∈ H | Rejects 𝕜 A A M}.Countable) := by
  let pool : Option (ScalarMatrix 𝕜) → FiniteWitnessPool closedTreeFamily :=
    fun x => x.elim treeSingletonPool (matrixWitnessPool hdich)
  let R : ScalarMatrix 𝕜 → Set ℕ → Prop := fun M A =>
    HasBoundedRows 𝕜 M → ¬ ScalarShiftAcceptedOffCountable closedTreeFamily M →
      Rejects 𝕜 A A M
  have hR (M : ScalarMatrix 𝕜) (i : Set ℕ) : R M ((pool (some M)).witness i) :=
    fun hM hbad => matrixWitnessPool_rejects hdich M hM hbad i
  obtain ⟨F, B, H, C, hm, hd, hi, hs, hH, hC, hinj, hprivate, hr⟩ :=
    exists_common_private_witnesses (scalarMatrix_card 𝕜).le
      closedTreeFamily_almostDisjoint pool R hR
  refine ⟨F, B, H, C, hm, hd, hi, hs, hH, hC, hinj, hprivate, ?_⟩
  intro M hM hbad hcount
  apply hr M
  apply hcount.mono
  intro A hA
  exact ⟨hA.1, hA.2 hM hbad⟩

end Posets
