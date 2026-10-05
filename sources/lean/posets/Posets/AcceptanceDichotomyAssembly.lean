import Posets.AcceptanceDichotomyScalarBorel
import Posets.BorelMatching

/-! Assembly of the acceptance/rejection dichotomy from the analytic
decidability statement for a single subset of the natural numbers. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology MeasureTheory
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

local instance : MeasurableSpace (ℕ → Bool) := borel _
local instance : BorelSpace (ℕ → Bool) := ⟨rfl⟩
local instance : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool)) := borel _
local instance : BorelSpace ((ℕ → Bool) × (ℕ → Bool)) := ⟨rfl⟩

theorem acceptance_rejection_dichotomy_of_decidability (𝒜 : Set (Set ℕ))
    (M : ScalarMatrix 𝕜)
    (hdec : ∀ A : Set ℕ, (¬ ∃ a : 𝕜, AcceptsPair 𝕜 A A (M - a • identityMatrix 𝕜)) →
      ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ Rejects 𝕜 B B M) :
    Lemma_5_2 𝕜 𝒜 M := by
  intro hAD _hunc hborel hM
  let R : Set ((ℕ → Bool) × (ℕ → Bool)) := {p |
    p.1 ∈ cantorCode '' 𝒜 ∧ p.2 ∈ cantorCode '' 𝒜 ∧
    ¬ ∃ a : 𝕜, AcceptsPair 𝕜 (cantorSet p.1 ∪ cantorSet p.2)
      (cantorSet p.1 ∪ cantorSet p.2) (M - a • identityMatrix 𝕜)}
  have hR : MeasurableSet R := (hborel.preimage continuous_fst.measurable).inter
    ((hborel.preimage continuous_snd.measurable).inter
      (measurableSet_union_exists_scalarShift_cantor M hM).compl)
  rcases borel_square_matching_dichotomy hR with ⟨Y, hY, hcover⟩ | ⟨f, hfR, hf⟩
  · left
    let 𝒜' := 𝒜 ∩ cantorSet '' Y
    refine ⟨𝒜', Set.inter_subset_left, (hY.image cantorSet).mono Set.inter_subset_right, ?_⟩
    apply accepts_scalarShift_amalgamation hM (fun A hA => hAD.1 A hA.1)
    intro A hA B hB
    by_contra hbad
    have hpair : (cantorCode A, cantorCode B) ∈ R := by
      refine ⟨⟨A, hA.1, rfl⟩, ⟨B, hB.1, rfl⟩, ?_⟩
      simpa only [cantorSet_cantorCode] using hbad
    rcases hcover _ hpair with hAY | hBY
    · exact hA.2 ⟨hA.1, ⟨cantorCode A, hAY, cantorSet_cantorCode A⟩⟩
    · exact hB.2 ⟨hB.1, ⟨cantorCode B, hBY, cantorSet_cantorCode B⟩⟩
  · right
    let A (ξ : Set ℕ) := cantorSet (f (cantorCode ξ)).1
    let A' (ξ : Set ℕ) := cantorSet (f (cantorCode ξ)).2
    have hfamily (p : ℕ → Bool) (hp : p ∈ cantorCode '' 𝒜) : cantorSet p ∈ 𝒜 := by
      obtain ⟨C, hC, rfl⟩ := hp
      simpa only [cantorSet_cantorCode] using hC
    have hdata (ξ : Set ℕ) : A ξ ∈ 𝒜 ∧ A' ξ ∈ 𝒜 ∧
        ¬ ∃ a : 𝕜, AcceptsPair 𝕜 (A ξ ∪ A' ξ) (A ξ ∪ A' ξ)
          (M - a • identityMatrix 𝕜) := by
      have h := hfR (Set.mem_range_self (cantorCode ξ))
      exact ⟨hfamily _ h.1, hfamily _ h.2.1, h.2.2⟩
    choose B hBsub hBinf hBrej using fun ξ => hdec (A ξ ∪ A' ξ) (hdata ξ).2.2
    refine ⟨A, A', B, fun ξ => ⟨(hdata ξ).1, (hdata ξ).2.1, hBinf ξ, hBsub ξ, hBrej ξ⟩, ?_⟩
    intro ξ η hne
    have hcode : cantorCode ξ ≠ cantorCode η := by
      intro h
      apply hne
      simpa only [cantorSet_cantorCode] using congrArg cantorSet h
    have hdisj := hf hcode
    apply Set.disjoint_left.mpr
    intro C hCξ hCη
    have hξ : cantorCode C ∈ ({(f (cantorCode ξ)).1, (f (cantorCode ξ)).2} : Set (ℕ → Bool)) := by
      rcases Set.mem_insert_iff.mp hCξ with rfl | hCξ
      · simp [A]
      · obtain rfl := Set.mem_singleton_iff.mp hCξ
        simp [A']
    have hη : cantorCode C ∈ ({(f (cantorCode η)).1, (f (cantorCode η)).2} : Set (ℕ → Bool)) := by
      rcases Set.mem_insert_iff.mp hCη with rfl | hCη
      · simp [A]
      · obtain rfl := Set.mem_singleton_iff.mp hCη
        simp [A']
    exact Set.disjoint_left.mp hdisj hξ hη

end Posets
