import ThesisCommon.Analysis.BooleanAdjoin
import Mathlib.Data.Set.Countable

/-! Finite support and cardinal bounds for a generated Boolean algebra. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon

theorem booleanClosure_finite_support {α : Type*} {S : Set (Set α)}
    {A : Set α} (hA : A ∈ BooleanSubalgebra.closure S) :
    ∃ F : Finset (Set α), (↑F : Set (Set α)) ⊆ S ∧ A ∈ BooleanSubalgebra.closure ↑F := by
  classical
  induction hA using BooleanSubalgebra.closure_bot_sup_induction with
  | mem A hA => exact ⟨{A}, by simpa, BooleanSubalgebra.subset_closure (by simp)⟩
  | bot => exact ⟨∅, by simp, BooleanSubalgebra.bot_mem⟩
  | sup A hA D hD ihA ihD =>
    obtain ⟨F, hF, hAF⟩ := ihA
    obtain ⟨G, hG, hDG⟩ := ihD
    refine ⟨F ∪ G, ?_, ?_⟩
    · simpa only [Finset.coe_union] using Set.union_subset hF hG
    · have hFG : BooleanSubalgebra.closure (↑F : Set (Set α)) ≤
          BooleanSubalgebra.closure (↑(F ∪ G) : Set (Set α)) :=
        BooleanSubalgebra.closure_mono (fun _ hx => Finset.mem_union_left G hx)
      have hGF : BooleanSubalgebra.closure (↑G : Set (Set α)) ≤
          BooleanSubalgebra.closure (↑(F ∪ G) : Set (Set α)) :=
        BooleanSubalgebra.closure_mono (fun _ hx => Finset.mem_union_right F hx)
      exact BooleanSubalgebra.sup_mem (hFG hAF) (hGF hDG)
  | compl A hA ih =>
    obtain ⟨F, hF, hAF⟩ := ih
    exact ⟨F, hF, (BooleanSubalgebra.closure (↑F : Set (Set α))).compl_mem hAF⟩

def booleanDepth {α : Type} (S : Set (Set α)) : ℕ → Set (Set α)
  | 0 => insert ∅ S
  | n+1 => booleanDepth S n ∪ (fun A : Set α => Aᶜ) '' booleanDepth S n ∪
      (fun p : Set α × Set α => p.1 ∪ p.2) '' (booleanDepth S n ×ˢ booleanDepth S n)

theorem booleanDepth_mono {α : Type} (S : Set (Set α)) : Monotone (booleanDepth S) := by
  apply monotone_nat_of_le_succ
  intro n A hA
  exact Or.inl (Or.inl hA)

theorem booleanClosure_subset_depths {α : Type} (S : Set (Set α)) :
    (BooleanSubalgebra.closure S : Set (Set α)) ⊆ ⋃ n, booleanDepth S n := by
  intro A hA
  induction hA using BooleanSubalgebra.closure_bot_sup_induction with
  | mem A hA => exact Set.mem_iUnion.mpr ⟨0, Or.inr hA⟩
  | bot => exact Set.mem_iUnion.mpr ⟨0, Or.inl rfl⟩
  | sup A hA D hD ihA ihD =>
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ihA
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ihD
    exact Set.mem_iUnion.mpr ⟨max n m + 1, Or.inr ⟨(A,D),
      ⟨booleanDepth_mono S (le_max_left _ _) hn,
        booleanDepth_mono S (le_max_right _ _) hm⟩, rfl⟩⟩
  | compl A hA ih =>
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ih
    exact Set.mem_iUnion.mpr ⟨n+1, Or.inl (Or.inr ⟨A, hn, rfl⟩)⟩

theorem booleanClosure_cardinal_le {α : Type} (S : Set (Set α))
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hS : #S ≤ κ) :
    #(BooleanSubalgebra.closure S) ≤ κ := by
  have hsum : κ + κ = κ := Cardinal.add_eq_self hκ
  have hprod : κ * κ = κ := Cardinal.mul_eq_self hκ
  have hd (n : ℕ) : #(booleanDepth S n) ≤ κ := by
    induction n with
    | zero =>
      change #(insert (∅ : Set α) S : Set (Set α)) ≤ κ
      calc
        _ ≤ #({∅} : Set (Set α)) + #S := by
          simpa only [Set.singleton_union] using Cardinal.mk_union_le {∅} S
        _ ≤ κ + κ := add_le_add (by simpa using Cardinal.one_le_aleph0.trans hκ) hS
        _ = κ := hsum
    | succ n ih =>
      have hc : #((fun A : Set α => Aᶜ) '' booleanDepth S n) ≤ κ :=
        Cardinal.mk_image_le.trans ih
      have hu : #((fun p : Set α × Set α => p.1 ∪ p.2) ''
          (booleanDepth S n ×ˢ booleanDepth S n)) ≤ κ := by
        exact Cardinal.mk_image_le.trans (by
          rw [Cardinal.mk_setProd]
          exact (mul_le_mul' ih ih).trans_eq hprod)
      exact (Cardinal.mk_union_le _ _).trans ((add_le_add
        ((Cardinal.mk_union_le _ _).trans ((add_le_add ih hc).trans_eq hsum)) hu).trans_eq hsum)
  calc
    _ ≤ #(⋃ n, booleanDepth S n) := Cardinal.mk_le_mk_of_subset (booleanClosure_subset_depths S)
    _ ≤ #ℕ * ⨆ n, #(booleanDepth S n) := Cardinal.mk_iUnion_le _
    _ ≤ κ * κ := mul_le_mul' (by simpa using hκ) (ciSup_le' hd)
    _ = κ := hprod

theorem booleanClosure_directed_union_mem {α I : Type*} [Nonempty I]
    (B : I → BooleanSubalgebra (Set α)) (hdir : Directed (· ≤ ·) B)
    {A : Set α} (hA : A ∈ BooleanSubalgebra.closure (⋃ i, (B i : Set (Set α)))) :
    ∃ i, A ∈ B i := by
  induction hA using BooleanSubalgebra.closure_bot_sup_induction with
  | mem A hA => exact Set.mem_iUnion.mp hA
  | bot => exact ⟨Classical.arbitrary I, BooleanSubalgebra.bot_mem⟩
  | sup A hA D hD ihA ihD =>
    obtain ⟨i, hi⟩ := ihA
    obtain ⟨j, hj⟩ := ihD
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, (B k).sup_mem (hik hi) (hjk hj)⟩
  | compl A hA ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, (B i).compl_mem hi⟩

end ThesisCommon
