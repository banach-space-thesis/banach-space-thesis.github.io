import JFA.MrowkaTopology
import Mathlib.Order.Interval.Finset.Nat

/-! A countable subfamily admits pairwise disjoint compact clopen tails in
the original Mrówka space. Each tail removes only the finite intersections
with members earlier in an injective natural-number numbering. -/

noncomputable section
open TopologicalSpace Set
namespace JFA
set_option allowUnsafeReducibility true in
attribute [local reducible] Mrowka
variable {𝒜 : Set (Set ℕ)}
local instance countableTailsTopology : TopologicalSpace (Mrowka 𝒜) := mrowkaTopology 𝒜

theorem mrowka_isClopen_neighborhood (h𝒜 : IsAlmostDisjoint 𝒜)
    (A : 𝒜) (G : Finset ℕ) : IsClopen (mrowkaNeighborhood 𝒜 A G) := by
  letI := mrowka_t2Space h𝒜
  exact ⟨(mrowka_isCompact_neighborhood A G).isClosed, mrowka_isOpen_neighborhood A G⟩

theorem exists_pairwise_disjoint_mrowka_tails (h𝒜 : IsAlmostDisjoint 𝒜)
    {ι : Type*} [Countable ι] (b : ι → 𝒜) (hb : Function.Injective b) :
    ∃ G : ι → Finset ℕ, Pairwise fun i j =>
      Disjoint (mrowkaNeighborhood 𝒜 (b i) (G i)) (mrowkaNeighborhood 𝒜 (b j) (G j)) := by
  classical
  obtain ⟨code, hcode⟩ := exists_injective_nat ι
  let earlier (i : ι) : Set ι := {j | code j < code i}
  have hearlier (i : ι) : (earlier i).Finite := by
    change (code ⁻¹' Set.Iio (code i)).Finite
    exact (Set.finite_Iio (code i)).preimage hcode.injOn
  let F (i : ι) : Set ℕ := ⋃ j ∈ earlier i, (b i : Set ℕ) ∩ (b j : Set ℕ)
  have hF (i : ι) : (F i).Finite := (hearlier i).biUnion (fun j hj =>
    h𝒜.2 (b i) (b i).property (b j) (b j).property (by
      intro heq
      have hij : i = j := hb (Subtype.ext heq)
      exact (lt_irrefl (code i)) (hij ▸ hj)))
  let G (i : ι) : Finset ℕ := (hF i).toFinset
  have hd (i j : ι) (hij : code i < code j) :
      Disjoint (mrowkaNeighborhood 𝒜 (b i) (G i)) (mrowkaNeighborhood 𝒜 (b j) (G j)) := by
    apply disjoint_left.mpr
    intro p hpi hpj
    cases p with
    | inr A =>
      have hAi := (mrowka_inr_mem (b i) A (G i)).mp hpi
      have hAj := (mrowka_inr_mem (b j) A (G j)).mp hpj
      have heq := congrArg code (hb (hAi.symm.trans hAj))
      exact (ne_of_lt hij) heq
    | inl n =>
      have hni := (mrowka_inl_mem (b i) (G i) n).mp hpi
      have hnj := (mrowka_inl_mem (b j) (G j) n).mp hpj
      apply hnj.2
      exact (hF j).mem_toFinset.mpr (mem_iUnion₂.mpr ⟨i, hij, hnj.1, hni.1⟩)
  refine ⟨G, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne (hcode.ne hij) with hlt | hgt
  · exact hd i j hlt
  · exact (hd j i hgt).symm

end JFA
