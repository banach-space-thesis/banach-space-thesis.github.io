import BanachIsometric.RawUnionOverlapKernel
import BanachIsometric.SmallChainHomologyFilling

/-! Actual small representatives for the two-set homology argument. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X : Type*} [TopologicalSpace X]

def twoSetCover (U V : Set X) : Bool → Set X
  | false => U
  | true => V

theorem rawSmallChainCarrier_twoSet_eq_sup (U V : Set X) (n : ℕ) :
    rawSmallChainCarrier (twoSetCover U V) n =
      LinearMap.range (rawSubspaceChainInclusion U n) ⊔
        LinearMap.range (rawSubspaceChainInclusion V n) := by
  simp only [range_rawSubspaceChainInclusion, ← Finsupp.supported_union]
  unfold rawSmallChainCarrier
  congr 1
  ext σ
  constructor
  · rintro ⟨i, hi⟩
    cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩

omit [TopologicalSpace X] in
theorem twoSetCover_covers (U V : Set X) (hcover : U ∪ V = Set.univ) (x : X) :
    ∃ i, x ∈ twoSetCover U V i := by
  have h : x ∈ U ∪ V := by rw [hcover]; exact Set.mem_univ _
  rcases h with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

theorem rawSmall_twoSet_split (U V : Set X) (n : ℕ) (c : RawRationalChains X n)
    (hc : c ∈ rawSmallChainCarrier (twoSetCover U V) n) :
    ∃ p : RawUnionChainPair U V n, rawUnionChainSum U V n p = c := by
  rw [rawSmallChainCarrier_twoSet_eq_sup] at hc
  obtain ⟨a, ⟨a', ha⟩, b, ⟨b', hb⟩, hab⟩ := Submodule.mem_sup.mp hc
  exact ⟨(a', b'), by
    change rawSubspaceChainInclusion U n a' + rawSubspaceChainInclusion V n b' = c
    rw [ha, hb, hab]⟩

theorem rawUnionPairToHomology_surjective (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    Function.Surjective (rawUnionPairToHomology U V n) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    obtain ⟨d, hd, hdcycle, e, he⟩ := exists_small_cycle_representative (twoSetCover U V)
      (fun i => by cases i <;> assumption) (twoSetCover_covers U V hcover) n c.val c.property
    obtain ⟨p, hp⟩ := rawSmall_twoSet_split U V (n + 1) d hd
    let z : rawUnionPairCycles U V n := ⟨p, by
      change rawBoundary n (rawUnionChainSum U V (n + 1) p) = 0
      rwa [hp]⟩
    refine ⟨z, ?_⟩
    change Submodule.Quotient.mk (rawUnionPairToCycles U V n z) = Submodule.Quotient.mk c
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-e, ?_⟩
    apply Subtype.ext
    change rawBoundary (n + 1) (-e) = rawUnionChainSum U V (n + 1) p - c.val
    rw [map_neg, he, hp, neg_sub]

theorem rawZeroHomologyComponentSum_surjective (U V : Set X) (hcover : U ∪ V = Set.univ) :
    Function.Surjective (rawDegreeHomologyComponentSum U V 0) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    have hc : c ∈ rawSmallChainCarrier (twoSetCover U V) 0 := by
      rw [rawSmallChainCarrier_zero_eq_top _ (twoSetCover_covers U V hcover)]
      exact Submodule.mem_top
    obtain ⟨p, hp⟩ := rawSmall_twoSet_split U V 0 c hc
    refine ⟨(Submodule.Quotient.mk p.1, Submodule.Quotient.mk p.2), ?_⟩
    change Submodule.Quotient.mk (rawSubspaceChainInclusion U 0 p.1) +
      Submodule.Quotient.mk (rawSubspaceChainInclusion V 0 p.2) =
        (Submodule.Quotient.mk c : RawZeroHomology X)
    rw [← Submodule.Quotient.mk_add]
    exact congrArg Submodule.Quotient.mk hp

end BanachIsometric.SingularPrism
