import Sigma.ConstructedFamilies
import Sigma.AdaptiveConstruction
import ThesisCommon.Analysis.UltrafilterCharge

/-! Reserve an infinite part of the countable base for the infinity atom. All
stock cylinders, and hence all eventual split pieces, avoid that part. -/
noncomputable section
open Set Cardinal Filter ThesisCommon
namespace SigmaNonprimarity

theorem exists_continuum_stock_inside (C : Set ℕ) (hC : C.Infinite) :
    ∃ R : ConstructionIndex → Set ℕ,
      (∀ i, R i ⊆ C ∧ (R i).Infinite) ∧ Pairwise (fun i j => (R i ∩ R j).Finite) := by
  obtain ⟨S,hcard,hS,hpair⟩ := continuum_almostDisjoint_subsets C hC
  obtain ⟨e⟩ := Cardinal.eq.mp (constructionIndex_cardinal.trans hcard.symm)
  refine ⟨fun i => (e i).val, fun i => hS _ (e i).property, ?_⟩
  intro i j hij
  exact hpair (e i).property (e j).property (fun h => hij (e.injective (Subtype.ext h)))

theorem exists_reserved_stock : ∃ (C : Set ℕ) (R : ConstructionIndex → Set ℕ),
    C.Infinite ∧ Cᶜ.Infinite ∧ (∀ i, R i ⊆ C ∧ (R i).Infinite) ∧
      Pairwise (fun i j => (R i ∩ R j).Finite) := by
  obtain ⟨C,_,hC,hCc⟩ := infinite_coinfinite_subset (Set.univ : Set ℕ) Set.infinite_univ
  obtain ⟨R,hR,hpair⟩ := exists_continuum_stock_inside C hC
  exact ⟨C,R,hC,hCc.mono (fun _ hn => hn.2),hR,hpair⟩

def reservedInfinityUltrafilter (C : Set ℕ) (hC : Cᶜ.Infinite) : Ultrafilter Point :=
  freeUltrafilterOn (cylinder Cᶜ) (cylinder_infinite hC)

theorem reservedInfinityUltrafilter_free (C : Set ℕ) (hC : Cᶜ.Infinite) :
    (reservedInfinityUltrafilter C hC : Filter Point) ≤ Filter.cofinite :=
  freeUltrafilterOn_le_cofinite _ _

theorem reservedInfinityUltrafilter_avoids (C : Set ℕ) (hC : Cᶜ.Infinite)
    {A : Set Point} (hA : A ⊆ cylinder C) : A ∉ reservedInfinityUltrafilter C hC := by
  intro hAU
  have hCU : cylinder Cᶜ ∈ reservedInfinityUltrafilter C hC := mem_freeUltrafilterOn _ _
  apply (reservedInfinityUltrafilter C hC).neBot.not_disjoint hCU hAU
  apply Set.disjoint_left.mpr
  intro p hp hpa
  exact hp (hA hpa)

theorem threeLevelChoice_family_subset {I : Type} (μ : I → AtomicRows) (R : I → Set ℕ)
    (d : ∀ i, ThreeLevelChoice (μ i) (R i)) (C : Set ℕ) (hR : ∀ i, R i ⊆ C) :
    ∀ A ∈ splitFamily (fun i => (d i).J₁) (fun i => (d i).Z), A ⊆ cylinder C := by
  have hJ (i : I) : (d i).J₁ ⊆ C := ((d i).J₁_subset.trans (d i).J₀_subset).trans (hR i)
  rintro A (⟨i,rfl⟩ | ⟨i,rfl⟩) p hp
  · exact hJ i ((d i).splits.1 hp)
  · exact hJ i hp.1

theorem reservedInfinityUltrafilter_avoids_family {I : Type}
    (μ : I → AtomicRows) (R : I → Set ℕ) (d : ∀ i, ThreeLevelChoice (μ i) (R i))
    (C : Set ℕ) (hC : Cᶜ.Infinite) (hR : ∀ i, R i ⊆ C) :
    ∀ A ∈ splitFamily (fun i => (d i).J₁) (fun i => (d i).Z),
      A ∉ reservedInfinityUltrafilter C hC :=
  fun A hA => reservedInfinityUltrafilter_avoids C hC (threeLevelChoice_family_subset μ R d C hR A hA)

end SigmaNonprimarity
