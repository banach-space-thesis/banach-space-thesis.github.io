import BanachIsometric.RawSingularSubdivision
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! Small singular chains for an actual set cover. Both literal
subdivision and its literal homotopy preserve small chains, because all
their universal pieces remain inside the original singular simplex. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

theorem rawChainMap_supported {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (P : Set (RawSingularSimplex X n)) (Q : Set (RawSingularSimplex Y n))
    (h : ∀ simplex ∈ P, f.comp simplex ∈ Q) :
    Finsupp.supported ℚ ℚ P ≤ (Finsupp.supported ℚ ℚ Q).comap (rawChainMap f n) := by
  rw [Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨simplex, hsimplex, rfl⟩
  change rawChainMap f n (Finsupp.single simplex 1) ∈ Finsupp.supported ℚ ℚ Q
  simp only [rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact Finsupp.single_mem_supported ℚ 1 (h simplex hsimplex)

theorem rawChainMap_supported_all {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (Q : Set (RawSingularSimplex Y n))
    (h : ∀ simplex, f.comp simplex ∈ Q) (c : RawRationalChains X n) :
    rawChainMap f n c ∈ Finsupp.supported ℚ ℚ Q := by
  apply rawChainMap_supported f n Set.univ Q (fun simplex _ => h simplex)
  apply (Finsupp.mem_supported ℚ c).mpr
  exact Set.subset_univ _

def rawSmallChainCarrier {X ι : Type*} [TopologicalSpace X] (U : ι → Set X) (n : ℕ) :
    Submodule ℚ (RawRationalChains X n) :=
  Finsupp.supported ℚ ℚ {simplex | ∃ i, Set.range simplex ⊆ U i}

theorem rawSubdivision_preserves_small {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (n : ℕ) :
    rawSmallChainCarrier U n ≤ (rawSmallChainCarrier U n).comap (rawSubdivision X n) := by
  conv_lhs => rw [rawSmallChainCarrier, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨simplex, ⟨i, hi⟩, rfl⟩
  change rawSubdivision X n (Finsupp.single simplex 1) ∈ rawSmallChainCarrier U n
  rw [rawSubdivision_single_one]
  apply rawChainMap_supported_all
  intro piece
  refine ⟨i, ?_⟩
  rintro _ ⟨w, rfl⟩
  exact hi (Set.mem_range_self (piece w))

theorem rawSubdivisionHomotopy_preserves_small {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (n : ℕ) :
    rawSmallChainCarrier U n ≤
      (rawSmallChainCarrier U (n + 1)).comap (rawSubdivisionHomotopy X n) := by
  conv_lhs => rw [rawSmallChainCarrier, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨simplex, ⟨i, hi⟩, rfl⟩
  change rawSubdivisionHomotopy X n (Finsupp.single simplex 1) ∈ rawSmallChainCarrier U (n + 1)
  rw [rawSubdivisionHomotopy_single_one]
  apply rawChainMap_supported_all
  intro piece
  refine ⟨i, ?_⟩
  rintro _ ⟨w, rfl⟩
  exact hi (Set.mem_range_self (piece w))

end BanachIsometric.SingularPrism
