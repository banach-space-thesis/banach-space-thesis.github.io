import BanachIsometric.ConvexSingularAcyclicity
import BanachIsometric.ContractibleZeroHomology

/-! Actual boundary fillings on contractible singular models, including the
augmentation-zero degree-zero case. The choice operator is not asserted
linear or natural. The acyclic-model constructions use it only on their
fixed universal simplex products, then push the chosen chains forward. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

theorem raw_positive_cycle_bounds_of_contractible
    {X : Type*} [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (c : RawRationalChains X (n + 1)) (hc : rawBoundary n c = 0) :
    ∃ b : RawRationalChains X (n + 2), rawBoundary (n + 1) b = c := by
  let z : rawCycles X n := ⟨c, hc⟩
  have hz : (Submodule.Quotient.mk z : RawPositiveHomology X n) = 0 :=
    @Subsingleton.elim (RawPositiveHomology X n) (rawPositiveHomology_contractible X n) _ _
  have hm : z ∈ rawBoundaries X n := (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨b, hb⟩ := hm
  exact ⟨b, congrArg Subtype.val hb⟩

theorem raw_augmentation_zero_bounds_of_contractible
    {X : Type*} [TopologicalSpace X] [ContractibleSpace X]
    (c : RawRationalChains X 0) (hc : rawAugmentation X c = 0) :
    ∃ b : RawRationalChains X 1, rawBoundary 0 b = c := by
  have hz : (Submodule.Quotient.mk c : RawZeroHomology X) = 0 := by
    apply (rawZeroHomologyContractibleEquiv X).injective
    rw [map_zero]
    exact hc
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range (rawBoundary (X := X) 0))).mp hz

def rawBoundaryChoice {X : Type*} [TopologicalSpace X] (n : ℕ)
    (c : RawRationalChains X n) : RawRationalChains X (n + 1) := by
  classical
  exact if h : ∃ b : RawRationalChains X (n + 1), rawBoundary n b = c then h.choose else 0

theorem rawBoundaryChoice_spec {X : Type*} [TopologicalSpace X] (n : ℕ)
    (c : RawRationalChains X n)
    (h : ∃ b : RawRationalChains X (n + 1), rawBoundary n b = c) :
    rawBoundary n (rawBoundaryChoice n c) = c := by
  classical
  rw [rawBoundaryChoice, dif_pos h]
  exact h.choose_spec

def simplexVertex (n : ℕ) (i : Fin (n + 1)) : Simplex n :=
  ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩

theorem simplex_contractible (n : ℕ) : ContractibleSpace (Simplex n) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace ⟨_, (simplexVertex n 0).property⟩

theorem contractible_product (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] [ContractibleSpace Y] : ContractibleSpace (X × Y) := by
  obtain ⟨eX⟩ := ContractibleSpace.hequiv_unit X
  obtain ⟨eY⟩ := ContractibleSpace.hequiv_unit Y
  exact (eX.prodCongr eY).contractibleSpace

theorem simplex_product_contractible (p q : ℕ) : ContractibleSpace (Simplex p × Simplex q) := by
  letI := simplex_contractible p
  letI := simplex_contractible q
  exact contractible_product _ _

end BanachIsometric.SingularPrism
