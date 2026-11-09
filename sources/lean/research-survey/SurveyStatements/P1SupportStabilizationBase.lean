import SurveyStatements.P1PrefixClassRamsey
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-! The exact assignment hypotheses and elementary finite-prefix geometry for
the support stabilization used in the complex Elton selection argument. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Filter Topology

namespace SurveyStatements.P1

/-- Discrete finite-witness selection gives this stronger form of pointwise
continuity: the whole selected scalar sequence is fixed by a finite front. -/
def SupportAssignmentLocallyConstant (f : Set ℕ → ℕ → ℂ) : Prop :=
  ∀ M : Set ℕ, M.Infinite → ∃ r : ℕ, ∀ Q : Set ℕ, Q.Infinite →
    (∀ i : ℕ, i < r → (i ∈ M ↔ i ∈ Q)) → f Q = f M

/-- Every sequence of assigned values has an actual coordinatewise convergent
subsequence whose limit belongs to `c₀`, expressed without a change of topology. -/
def SupportAssignmentSequentialC0Cluster (f : Set ℕ → ℕ → ℂ) : Prop :=
  ∀ P : ℕ → Set ℕ, (∀ n, (P n).Infinite) →
    ∃ g : ℕ → ℂ, ∃ ν : ℕ → ℕ, StrictMono ν ∧
      Tendsto g atTop (𝓝 0) ∧
      ∀ i : ℕ, Tendsto (fun n => f (P (ν n)) i) atTop (𝓝 (g i))

theorem support_prefix_eq_low_membership (ν η : ℕ → ℕ)
    (hν : StrictMono ν) (hη : StrictMono η) {N : ℕ}
    (heq : (Finset.range N).image η = (Finset.range N).image ν) :
    ∀ i : ℕ, i < N → (i ∈ range ν ↔ i ∈ range η) := by
  intro i hi
  constructor
  · rintro ⟨j, rfl⟩
    have hj : j < N := (hν.id_le j).trans_lt hi
    have hm : ν j ∈ (Finset.range N).image η := by
      rw [heq]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hm
    exact ⟨k, hk⟩
  · rintro ⟨j, rfl⟩
    have hj : j < N := (hη.id_le j).trans_lt hi
    have hm : η j ∈ (Finset.range N).image ν := by
      rw [← heq]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hm
    exact ⟨k, hk⟩

theorem support_prefix_eq_first (ν η : ℕ → ℕ)
    (hν : StrictMono ν) (hη : StrictMono η) {N : ℕ} (hN : 0 < N)
    (heq : (Finset.range N).image η = (Finset.range N).image ν) : η 0 = ν 0 := by
  apply le_antisymm
  · have hm : ν 0 ∈ (Finset.range N).image η := by
      rw [heq]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hN, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact hj ▸ hη.monotone (Nat.zero_le j)
  · have hm : η 0 ∈ (Finset.range N).image ν := by
      rw [← heq]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hN, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact hj ▸ hν.monotone (Nat.zero_le j)

theorem support_strictMono_range_sInf (ν : ℕ → ℕ) (hν : StrictMono ν) :
    sInf (range ν) = ν 0 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨0, rfl⟩
  · obtain ⟨j, hj⟩ := Nat.sInf_mem (Set.range_nonempty ν)
    exact hj ▸ hν.monotone (Nat.zero_le j)

theorem support_infinite_strictMono_range (ν : ℕ → ℕ) (hν : StrictMono ν) :
    (range ν).Infinite := Set.infinite_range_of_injective hν.injective

theorem support_tail_infinite (Q : Set ℕ) (hQ : Q.Infinite) :
    (Q \ {sInf Q}).Infinite := hQ.diff (finite_singleton _)

theorem support_infinite_enumeration (Q : Set ℕ) (hQ : Q.Infinite) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ range ν = Q := by
  classical
  letI : Infinite Q := hQ.to_subtype
  exact ⟨Nat.orderEmbeddingOfSet Q, (Nat.orderEmbeddingOfSet Q).strictMono,
    Nat.orderEmbeddingOfSet_range Q⟩

end SurveyStatements.P1
