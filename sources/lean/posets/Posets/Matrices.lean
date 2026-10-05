import Posets.Models
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Sections 4.2–4.3. Row summability is explicit: Lean's totalised tsum
would otherwise assign zero to divergent rows and accept invalid matrices. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped ZeroAtInfty
namespace Posets
variable (𝕜 : Type*) [RCLike 𝕜]

abbrev ScalarMatrix := ℕ → ℕ → 𝕜

def HasBoundedRows (M : ScalarMatrix 𝕜) : Prop :=
  (∀ k, Summable (fun n => ‖M k n‖)) ∧
  ∃ C : ℝ, ∀ k, (∑' n, ‖M k n‖) ≤ C

def matrixNorm (M : ScalarMatrix 𝕜) : ℝ := ⨆ k, ∑' n, ‖M k n‖
def matrixAction (M : ScalarMatrix 𝕜) (f : ℕ → 𝕜) (k : ℕ) : 𝕜 := ∑' n, M k n * f n
def identityMatrix : ScalarMatrix 𝕜 := fun k n => if k = n then 1 else 0
def indicator (A : Set ℕ) : ℕ → 𝕜 := A.indicator (fun _ => 1)

/-- Convergence along the increasing enumeration of an infinite subset of ℕ,
written with the equivalent restricted cofinite filter. -/
def Along (A : Set ℕ) : Filter ℕ := Filter.cofinite ⊓ Filter.principal A

def Admits (𝒜 ℬ : Set (Set ℕ)) (M : ScalarMatrix 𝕜) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ ℬ, Tendsto (matrixAction 𝕜 M (indicator 𝕜 A)) (Along B) (𝓝 0)

def Rejects (A B : Set ℕ) (M : ScalarMatrix 𝕜) : Prop :=
  ¬ ∃ a : 𝕜, Tendsto (matrixAction 𝕜 M (indicator 𝕜 A)) (Along B) (𝓝 a)

def Undermines (A : Set ℕ) (M : ScalarMatrix 𝕜) : Prop :=
  ∃ n : ℕ, ¬ Tendsto (matrixAction 𝕜 M (indicator 𝕜 {n})) (Along A) (𝓝 0)

def matrixTail (M : ScalarMatrix 𝕜) (j : ℕ) : ScalarMatrix 𝕜 :=
  fun k n => if j < n then M k n else 0

def matrixRestriction (M : ScalarMatrix 𝕜) (A B : Set ℕ) : ScalarMatrix 𝕜 :=
  fun k n => if k ∈ B ∧ n ∈ A then M k n else 0

/-- Compact MATRIX means uniformly small column tails, not compactness of
an arbitrary map ℓ∞→ℓ∞. The paper distinguishes these notions. -/
def IsCompactMatrix (M : ScalarMatrix 𝕜) : Prop :=
  HasBoundedRows 𝕜 M ∧
  Tendsto (fun j => matrixNorm 𝕜 (matrixTail 𝕜 M j)) atTop (𝓝 0)

def AcceptsPair (A B : Set ℕ) (M : ScalarMatrix 𝕜) : Prop :=
  IsCompactMatrix 𝕜 (matrixRestriction 𝕜 M A B)

def Accepts (𝒜 ℬ : Set (Set ℕ)) (M : ScalarMatrix 𝕜) : Prop :=
  ∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, ∀ B ∈ ℬ, ∀ B' ∈ ℬ,
    AcceptsPair 𝕜 (A ∪ A') (B ∪ B') M

theorem isolated_open (𝒜 : Set (Set ℕ)) (n : ℕ) :
    IsOpen ({Sum.inl n} : Set (Mrowka 𝒜)) :=
  TopologicalSpace.isOpen_generateFrom_of_mem (Or.inl ⟨n, rfl⟩)

theorem neighborhood_open (𝒜 : Set (Set ℕ)) (A : 𝒜) (F : Finset ℕ) :
    IsOpen (JFA.mrowkaNeighborhood 𝒜 A F) :=
  TopologicalSpace.isOpen_generateFrom_of_mem (Or.inr ⟨A, F, rfl⟩)

/-- Isolated natural-number points are compact and clopen, even without the
almost-disjointness hypothesis. -/
theorem isolated_clopen (𝒜 : Set (Set ℕ)) (n : ℕ) :
    IsClopen ({Sum.inl n} : Set (Mrowka 𝒜)) := by
  refine ⟨?_, isolated_open 𝒜 n⟩
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  intro p hp
  rcases p with m | A
  · apply Filter.mem_of_superset ((isolated_open 𝒜 m).mem_nhds (Set.mem_singleton _))
    intro q hq
    simpa only [Set.mem_singleton_iff.mp hq] using hp
  · have hm : Sum.inr A ∈ JFA.mrowkaNeighborhood 𝒜 A {n} := Or.inl rfl
    apply Filter.mem_of_superset ((neighborhood_open 𝒜 A {n}).mem_nhds hm)
    rintro q (hq | ⟨m, _, hmn, hq⟩)
    · simp [hq]
    · simp only [Finset.mem_singleton] at hmn
      rw [hq]
      exact fun h => hmn (Sum.inl.inj h)

/-- 1_{x_n}, used to define the reduced matrix without assuming Rudin's theorem. -/
def isolatedVector (𝒜 : Set (Set ℕ)) (n : ℕ) : Space 𝕜 𝒜 where
  toFun := ({Sum.inl n} : Set (Mrowka 𝒜)).indicator (fun _ => 1)
  continuous_toFun := continuous_indicator (by simp [isolated_clopen 𝒜 n])
    continuous_const.continuousOn
  zero_at_infty' := by
    apply tendsto_const_nhds.congr'
    have hc : IsCompact ({Sum.inl n} : Set (Mrowka 𝒜)) := isCompact_singleton
    filter_upwards [hc.compl_mem_cocompact] with x hx
    exact (Set.indicator_of_notMem hx _).symm

@[simp] theorem isolatedVector_natural (𝒜 : Set (Set ℕ)) (n k : ℕ) :
    isolatedVector 𝕜 𝒜 n (Sum.inl k) = if k = n then 1 else 0 := by
  change ({Sum.inl n} : Set (Mrowka 𝒜)).indicator (fun _ => (1 : 𝕜)) (Sum.inl k) = _
  by_cases h : k = n
  · subst k
    rw [if_pos rfl]
    exact Set.indicator_of_mem (Set.mem_singleton _) _
  · rw [if_neg h]
    apply Set.indicator_of_notMem
    intro hx
    exact h (Sum.inl.inj (Set.mem_singleton_iff.mp hx))

@[simp] theorem isolatedVector_family (𝒜 : Set (Set ℕ)) (n : ℕ) (A : 𝒜) :
    isolatedVector 𝕜 𝒜 n (Sum.inr A) = 0 := by
  simp [isolatedVector]

/-- m_kn = (T 1_{x_n})(z_k), the singleton-mass expression for T*δ_zk.
This is an actual coefficient of T, not a supplied matrix-representation interface. -/
def reducedMatrix {𝒜 ℬ : Set (Set ℕ)} (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) : ScalarMatrix 𝕜 :=
  fun k n => T (isolatedVector 𝕜 𝒜 n) (Sum.inl k)

@[simp] theorem reducedMatrix_add {𝒜 ℬ : Set (Set ℕ)}
    (S T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) :
    reducedMatrix 𝕜 (S + T) = reducedMatrix 𝕜 S + reducedMatrix 𝕜 T := rfl

@[simp] theorem reducedMatrix_smul {𝒜 ℬ : Set (Set ℕ)}
    (a : 𝕜) (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) :
    reducedMatrix 𝕜 (a • T) = a • reducedMatrix 𝕜 T := rfl

@[simp] theorem reducedMatrix_sub {𝒜 ℬ : Set (Set ℕ)}
    (S T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) :
    reducedMatrix 𝕜 (S - T) = reducedMatrix 𝕜 S - reducedMatrix 𝕜 T := rfl

theorem reducedMatrix_id (𝒜 : Set (Set ℕ)) :
    reducedMatrix 𝕜 (ContinuousLinearMap.id 𝕜 (Space 𝕜 𝒜)) = identityMatrix 𝕜 := by
  funext k n
  exact isolatedVector_natural 𝕜 𝒜 n k

end Posets
