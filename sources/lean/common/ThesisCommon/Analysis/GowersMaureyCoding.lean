import ThesisCommon.Analysis.GowersMaureyFiniteSequences
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Literal finite-sequence data from Gowers--Maurey, *Banach Spaces with
Small Spaces of Operators*, printed p. 8. Indices of the sequence j start
at zero here; hence the source's j_(2k) is `j (2*k-1)`.
For complex scalars, rational coordinates mean Gaussian rational coordinates.
No operator-theoretic conclusion is included in these construction data.
-/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def Before (a b : C00 𝕜) : Prop :=
  ∀ s ∈ a.support, ∀ t ∈ b.support, s < t

def Successive {k : ℕ} (a : Fin k → C00 𝕜) : Prop :=
  ∀ i j, i < j → Before (a i) (a j)

def RationalCoordinate (c : 𝕜) : Prop :=
  ∃ r s : ℚ, c = (r : 𝕜) + (s : 𝕜) * RCLike.I

def RationalUnitSequence (x : C00 𝕜) : Prop :=
  (∀ n, RationalCoordinate (x n)) ∧ ∀ n, ‖x n‖ ≤ 1

def CodingDomain (xs : List (C00 𝕜)) : Prop :=
  (∀ x ∈ xs, RationalUnitSequence x) ∧ xs.Pairwise Before

/-- The free choices J and σ made before defining the implicit norm. -/
structure ConstructionData (𝕜 : Type*) [RCLike 𝕜] where
  j : ℕ → ℕ
  j_strict : StrictMono j
  j_positive : ∀ n, 0 < j n
  rapid : ∀ m n, m < n →
    (2 * j m : ℝ) < Real.log (Real.log (Real.log (j n : ℝ)))
  first_large : 256 < logarithmicWeight (j 0)
  sigma : List (C00 𝕜) → ℕ
  sigma_injective : Set.InjOn sigma CodingDomain
  sigma_even : ∀ xs, CodingDomain xs → ∃ n, sigma xs = j (2 * n + 1)

def ConstructionData.specialSizes (D : ConstructionData 𝕜) : Set ℕ :=
  Set.range (fun n => D.j (2 * n))

theorem ConstructionData.specialSize_pos (D : ConstructionData 𝕜)
    {k : ℕ} (hk : k ∈ D.specialSizes) : 0 < k := by
  obtain ⟨n, rfl⟩ := hk
  exact D.j_positive _

/-- Dual-unit-ball membership is an actual inequality on every finite vector. -/
def DualUnit (p : Seminorm 𝕜 (C00 𝕜)) (a : C00 𝕜) : Prop :=
  ∀ x, ‖pairing a x‖ ≤ p x

/-- The source's A_m^*(X), with its positive integer parameter explicit. -/
def AveragedFunctional (p : Seminorm 𝕜 (C00 𝕜)) (m : ℕ) (a : C00 𝕜) : Prop :=
  0 < m ∧ ∃ z : Fin m → C00 𝕜,
    Successive z ∧ (∀ i, DualUnit p (z i)) ∧
      a = (logarithmicWeight (m : ℝ))⁻¹ • ∑ i, z i

def initialSegment {k : ℕ} (g : Fin k → C00 𝕜) (i : Fin k) : List (C00 𝕜) :=
  List.ofFn (fun t : Fin i.val => g ⟨t.val, t.isLt.trans i.isLt⟩)

/-- Γ_k^X, including its rationality, order and recursive σ clauses. -/
def SpecialSequence (D : ConstructionData 𝕜) (p : Seminorm 𝕜 (C00 𝕜))
    {k : ℕ} (g : Fin k → C00 𝕜) : Prop :=
  Successive g ∧ (∀ i, RationalUnitSequence (g i)) ∧
    ∀ i, AveragedFunctional p
      (if i.val = 0 then D.j (2 * k - 1) else D.sigma (initialSegment g i)) (g i)

/-- The finite functional in B_k^*(X). -/
def specialFunctional {k : ℕ} (g : Fin k → C00 𝕜) : C00 𝕜 :=
  (Real.sqrt (logarithmicWeight (k : ℝ)))⁻¹ • ∑ i, g i

theorem dualUnit_mono {p q : Seminorm 𝕜 (C00 𝕜)} (hpq : p ≤ q)
    {a : C00 𝕜} (ha : DualUnit p a) : DualUnit q a :=
  fun x => (ha x).trans (hpq x)

theorem averagedFunctional_mono {p q : Seminorm 𝕜 (C00 𝕜)} (hpq : p ≤ q)
    {m : ℕ} {a : C00 𝕜} (ha : AveragedFunctional p m a) : AveragedFunctional q m a := by
  obtain ⟨hm, z, hz, hu, rfl⟩ := ha
  exact ⟨hm, z, hz, fun i => dualUnit_mono hpq (hu i), rfl⟩

theorem specialSequence_mono (D : ConstructionData 𝕜)
    {p q : Seminorm 𝕜 (C00 𝕜)} (hpq : p ≤ q)
    {k : ℕ} {g : Fin k → C00 𝕜} (hg : SpecialSequence D p g) :
    SpecialSequence D q g :=
  ⟨hg.1, hg.2.1, fun i => averagedFunctional_mono hpq (hg.2.2 i)⟩

end ThesisCommon.GowersMaurey
