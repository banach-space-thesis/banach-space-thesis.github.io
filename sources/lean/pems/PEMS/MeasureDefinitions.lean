import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section
open MeasureTheory Set
namespace PEMS
universe u

/-- Definition 3.3: arbitrary measurable disjoint finite-measure decomposition,
including the local criterion for measurability and the uncountable measure sum.
Index by subsets of X to avoid an artificial bound on the cardinality of pieces. -/
def StrictlyLocalizable {X : Type u} [MeasurableSpace X] (μ : Measure X) : Prop :=
  ∃ parts : Set (Set X),
    (∀ A ∈ parts, MeasurableSet A ∧ μ A < ⊤) ∧
    parts.Pairwise Disjoint ∧
    (⋃ A ∈ parts, A) = univ ∧
    (∀ A : Set X, MeasurableSet A ↔ ∀ B ∈ parts, MeasurableSet (A ∩ B)) ∧
    (∀ A : Set X, MeasurableSet A → μ A = ∑' B : parts, μ (A ∩ B.val))

abbrev LOne (𝕜 : Type*) [RCLike 𝕜] {X : Type*} [MeasurableSpace X] (μ : Measure X) :=
  Lp 𝕜 1 μ

/-- L∞[0,1] on the actual restricted Lebesgue measure. Values outside the
interval are null, so this is canonically the usual space on [0,1]. -/
abbrev LInfinityUnitInterval (𝕜 : Type*) [RCLike 𝕜] :=
  Lp 𝕜 ⊤ (volume.restrict (Icc (0 : ℝ) 1))

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

/-- Expanded operator norm of multiplication by 1_A after T, using actual L¹
functions modulo null sets. For measurable A it is ‖χ_A T‖. The union in
alphaTheta is disjoint, giving χ_(Y\Θ) T + χ_B T. -/
def cutOperatorNorm (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (A : Set Y) : ℝ :=
  sSup {r : ℝ | ∃ f : LOne 𝕜 μ, ‖f‖ ≤ 1 ∧
    r = (eLpNorm (A.indicator (T f)) 1 ν).toReal}

/-- Supremum over all measurable B⊆Θ with ν(B)<δ. -/
def smallSetSup (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (Θ : Set Y) (δ : ℝ) : ℝ :=
  sSup {q : ℝ | ∃ B : Set Y, MeasurableSet B ∧ B ⊆ Θ ∧
    ν B < ENNReal.ofReal δ ∧ q = cutOperatorNorm T (Θᶜ ∪ B)}

/-- The limsup over measurable B⊆Θ with ν(B)→0, expanded as inf_(δ>0) sup.
No sequence/cofinality assumption or finite-measure assumption on Y is added. -/
def alphaTheta (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (Θ : Set Y) : ℝ :=
  sInf {r : ℝ | ∃ δ : ℝ, 0 < δ ∧ r = smallSetSup T Θ δ}

/-- Infimum over all measurable finite-measure localizations, including ∅. -/
def localizedWeakNoncompactness (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) : ℝ :=
  sInf {r : ℝ | ∃ Θ : Set Y, MeasurableSet Θ ∧ ν Θ < ⊤ ∧ r = alphaTheta T Θ}

end PEMS
