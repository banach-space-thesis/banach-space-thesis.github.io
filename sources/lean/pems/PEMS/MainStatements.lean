import PEMS.Definitions

/-! Exact main-result targets, not asserted theorems.
Source: Acuaviva--Nasseri, Quantifying (non-)weak compactness of operators on
AL- and C(K)-spaces, final author manuscript dated 20 January 2026, pp. 2--5;
numbering agrees with the local annotated PEMS production proof.
All scalar-generic statements range over real or complex scalars. -/
noncomputable section
namespace PEMS
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Theorem 1.1, p. 2: a best weakly compact approximant exists, and the
weak essential norm is the infimum of the localized limsups. Both equalities
and both strictly localizable hypotheses are retained. -/
def Theorem_1_1 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : MeasureTheory.Measure X) (ν : MeasureTheory.Measure Y)
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) : Prop :=
  StrictlyLocalizable μ → StrictlyLocalizable ν →
    ∃ W : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν, IsWeaklyCompactOperator W ∧
      weakEssentialNorm T = ‖T - W‖ ∧ ‖T - W‖ = localizedWeakNoncompactness T

/-- Corollary 1.2, p. 2: for compact Hausdorff K,L and extremally disconnected
L, a best weakly compact approximant exists and ‖T*‖_w = ‖T‖_w. -/
def Corollary_1_2 (K L : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace L] [CompactSpace L] [T2Space L]
    (T : C(K, 𝕜) →L[𝕜] C(L, 𝕜)) : Prop :=
  ExtremallyDisconnected L →
    ∃ W : C(K, 𝕜) →L[𝕜] C(L, 𝕜), IsWeaklyCompactOperator W ∧
      dualWeakEssentialNorm T = weakEssentialNorm T ∧ weakEssentialNorm T = ‖T - W‖

section AL
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- Theorem 1.4, p. 3: for AL-spaces E,F, ‖T‖_w = sup 1/(‖U‖‖V‖)
over UTV=I_ℓ¹. The Banach-lattice hypothesis is defined intrinsically; no
Kakutani representation or factorization is assumed. -/
def Theorem_1_4 [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F) : Prop :=
  IsALSpace 𝕜 E → IsALSpace 𝕜 F → weakEssentialNorm T = factorizationSup (EllOne 𝕜) T

/-- Corollary 1.7, p. 3: the actual weak Calkin algebra of any AL-space admits
a unique algebra norm up to equivalence, with no completeness restriction. -/
def Corollary_1_7 [CompleteSpace E] : Prop :=
  IsALSpace 𝕜 E → HasUniqueWeakCalkinAlgebraNorm 𝕜 E

/-- Corollary 1.11, p. 4: the weak essential norm on the weak Calkin algebra
of an AL-space has Bonsall minimality. Includes descent and normhood. -/
def Corollary_1_11 [CompleteSpace E] : Prop :=
  IsALSpace 𝕜 E → HasBonsallWeakCalkinMinimality 𝕜 E weakEssentialNorm
end AL

/-- Theorem 1.5, p. 3, ALL THREE clauses: the c₀ minimum-modulus formula;
c₀ factorization if the range compactum K is sequentially compact; ℓ∞
factorization if the domain compactum L is extremally disconnected. -/
def Theorem_1_5 (K L : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace L] [CompactSpace L] [T2Space L]
    (T : C(L, 𝕜) →L[𝕜] C(K, 𝕜)) : Prop :=
  dualWeakEssentialNorm T = fixesCZeroSup T ∧
    (SeqCompactSpace K → dualWeakEssentialNorm T = factorizationSup (CZero 𝕜) T) ∧
    (ExtremallyDisconnected L → dualWeakEssentialNorm T = factorizationSup (EllInfinity 𝕜) T)

/-- Corollary 1.8, pp. 3--4: weak essential norm minimality for C(L) when
L is extremally disconnected and compact Hausdorff. -/
def Corollary_1_8 (L : Type*) [TopologicalSpace L] [CompactSpace L] [T2Space L] : Prop :=
  ExtremallyDisconnected L → IsMinimalWeakCalkinNorm 𝕜 C(L, 𝕜) weakEssentialNorm

/-- Corollary 1.9, p. 4: DUAL weak essential norm minimality for C(K) when
K is sequentially compact and compact Hausdorff. -/
def Corollary_1_9 (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K] : Prop :=
  SeqCompactSpace K → IsMinimalWeakCalkinNorm 𝕜 C(K, 𝕜) dualWeakEssentialNorm

/-- Corollary 1.12, p. 4: Bonsall minimality of the weak essential norm on
the weak Calkin algebra of C(L), L extremally disconnected compact Hausdorff. -/
def Corollary_1_12 (L : Type*) [TopologicalSpace L] [CompactSpace L] [T2Space L] : Prop :=
  ExtremallyDisconnected L → HasBonsallWeakCalkinMinimality 𝕜 C(L, 𝕜) weakEssentialNorm

/-- Corollary 1.13, p. 4: Bonsall minimality of the DUAL weak essential norm
on the weak Calkin algebra of C(K), K sequentially compact compact Hausdorff. -/
def Corollary_1_13 (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K] : Prop :=
  SeqCompactSpace K → HasBonsallWeakCalkinMinimality 𝕜 C(K, 𝕜) dualWeakEssentialNorm

/-- Theorem 1.14, p. 5: all four quantities agree on actual L∞[0,1].
The residuum is constructed on E**/J(E), and De Blasi uses weak compactness. -/
def Theorem_1_14 (T : LInfinityUnitInterval 𝕜 →L[𝕜] LInfinityUnitInterval 𝕜) : Prop :=
  weakEssentialNorm T = dualWeakEssentialNorm T ∧
    dualWeakEssentialNorm T = residuumNorm T ∧
    residuumNorm T = deBlasiOperator T

end PEMS
