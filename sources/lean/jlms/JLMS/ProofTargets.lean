import JLMS.CZeroTools
import JLMS.AtomicDual
import JLMS.Factorization
import JLMS.ScatteredTopology

/-!
# Named proof obligations along the paper's argument

The definitions here are propositions or data structures; by themselves they
assert no existence and introduce no axioms. The theorems check consequences
and assembly steps from explicit inputs. The graph records which targets
are discharged and which analytic inputs remain open.
-/

noncomputable section

attribute [local instance] Classical.decEq

namespace JLMS

variable (𝕜 : Type*) [RCLike 𝕜]
variable (K : Type*) [TopologicalSpace K]

/-- The compact clopen local base used throughout Sections 4–6. -/
def CompactClopenNeighborhoodBasis [LocallyCompactSpace K] [T2Space K] : Prop :=
  IsScattered K → ∀ x : K, ∀ O : Set K, IsOpen O → x ∈ O →
    ∃ U : Set K, IsClopen U ∧ IsCompact U ∧ x ∈ U ∧ U ⊆ O

/-- The compact clopen base target is discharged by the Section 4 topology proof. -/
theorem compactClopenNeighborhoodBasis [LocallyCompactSpace K] [T2Space K] :
    CompactClopenNeighborhoodBasis K := by
  intro hK x O hO hx
  exact exists_compact_clopen_subset hK hO hx

variable {𝕜 K}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The disjoint functions constructed in Theorem 3.3 and its Section 7 variant. -/
def DisjointFunctionWitnesses (T : CZero 𝕜 K →L[𝕜] X) (δ : ℝ) : Prop :=
  ∃ η : ℕ → CZero 𝕜 K,
    (∀ j, ‖η j‖ ≤ 1) ∧
    (Pairwise fun i j => Disjoint (Function.support (η i)) (Function.support (η j))) ∧
    ∀ j, δ < ‖T (η j)‖

/-- A strict UNIFORM margin above δ, as required by inf_j ‖Tη_j‖ > δ.
Pointwise strict inequalities at δ alone would be insufficient. The existence
of a larger threshold is the form of the strict infimum condition used here. -/
def UniformDisjointFunctionWitnesses (T : CZero 𝕜 K →L[𝕜] X) (δ : ℝ) : Prop :=
  ∃ γ : ℝ, δ < γ ∧ DisjointFunctionWitnesses T γ

/-- Recover the two exact analytic conditions from the cited theorem:
the pointwise sum bound and the strictly larger infimum. -/
theorem arnottLaustsen_conditions_of_uniform
    (T : CZero 𝕜 K →L[𝕜] X) (δ : ℝ) (h : UniformDisjointFunctionWitnesses T δ) :
    ∃ η : ℕ → CZero 𝕜 K,
      (∀ k : K, (∑' j, ‖η j k‖) ≤ 1) ∧
      δ < sInf (Set.range fun j => ‖T (η j)‖) := by
  obtain ⟨γ, hδγ, η, hunit, hdisjoint, hlarge⟩ := h
  refine ⟨η, pointwise_tsum_norm_le_one_of_disjoint η hunit hdisjoint, ?_⟩
  apply lt_of_lt_of_le hδγ
  apply le_csInf (show (Set.range fun j => ‖T (η j)‖).Nonempty from ⟨_, ⟨0, rfl⟩⟩)
  rintro r ⟨j, rfl⟩
  exact (hlarge j).le

/-- Theorem 3.3 in normalized form, exactly the threshold that leads to factor 2. -/
def DisjointFunctionsHalf [LocallyCompactSpace K] [T2Space K] [CompleteSpace X] : Prop :=
  IsScattered K → ∀ T : CZero 𝕜 K →L[𝕜] X, essentialNorm T = 1 →
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → DisjointFunctionWitnesses T δ

/-- The stronger disjoint-function construction in Section 7. -/
def DisjointFunctionsSharp [LocallyCompactSpace K] [T2Space K] [CompleteSpace X] : Prop :=
  IsScattered K → ∀ T : CZero 𝕜 K →L[𝕜] X,
    ∀ δ : ℝ, 0 < δ → δ < dualEssentialNorm T → DisjointFunctionWitnesses T δ

/-- The part of the cited Arnott–Laustsen/Hagler–Johnson machinery needed
after the paper constructs disjoint functions. Proving this combined interface
still requires implementing those cited results and the codomain disjunction. -/
def FactorizationFromDisjointFunctions [LocallyCompactSpace K] [T2Space K]
    [CompleteSpace X] : Prop :=
  AdmissibleCodomain 𝕜 X → ∀ T : CZero 𝕜 K →L[𝕜] X,
    ∀ δ : ℝ, 0 < δ → UniformDisjointFunctionWitnesses T δ →
    ∃ U : X →L[𝕜] cZero 𝕜, ∃ V : cZero 𝕜 →L[𝕜] CZero 𝕜 K,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧
      ‖U‖ * ‖V‖ < 1 / δ

/-- Composing the two outstanding analytic constructions yields the sharp
factorizations required by the proved supremum argument. -/
theorem sharpFactorizations_of_disjointFunctions
    [LocallyCompactSpace K] [T2Space K] [CompleteSpace X]
    (hfunctions : DisjointFunctionsSharp (𝕜 := 𝕜) (K := K) (X := X))
    (hfactor : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := X))
    (hK : IsScattered K) (hX : AdmissibleCodomain 𝕜 X)
    (T : CZero 𝕜 K →L[𝕜] X) : SharpFactorizations (𝕜 := 𝕜) T := by
  intro δ hδ hδT
  let γ := (δ + dualEssentialNorm T) / 2
  have hδγ : δ < γ := by dsimp [γ]; linarith
  have hγ : 0 < γ := hδ.trans hδγ
  have hγT : γ < dualEssentialNorm T := by dsimp [γ]; linarith
  exact hfactor hX T δ hδ ⟨γ, hδγ, hfunctions hK T γ hγ hγT⟩

/-- The final normalization and strict epsilon estimate for Theorem 1.6.
The two substantial analytic results remain explicit parameters. -/
theorem theorem_1_6_of_disjointFunctions
    [LocallyCompactSpace K] [T2Space K] [CompleteSpace X]
    (hfunctions : DisjointFunctionsHalf (𝕜 := 𝕜) (K := K) (X := X))
    (hfactor : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := X)) :
    Theorem_1_6 𝕜 K X := by
  intro hK hX T hT ε hε
  have he : 0 < essentialNorm T := essentialNorm_pos hT
  let a : 𝕜 := ((essentialNorm T)⁻¹ : ℝ)
  have ha : ‖a‖ = (essentialNorm T)⁻¹ := by
    change ‖(((essentialNorm T)⁻¹ : ℝ) : 𝕜)‖ = (essentialNorm T)⁻¹
    rw [RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr he.le)]
  have hnormalized : essentialNorm (a • T) = 1 := by
    rw [essentialNorm_smul, ha, inv_mul_cancel₀ (ne_of_gt he)]
  let δ : ℝ := 1 / (2 + ε * essentialNorm T / 2)
  have hden : 0 < 2 + ε * essentialNorm T / 2 := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  have hδhalf : δ < 1 / 2 := by
    apply one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2)
    nlinarith
  let γ := (δ + 1 / 2) / 2
  have hδγ : δ < γ := by dsimp [γ]; linarith
  have hγ : 0 < γ := hδ.trans hδγ
  have hγhalf : γ < 1 / 2 := by dsimp [γ]; linarith
  obtain ⟨U, V, hidentity, hproduct⟩ :=
    hfactor hX (a • T) δ hδ
      ⟨γ, hδγ, hfunctions hK (a • T) hnormalized γ hγ hγhalf⟩
  letI : NormSMulClass 𝕜 (X →L[𝕜] cZero 𝕜) :=
    @NormedSpace.toNormSMulClass 𝕜 (X →L[𝕜] cZero 𝕜) _ _ _
  refine ⟨a • U, V, ?_, ?_⟩
  · have heq : ((a • U).comp T).comp V = (U.comp (a • T)).comp V := by
      ext x
      simp
    rw [heq]
    exact hidentity
  · rw [norm_smul, ha]
    have hinv : 0 < (essentialNorm T)⁻¹ := inv_pos.mpr he
    have hdeltainv : 1 / δ = 2 + ε * essentialNorm T / 2 := by
      simp [δ]
    rw [hdeltainv] at hproduct
    calc
      ((essentialNorm T)⁻¹ * ‖U‖) * ‖V‖ =
          (essentialNorm T)⁻¹ * (‖U‖ * ‖V‖) := by ring
      _ < (essentialNorm T)⁻¹ * (2 + ε * essentialNorm T / 2) :=
        mul_lt_mul_of_pos_left hproduct hinv
      _ = 2 / essentialNorm T + ε / 2 := by field_simp
      _ < 2 / essentialNorm T + ε := by linarith

/-- Assembly of the full statement of Theorem 1.7 from the named open targets
and the already checked supremum argument. -/
theorem theorem_1_7_of_disjointFunctions
    [LocallyCompactSpace K] [T2Space K] [CompleteSpace X]
    (hfunctions : DisjointFunctionsSharp (𝕜 := 𝕜) (K := K) (X := X))
    (hfactor : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := X))
    (hpositive : ∀ T : CZero 𝕜 K →L[𝕜] X,
      ¬ IsCompactOperator T → 0 < dualEssentialNorm T) :
    Theorem_1_7 𝕜 K X := by
  intro hK hX T hT
  exact factorizationValues_isLUB_of_sharp_cZero T (hpositive T hT)
    (sharpFactorizations_of_disjointFunctions hfunctions hfactor hK hX T)

end JLMS
