import ThesisCommon.Analysis.LpFiniteProducts
import ThesisCommon.Analysis.ScalarLpPrimary
import ThesisCommon.Analysis.PrimaryIsomorphism

/-! The finite and empty compact-space cases. For nonempty finite K, actual
continuous functions identify with the finite maximum-norm coefficient space;
the countable lp sum of that coefficient space is isomorphic to scalar lp.
The empty case is the zero space. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K] [Finite K]

def finiteContinuousMapRead [Fintype K] : C(K, 𝕜) →L[𝕜] (K → 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun f => fun x => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by
      simp only [one_mul]
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2 f.norm_coe_le_norm)

def finiteContinuousMapInsert [Fintype K] : (K → 𝕜) →L[𝕜] C(K, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨f, continuous_of_discreteTopology⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by
      simp only [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg f)).2 (fun x => norm_le_pi_norm f x))

def finiteContinuousMapEquiv [Fintype K] : C(K, 𝕜) ≃L[𝕜] (K → 𝕜) :=
  ContinuousLinearEquiv.equivOfInverse (finiteContinuousMapRead K)
    (finiteContinuousMapInsert K)
    (by intro f; ext x; rfl) (by intro f; rfl)

def finiteCompactLpEquivScalar [Fintype K] [Nonempty K]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    lp (fun _ : ℕ => C(K, 𝕜)) p ≃L[𝕜] lp (fun _ : ℕ => 𝕜) p :=
  (lpMapEquiv p (finiteContinuousMapEquiv K)).trans (lpCountableFinitePiCoefficientEquiv p)

theorem finiteCompact_lp_upfp_primary (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    HasUPFP 𝕜 (lp (fun _ : ℕ => C(K, 𝕜)) p) ∧
      IsPrimary 𝕜 (lp (fun _ : ℕ => C(K, 𝕜)) p) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  by_cases hK : Nonempty K
  · letI : Nonempty K := hK
    have h := (scalar_lp_hasUPFP (𝕜 := 𝕜) p).of_equiv (finiteCompactLpEquivScalar K p).symm
    exact ⟨h, h.lp_isPrimary⟩
  · letI : IsEmpty K := not_nonempty_iff.mp hK
    letI : Subsingleton C(K, 𝕜) := ⟨fun f g => by ext x; exact isEmptyElim x⟩
    letI : Subsingleton (lp (fun _ : ℕ => C(K, 𝕜)) p) :=
      ⟨fun f g => by ext n x; exact isEmptyElim x⟩
    have h : HasUPFP 𝕜 (lp (fun _ : ℕ => C(K, 𝕜)) p) := hasUPFP_of_subsingleton
    exact ⟨h, h.lp_isPrimary⟩

theorem finiteCompact_sequence_upfp_primary (p : BanachExponent) :
    HasUPFP 𝕜 (SequenceSum p C(K, 𝕜)) ∧ IsPrimary 𝕜 (SequenceSum p C(K, 𝕜)) :=
  finiteCompact_lp_upfp_primary K p.val

end ThesisCommon

