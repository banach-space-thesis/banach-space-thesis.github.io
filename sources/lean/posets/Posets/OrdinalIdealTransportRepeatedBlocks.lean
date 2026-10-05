import Posets.OrdinalIdealTransportFamilyScalars
import Posets.OrdinalIdealTransportBlockCompression

/-! Every operator on countably many copies of a regular initial ordinal
C-space has a common compression whose matrix consists of scalar multiples
of the identity. Those scalars form an actual bounded operator on c₀. -/
noncomputable section
namespace Posets
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

local instance repeatedSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance repeatedSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance

theorem exists_repeatedRegularOrdinal_scalar_blocks
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : CZeroSum 𝕜 (fun _ : ℕ => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : ℕ => OrdinalC 𝕜 c.ord)) :
    ∃ L R : CZeroSum 𝕜 (fun _ : ℕ => OrdinalC 𝕜 c.ord) →L[𝕜]
        CZeroSum 𝕜 (fun _ : ℕ => OrdinalC 𝕜 c.ord),
      L.comp R = ContinuousLinearMap.id 𝕜 _ ∧ ‖L‖ ≤ 4 ∧ ‖R‖ ≤ 2 ∧
      ∃ A : CZeroSum 𝕜 (fun _ : ℕ => 𝕜) →L[𝕜] CZeroSum 𝕜 (fun _ : ℕ => 𝕜),
        ∀ i j f, L (T (R (CZeroSum.single j f))) i =
          A (CZeroSum.single j 1) i • f := by
  let B (i j : ℕ) : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
    (CZeroSum.evalCLM i).comp (T.comp (CZeroSum.singleIsometry j).toContinuousLinearMap)
  obtain ⟨l, r, hlr, hl, hr, _, hscalar⟩ :=
    exists_initialOrdinal_scalar_countable_compression hc hu (fun ij : ℕ × ℕ => B ij.1 ij.2)
  let L := CZeroSum.mapCLM (fun _ : ℕ => l) (by norm_num : (0:ℝ) ≤ 4) (fun _ => hl)
  let R := CZeroSum.mapCLM (fun _ : ℕ => r) (by norm_num : (0:ℝ) ≤ 2) (fun _ => hr)
  let a (i j : ℕ) := initialEndpointJump (𝕜 := 𝕜) hc hu (B i j)
  have hcol (i j : ℕ) (f : OrdinalC 𝕜 c.ord) :
      L (T (R (CZeroSum.single j f))) i = a i j • f := by
    change l (T (R (CZeroSum.single j f)) i) = _
    rw [cZeroSum_mapCLM_single]
    exact congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V f)
      (hscalar (i,j))
  let J₀ : 𝕜 →L[𝕜] OrdinalC 𝕜 c.ord := ContinuousLinearMap.const 𝕜 (OrdinalInterval c.ord)
  let Q₀ : OrdinalC 𝕜 c.ord →L[𝕜] 𝕜 :=
    ContinuousMap.evalCLM 𝕜 ⟨0, le_rfl, Ordinal.zero_le _⟩
  have hJ₀ : ‖J₀‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg z)).mpr (fun _ => le_rfl)
  have hQ₀ : ‖Q₀‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    simpa only [one_mul] using f.norm_coe_le_norm ⟨0, le_rfl, Ordinal.zero_le _⟩
  let J := CZeroSum.mapCLM (fun _ : ℕ => J₀) zero_le_one (fun _ => hJ₀)
  let Q := CZeroSum.mapCLM (fun _ : ℕ => Q₀) zero_le_one (fun _ => hQ₀)
  let A : CZeroSum 𝕜 (fun _ : ℕ => 𝕜) →L[𝕜] CZeroSum 𝕜 (fun _ : ℕ => 𝕜) :=
    Q.comp (L.comp (T.comp (R.comp J)))
  have hJ (j : ℕ) : J (CZeroSum.single j (1 : 𝕜)) = CZeroSum.single j (J₀ 1) := by
    classical
    apply CZeroSum.ext
    intro i
    by_cases hi : i = j
    · subst i
      simp [J]
    · simp only [J, CZeroSum.mapCLM_apply, CZeroSum.single_apply_ne _ _ hi, map_zero]
  have hA (i j : ℕ) : A (CZeroSum.single j 1) i = a i j := by
    change Q₀ (L (T (R (J (CZeroSum.single j 1)))) i) = _
    rw [hJ, hcol]
    change a i j * 1 = a i j
    exact mul_one _
  refine ⟨L, R, ?_, CZeroSum.norm_mapCLM_le _ _ _, CZeroSum.norm_mapCLM_le _ _ _, A, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply CZeroSum.ext
    intro i
    exact congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V (x i)) hlr
  · intro i j f
    rw [hcol, hA]

end Posets
