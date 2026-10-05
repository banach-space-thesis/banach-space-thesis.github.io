import JLMS.CZeroTools
import JLMS.Simultaneous
import Mathlib.Data.Nat.Pairing

/-!
# The c₀ block decomposition used in Lemma 8.2

Cantor pairing partitions the coordinates of c₀ into countably many copies of
c₀. The inclusion extends by zero off its block; the projection reads that
block. Both maps are contractions and satisfy the Kronecker-delta identity.
Transport through any bounded retract of c₀ supplies the block system in E.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Insert a sequence on the coordinates pair(j,n), extending by zero. -/
def cZeroBlockInsert (j : ℕ) (f : cZero 𝕜) : cZero 𝕜 where
  toFun m := if (Nat.unpair m).1 = j then f (Nat.unpair m).2 else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    classical
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hf := Metric.tendsto_nhds.mp f.zero_at_infty' ε hε
    rw [cocompact_eq_cofinite] at hf ⊢
    have hbad : {n : ℕ | ¬ dist (f n) 0 < ε}.Finite := mem_cofinite.mp hf
    filter_upwards [(hbad.image (Nat.pair j)).compl_mem_cofinite] with m hm
    by_cases hj : (Nat.unpair m).1 = j
    · simp only [hj, if_true]
      by_contra h
      apply hm
      refine ⟨(Nat.unpair m).2, h, ?_⟩
      simpa [hj] using Nat.pair_unpair m
    · simp [hj, hε]

/-- Read the coordinates pair(j,n). -/
def cZeroBlockRead (j : ℕ) (f : cZero 𝕜) : cZero 𝕜 where
  toFun n := f (Nat.pair j n)
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    have hinj : Function.Injective (Nat.pair j) := by
      intro m n h
      simpa using congrArg Prod.snd (congrArg Nat.unpair h)
    have ht := hinj.tendsto_cofinite
    rw [← cocompact_eq_cofinite ℕ] at ht
    exact f.zero_at_infty'.comp ht

theorem norm_cZeroBlockInsert_le (j : ℕ) (f : cZero 𝕜) : ‖cZeroBlockInsert j f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro m
  change ‖if (Nat.unpair m).1 = j then f (Nat.unpair m).2 else 0‖ ≤ ‖f‖
  split_ifs
  · exact norm_CZero_apply_le f _
  · simp

theorem norm_cZeroBlockRead_le (j : ℕ) (f : cZero 𝕜) : ‖cZeroBlockRead j f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro n
  exact norm_CZero_apply_le f (Nat.pair j n)

def cZeroBlockInclusion (j : ℕ) : cZero 𝕜 →L[𝕜] cZero 𝕜 :=
  ({ toFun := cZeroBlockInsert j
     map_add' := by
       intro f g
       ext m
       change (if _ then _ else _) = _
       split_ifs <;> simp_all [cZeroBlockInsert]
     map_smul' := by
       intro a f
       ext m
       change (if _ then _ else _) = _
       split_ifs <;> simp_all [cZeroBlockInsert] } : cZero 𝕜 →ₗ[𝕜] cZero 𝕜).mkContinuous 1
    (fun f => by simpa using norm_cZeroBlockInsert_le j f)

def cZeroBlockProjection (j : ℕ) : cZero 𝕜 →L[𝕜] cZero 𝕜 :=
  ({ toFun := cZeroBlockRead j
     map_add' := by intro f g; ext n; rfl
     map_smul' := by intro a f; ext n; rfl } : cZero 𝕜 →ₗ[𝕜] cZero 𝕜).mkContinuous 1
    (fun f => by simpa using norm_cZeroBlockRead_le j f)

theorem norm_cZeroBlockInclusion_le (j : ℕ) : ‖cZeroBlockInclusion (𝕜 := 𝕜) j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_cZeroBlockInsert_le j f

theorem norm_cZeroBlockProjection_le (j : ℕ) : ‖cZeroBlockProjection (𝕜 := 𝕜) j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_cZeroBlockRead_le j f

theorem cZeroBlock_retract (j : ℕ) :
    (cZeroBlockProjection (𝕜 := 𝕜) j).comp (cZeroBlockInclusion j) =
      ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
  ext f n
  change (if (Nat.unpair (Nat.pair j n)).1 = j then f (Nat.unpair (Nat.pair j n)).2 else 0) = f n
  simp

theorem cZeroBlock_orthogonal (i j : ℕ) (hij : i ≠ j) :
    (cZeroBlockProjection (𝕜 := 𝕜) i).comp (cZeroBlockInclusion j) = 0 := by
  ext f n
  change (if (Nat.unpair (Nat.pair i n)).1 = j then f (Nat.unpair (Nat.pair i n)).2 else 0) = 0
  simp [hij]

def cZeroOrthogonalRetracts (𝕜 : Type*) [RCLike 𝕜] :
    OrthogonalRetracts 𝕜 (cZero 𝕜) (cZero 𝕜) where
  inclusion := cZeroBlockInclusion
  projection := cZeroBlockProjection
  retract := cZeroBlock_retract
  orthogonal := cZeroBlock_orthogonal
  bound := 1
  inclusion_bound := norm_cZeroBlockInclusion_le
  projection_bound := norm_cZeroBlockProjection_le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Transport the c₀ blocks through the retract A,B of Lemma 8.1. -/
def orthogonalRetracts_of_cZero_retract (A : cZero 𝕜 →L[𝕜] E) (B : E →L[𝕜] cZero 𝕜)
    (hBA : B.comp A = ContinuousLinearMap.id 𝕜 (cZero 𝕜)) :
    OrthogonalRetracts 𝕜 E (cZero 𝕜) where
  inclusion j := A.comp (cZeroBlockInclusion j)
  projection j := (cZeroBlockProjection j).comp B
  retract j := by
    ext f n
    have h := congrArg (fun L : cZero 𝕜 →L[𝕜] cZero 𝕜 => L (cZeroBlockInclusion j f)) hBA
    have h' := congrArg (fun g : cZero 𝕜 => cZeroBlockProjection j g n) h
    exact h'.trans (congrArg (fun L : cZero 𝕜 →L[𝕜] cZero 𝕜 => L f n) (cZeroBlock_retract j))
  orthogonal i j hij := by
    ext f n
    have h := congrArg (fun L : cZero 𝕜 →L[𝕜] cZero 𝕜 => L (cZeroBlockInclusion j f)) hBA
    have h' := congrArg (fun g : cZero 𝕜 => cZeroBlockProjection i g n) h
    exact h'.trans (congrArg (fun L : cZero 𝕜 →L[𝕜] cZero 𝕜 => L f n) (cZeroBlock_orthogonal i j hij))
  bound := ‖A‖ + ‖B‖
  inclusion_bound j := calc
    ‖A.comp (cZeroBlockInclusion j)‖ ≤ ‖A‖ * ‖cZeroBlockInclusion j‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖ := by simpa using mul_le_mul_of_nonneg_left (norm_cZeroBlockInclusion_le j) (norm_nonneg A)
    _ ≤ ‖A‖ + ‖B‖ := le_add_of_nonneg_right (norm_nonneg B)
  projection_bound j := calc
    ‖(cZeroBlockProjection j).comp B‖ ≤ ‖cZeroBlockProjection j‖ * ‖B‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖B‖ := by simpa using mul_le_mul_of_nonneg_right (norm_cZeroBlockProjection_le j) (norm_nonneg B)
    _ ≤ ‖A‖ + ‖B‖ := le_add_of_nonneg_left (norm_nonneg A)

end JLMS
