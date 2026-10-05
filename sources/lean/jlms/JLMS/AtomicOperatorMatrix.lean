import JLMS.AtomicDual

/-!
# Ogden Section 3: the atomic matrix of an operator on C₀(K)

Rudin coordinates of T*δₓ form the x-row. Every row is in ℓ¹(K), its pairing
with a function gives that function's image at x, and composition is matrix
multiplication expressed as a convergent ℓ¹-valued series. These statements
apply to all scattered locally compact spaces once Rudin's proved model is
supplied; the ordinal specialization does not introduce a new assumption.
-/

noncomputable section
attribute [local instance] Classical.decEq
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]
variable (M : AtomicDualModel 𝕜 K)

local instance atomicMatrixDualGroup : NormedAddCommGroup (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance atomicMatrixDualSpace : NormedSpace 𝕜 (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

def atomicOperatorRow (T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K) (x : K) : ellOneOn 𝕜 K :=
  M.representation ((evaluation x).comp T)

def atomicOperatorMatrix (T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K) (x y : K) : 𝕜 :=
  atomicOperatorRow M T x y

theorem atomicOperatorRow_hasSum (T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K)
    (f : CZero 𝕜 K) (x : K) :
    HasSum (fun y => atomicOperatorMatrix M T x y * f y) (T f x) :=
  atomicDual_apply_hasSum M ((evaluation x).comp T) f

theorem atomicOperatorRow_countable_support (T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K)
    (x : K) : (Function.support (atomicOperatorMatrix M T x)).Countable :=
  atomicDual_countable_support M ((evaluation x).comp T)

theorem norm_atomicOperatorRow_le (T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K) (x : K) :
    ‖atomicOperatorRow M T x‖ ≤ ‖T‖ := by
  change ‖M.representation ((evaluation x).comp T)‖ ≤ _
  rw [M.representation.norm_map]
  calc
    ‖(evaluation (𝕜 := 𝕜) x).comp T‖ ≤ ‖evaluation (𝕜 := 𝕜) x‖ * ‖T‖ :=
      ContinuousLinearMap.opNorm_comp_le (evaluation (𝕜 := 𝕜) x) T
    _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right
      (norm_evaluation_le (𝕜 := 𝕜) x) (norm_nonneg T)
    _ = ‖T‖ := one_mul _

theorem opNorm_le_of_atomicOperatorRows (T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K)
    {C : ℝ} (hC : 0 ≤ C) (hrows : ∀ x, ‖atomicOperatorRow M T x‖ ≤ C) : ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg f))).mpr
  intro x
  change ‖T f x‖ ≤ C * ‖f‖
  calc
    ‖T f x‖ ≤ ‖(evaluation x).comp T‖ * ‖f‖ := ((evaluation x).comp T).le_opNorm f
    _ = ‖atomicOperatorRow M T x‖ * ‖f‖ := by rw [atomicOperatorRow, M.representation.norm_map]
    _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right (hrows x) (norm_nonneg f)

theorem atomicOperatorRows_isLUB [Nonempty K]
    (T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K) :
    IsLUB (Set.range (fun x => ‖atomicOperatorRow M T x‖)) ‖T‖ := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact norm_atomicOperatorRow_le M T x
  · intro C hC
    have hCpos : 0 ≤ C := (norm_nonneg (atomicOperatorRow M T (Classical.arbitrary K))).trans
      (hC ⟨Classical.arbitrary K, rfl⟩)
    exact opNorm_le_of_atomicOperatorRows M T hCpos (fun x => hC ⟨x, rfl⟩)

@[simp] theorem atomicOperatorRow_id (x : K) :
    atomicOperatorRow M (ContinuousLinearMap.id 𝕜 (CZero 𝕜 K)) x =
      lp.single 1 x (1 : 𝕜) := by
  apply M.representation.symm.injective
  simp [atomicOperatorRow, M.pointMass]

theorem atomicOperatorRow_comp_hasSum (S T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K) (x : K) :
    HasSum (fun y => atomicOperatorMatrix M S x y • atomicOperatorRow M T y)
      (atomicOperatorRow M (S.comp T) x) := by
  let L := (atomicCoordinates M).comp (banachAdjoint T)
  have h := (atomicDual_hasSum M ((evaluation x).comp S)).map L L.continuous
  convert h using 1
  funext y
  change _ = L (atomicOperatorMatrix M S x y • evaluation y)
  rw [map_smul]
  rfl

end JLMS
