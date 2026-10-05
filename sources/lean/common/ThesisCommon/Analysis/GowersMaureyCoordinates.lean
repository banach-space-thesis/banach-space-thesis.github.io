import ThesisCommon.Analysis.GowersMaureyShifts

/-! Actual scalar coordinates and matrix entries on the completed shift space.
Every map is extended from the concrete finite-sequence pre-space. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def preCoordinate (D : ConstructionData 𝕜) (n : ℕ) : PreSpace D →L[𝕜] 𝕜 :=
  (Finsupp.lapply n : PreSpace D →ₗ[𝕜] 𝕜).mkContinuous 1
    (fun x => by simpa only [one_mul] using PreSpace.norm_apply_le x n)

def completedCoordinate (D : ConstructionData 𝕜) (n : ℕ) : ShiftSpace D →L[𝕜] 𝕜 :=
  (preCoordinate D n).extend (denseEmbedding D).toContinuousLinearMap
    (denseEmbedding_denseRange D) (denseEmbedding D).isometry.isUniformInducing

@[simp] theorem completedCoordinate_denseEmbedding (D : ConstructionData 𝕜)
    (n : ℕ) (x : PreSpace D) : completedCoordinate D n (denseEmbedding D x) = x n :=
  ContinuousLinearMap.extend_eq _ _ _ _ x

theorem completedCoordinate_norm_le (D : ConstructionData 𝕜) (n : ℕ) (x : ShiftSpace D) :
    ‖completedCoordinate D n x‖ ≤ ‖x‖ := by
  refine (denseEmbedding_denseRange D).induction_on x ?_ ?_
  · exact isClosed_le (completedCoordinate D n).continuous.norm continuous_norm
  · intro a
    rw [completedCoordinate_denseEmbedding, denseEmbedding_norm]
    exact PreSpace.norm_apply_le a n

theorem norm_completedCoordinate_le (D : ConstructionData 𝕜) (n : ℕ) :
    ‖completedCoordinate D n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using completedCoordinate_norm_le D n x

def basisVector (D : ConstructionData 𝕜) (n : ℕ) : ShiftSpace D :=
  denseEmbedding D (PreSpace.single n 1)

@[simp] theorem norm_basisVector (D : ConstructionData 𝕜) (n : ℕ) :
    ‖basisVector D n‖ = 1 := by simp [basisVector]

@[simp] theorem completedCoordinate_basisVector (D : ConstructionData 𝕜) (i j : ℕ) :
    completedCoordinate D i (basisVector D j) = if i = j then 1 else 0 := by
  simp [basisVector, eq_comm]

theorem completedCoordinate_spread_basisVector (D : ConstructionData 𝕜) (m n i j : ℕ) :
    completedCoordinate D i (completedSpread D m n (basisVector D j)) =
      if m ≤ j ∧ i = j - m + n then 1 else 0 := by
  rw [basisVector, completedSpread_denseEmbedding, completedCoordinate_denseEmbedding]
  change spread m n (Finsupp.single j (1 : 𝕜)) i = _
  rw [spread_single]
  split_ifs with hm hij
  · simp [hij]
  · simp_all
  · simp_all
  · rfl

def matrixEntry (D : ConstructionData 𝕜) (i j : ℕ) :
    (ShiftSpace D →L[𝕜] ShiftSpace D) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun T => completedCoordinate D i (T (basisVector D j))
      map_add' := by intros; simp
      map_smul' := by intros; simp }
    1 (fun T => by
      simpa only [one_mul, norm_basisVector, mul_one] using
        (completedCoordinate_norm_le D i (T (basisVector D j))).trans
          (T.le_opNorm (basisVector D j)))

@[simp] theorem matrixEntry_apply (D : ConstructionData 𝕜) (i j : ℕ)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    matrixEntry D i j T = completedCoordinate D i (T (basisVector D j)) := rfl

theorem norm_matrixEntry_le (D : ConstructionData 𝕜) (i j : ℕ) :
    ‖matrixEntry D i j‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _

end ThesisCommon.GowersMaurey
