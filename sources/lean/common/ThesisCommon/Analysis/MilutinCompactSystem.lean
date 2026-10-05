import ThesisCommon.Analysis.MilutinCoverStep
import ThesisCommon.Analysis.MilutinRegularAveraging

/-! The actual compact metric inverse system in Ditor's construction.
At stage n every new compact piece has diameter less than 2^(-n-1).
The bonding maps have norm-one averaging and have at least two lifts at
every point. No inverse-system existence hypothesis is assumed. -/

noncomputable section
universe u
namespace ThesisCommon

structure MilutinCompactMetric where
  carrier : Type u
  metric : MetricSpace carrier
  compact : @CompactSpace carrier metric.toUniformSpace.toTopologicalSpace
  nonempty : Nonempty carrier

attribute [instance] MilutinCompactMetric.metric MilutinCompactMetric.compact
  MilutinCompactMetric.nonempty

instance : CoeSort MilutinCompactMetric (Type u) := ⟨MilutinCompactMetric.carrier⟩

def MilutinCompactMetric.of (K : Type u) [MetricSpace K] [CompactSpace K] [Nonempty K] :
    MilutinCompactMetric := ⟨K, inferInstance, inferInstance, inferInstance⟩

def milutinMesh (n : ℕ) : ℝ := (1 / 2) ^ (n + 1)

theorem milutinMesh_pos (n : ℕ) : 0 < milutinMesh n := by
  unfold milutinMesh
  positivity

def milutinCompactRefine (B : MilutinCompactMetric) (n : ℕ) : MilutinCompactMetric :=
  let S := milutinCoverStep (K := B) (milutinMesh_pos n)
  ⟨S.Space, inferInstance, inferInstance, inferInstance⟩

def milutinCompactStage (B : MilutinCompactMetric) : ℕ → MilutinCompactMetric
  | 0 => B
  | n + 1 => milutinCompactRefine (milutinCompactStage B n) n

def milutinCompactCover (B : MilutinCompactMetric) (n : ℕ) :
    MilutinCoverStep (milutinCompactStage B n) (milutinMesh n) :=
  milutinCoverStep (milutinMesh_pos n)

def milutinCompactBonding (B : MilutinCompactMetric) (n : ℕ) :
    C(milutinCompactStage B (n + 1), milutinCompactStage B n) :=
  (milutinCompactCover B n).projection

theorem milutinCompactBonding_surjective (B : MilutinCompactMetric) (n : ℕ) :
    Function.Surjective (milutinCompactBonding B n) :=
  (milutinCompactCover B n).projection_surjective

theorem milutinCompactBonding_double (B : MilutinCompactMetric) (n : ℕ)
    (x : milutinCompactStage B n) :
    ∃ y z : milutinCompactStage B (n + 1), y ≠ z ∧
      milutinCompactBonding B n y = x ∧ milutinCompactBonding B n z = x :=
  (milutinCompactCover B n).projection_double x

theorem milutinCompactBonding_regular_averaging {𝕜 : Type*} [RCLike 𝕜]
    (B : MilutinCompactMetric) (n : ℕ) :
    ∃ A : C(milutinCompactStage B (n + 1), 𝕜) →L[𝕜] C(milutinCompactStage B n, 𝕜),
      ‖A‖ = 1 ∧ A.comp (continuousMapPullback (milutinCompactBonding B n)) =
        ContinuousLinearMap.id 𝕜 C(milutinCompactStage B n, 𝕜) :=
  (milutinCompactCover B n).projection_regular_averaging

abbrev MilutinCompactLimit (B : MilutinCompactMetric) :=
  MilutinInverseLimit (K := fun n => (milutinCompactStage B n).carrier) (milutinCompactBonding B)

def milutinCompactProjection (B : MilutinCompactMetric) : C(MilutinCompactLimit B, B) :=
  milutinLimitProjection (K := fun n => (milutinCompactStage B n).carrier) (milutinCompactBonding B) 0

theorem milutinCompactProjection_surjective (B : MilutinCompactMetric) :
    Function.Surjective (milutinCompactProjection B) :=
  milutinLimitProjection_surjective (K := fun n => (milutinCompactStage B n).carrier) (milutinCompactBonding B)
    (milutinCompactBonding_surjective B) 0

theorem milutinCompactProjection_regular_averaging {𝕜 : Type*} [RCLike 𝕜]
    (B : MilutinCompactMetric) :
    ∃ A : C(MilutinCompactLimit B, 𝕜) →L[𝕜] C(B, 𝕜),
      ‖A‖ = 1 ∧ A.comp (continuousMapPullback (milutinCompactProjection B)) =
        ContinuousLinearMap.id 𝕜 C(B, 𝕜) := by
  apply milutin_inverse_limit_regular_averaging (K := fun n => (milutinCompactStage B n).carrier) (milutinCompactBonding B)
    (milutinCompactBonding_surjective B)
  intro n
  obtain ⟨A, hA, hAJ⟩ := milutinCompactBonding_regular_averaging (𝕜 := 𝕜) B n
  exact ⟨A, hA.le, hAJ⟩

def milutinCompactLabel (B : MilutinCompactMetric) (n : ℕ) :
    C(milutinCompactStage B (n + 1), Fin (milutinCompactCover B n).count) where
  toFun x := x.1
  continuous_toFun := continuous_sigma fun _ => continuous_const

def milutinCompactCode (B : MilutinCompactMetric) :
    C(MilutinCompactLimit B, ∀ n, Fin (milutinCompactCover B n).count) where
  toFun x n := milutinCompactLabel B n (x.val (n + 1))
  continuous_toFun := continuous_pi fun n =>
    (milutinCompactLabel B n).continuous.comp ((continuous_apply (n + 1)).comp continuous_subtype_val)

end ThesisCommon
