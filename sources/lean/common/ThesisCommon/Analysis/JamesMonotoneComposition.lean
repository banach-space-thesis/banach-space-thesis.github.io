import ThesisCommon.Analysis.JamesMonotonePaths
import ThesisCommon.Analysis.JamesRawLimits

/-! Nondecreasing cofinal changes of index act contractively on the actual
finite-p James space. This includes subsequence sampling and step repetition. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
  (ρ : ℕ → ℕ) (hρ : Monotone ρ) (hco : Tendsto ρ atTop atTop)

def jamesMonotoneComposeValue (x : JamesSequenceSpace 𝕜 p) : JamesSequenceSpace 𝕜 p :=
  jamesOfConvergentVariation p (fun n => x (ρ n)) 0 (x.tendsto_zero.comp hco)
    (fun s => james_monotone_path_norm_le p hp (ρ ∘ s.index)
      (hρ.comp s.strictMono.monotone) x)

@[simp] theorem jamesMonotoneComposeValue_apply (x : JamesSequenceSpace 𝕜 p) (n : ℕ) :
    jamesMonotoneComposeValue p hp ρ hρ hco x n = x (ρ n) := by
  exact sub_zero _

theorem jamesMonotoneComposeValue_norm_le (x : JamesSequenceSpace 𝕜 p) :
    ‖jamesMonotoneComposeValue p hp ρ hρ hco x‖ ≤ ‖x‖ :=
  jamesOfConvergentVariation_norm_le _ _ _ _ _

def jamesMonotoneCompose : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p :=
  LinearMap.mkContinuous
    { toFun := jamesMonotoneComposeValue p hp ρ hρ hco
      map_add' := by intros; ext n; simp only [jamesMonotoneComposeValue_apply,
        JamesSequenceSpace.add_apply]
      map_smul' := by intros; ext n; simp only [jamesMonotoneComposeValue_apply,
        JamesSequenceSpace.smul_apply, RingHom.id_apply] }
    1 (fun x => by simpa only [one_mul] using
      jamesMonotoneComposeValue_norm_le p hp ρ hρ hco x)

@[simp] theorem jamesMonotoneCompose_apply (x : JamesSequenceSpace 𝕜 p) (n : ℕ) :
    jamesMonotoneCompose (𝕜 := 𝕜) p hp ρ hρ hco x n = x (ρ n) :=
  jamesMonotoneComposeValue_apply p hp ρ hρ hco x n

theorem jamesMonotoneCompose_norm_le :
    ‖jamesMonotoneCompose (𝕜 := 𝕜) p hp ρ hρ hco‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end ThesisCommon
