import PL1.WalshModel
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Canonical contractive inclusions between Lp spaces on a probability space -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PL1
namespace ProbabilityLp

variable {𝕜 : Type*} [RCLike 𝕜]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q)

def inclusionFun (f : Lp 𝕜 q μ) : Lp 𝕜 p μ :=
  ((Lp.memLp f).mono_exponent hpq).toLp f

theorem coeFn_inclusionFun (f : Lp 𝕜 q μ) : inclusionFun μ p q hpq f =ᵐ[μ] f :=
  ((Lp.memLp f).mono_exponent hpq).coeFn_toLp

theorem inclusionFun_add (f g : Lp 𝕜 q μ) :
    inclusionFun μ p q hpq (f + g) = inclusionFun μ p q hpq f + inclusionFun μ p q hpq g := by
  apply Lp.ext
  filter_upwards [coeFn_inclusionFun μ p q hpq (f + g), coeFn_inclusionFun μ p q hpq f,
    coeFn_inclusionFun μ p q hpq g, Lp.coeFn_add f g,
    Lp.coeFn_add (inclusionFun μ p q hpq f) (inclusionFun μ p q hpq g)]
      with x hfg hf hg hadd hadd'
  simp only [hfg, hadd, hadd', Pi.add_apply, hf, hg]

theorem inclusionFun_smul (c : 𝕜) (f : Lp 𝕜 q μ) :
    inclusionFun μ p q hpq (c • f) = c • inclusionFun μ p q hpq f := by
  apply Lp.ext
  filter_upwards [coeFn_inclusionFun μ p q hpq (c • f), coeFn_inclusionFun μ p q hpq f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (inclusionFun μ p q hpq f)] with x hcf hf hsmul hsmul'
  simp only [hcf, hsmul, hsmul', Pi.smul_apply, hf]

theorem norm_inclusionFun_le (f : Lp 𝕜 q μ) : ‖inclusionFun μ p q hpq f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_inclusionFun μ p q hpq f)]
  exact ENNReal.toReal_mono (Lp.memLp f).2.ne
    (eLpNorm_le_eLpNorm_of_exponent_le hpq (Lp.aestronglyMeasurable f))

def inclusion : Lp 𝕜 q μ →L[𝕜] Lp 𝕜 p μ :=
  LinearMap.mkContinuous
    { toFun := inclusionFun μ p q hpq
      map_add' := inclusionFun_add μ p q hpq
      map_smul' := inclusionFun_smul μ p q hpq }
    1 (fun f => by
      change ‖inclusionFun μ p q hpq f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_inclusionFun_le μ p q hpq f)

theorem coeFn_inclusion (f : Lp 𝕜 q μ) : inclusion μ p q hpq f =ᵐ[μ] f :=
  coeFn_inclusionFun μ p q hpq f

theorem norm_inclusion_le_one : ‖inclusion (𝕜 := 𝕜) μ p q hpq‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖inclusionFun μ p q hpq f‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using norm_inclusionFun_le μ p q hpq f

theorem inclusion_toLp {f : Ω → 𝕜} (hf : MemLp f q μ) :
    inclusion μ p q hpq (hf.toLp f) = (hf.mono_exponent hpq).toLp f := by
  apply Lp.ext
  exact (coeFn_inclusion μ p q hpq _).trans
    (hf.coeFn_toLp.trans (hf.mono_exponent hpq).coeFn_toLp.symm)

theorem inclusion_comp (r : ℝ≥0∞) [Fact (1 ≤ r)] (hqr : q ≤ r) :
    (inclusion (𝕜 := 𝕜) μ p q hpq).comp (inclusion μ q r hqr) =
      inclusion μ p r (hpq.trans hqr) := by
  ext f
  exact ((coeFn_inclusion μ p q hpq _).trans (coeFn_inclusion μ q r hqr f)).trans
    (coeFn_inclusion μ p r (hpq.trans hqr) f).symm

end ProbabilityLp

namespace Walsh

variable {𝕜 : Type*} [RCLike 𝕜]

abbrev l2ToL1 : Lp 𝕜 2 haar →L[𝕜] Lp 𝕜 1 haar :=
  ProbabilityLp.inclusion haar 1 2 (by norm_num)

abbrev linftyToL2 : Lp 𝕜 ∞ haar →L[𝕜] Lp 𝕜 2 haar :=
  ProbabilityLp.inclusion haar 2 ∞ le_top

theorem l2ToL1_scalarCharacter (F : Finset ℕ) :
    l2ToL1 (scalarCharacterLp 𝕜 2 F) = scalarCharacterLp 𝕜 1 F :=
  ProbabilityLp.inclusion_toLp haar 1 2 (by norm_num) (memLp_scalarCharacter 𝕜 2 F)

end Walsh
end PL1
