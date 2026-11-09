import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Topology.Algebra.Order.LiminfLimsup

noncomputable section
open Filter
open scoped Topology NNReal

namespace PL1CD

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (p : ℕ → Seminorm 𝕜 E) (C : ℝ≥0)
    (hbound : ∀ n x, p n x ≤ (C : ℝ) * ‖x‖)
    (l : Filter ℕ) [l.NeBot]

include C hbound in
omit [l.NeBot] in
theorem seminormSequence_boundedAbove (x : E) :
    l.IsBoundedUnder (· ≤ ·) (fun n => p n x) :=
  ⟨(C : ℝ) * ‖x‖, eventually_map.mpr (Eventually.of_forall (fun n => hbound n x))⟩

omit [l.NeBot] in
theorem seminormSequence_boundedBelow (x : E) :
    l.IsBoundedUnder (· ≥ ·) (fun n => p n x) :=
  ⟨0, eventually_map.mpr (Eventually.of_forall (fun n => apply_nonneg (p n) x))⟩

theorem seminormSequence_cobounded (x : E) :
    l.IsCoboundedUnder (· ≤ ·) (fun n => p n x) :=
  (seminormSequence_boundedBelow p l x).isCoboundedUnder_le

def limsupSeminorm (p : ℕ → Seminorm 𝕜 E) (C : ℝ≥0)
    (hbound : ∀ n x, p n x ≤ (C : ℝ) * ‖x‖)
    (l : Filter ℕ) [l.NeBot] : Seminorm 𝕜 E := Seminorm.of
  (fun x => limsup (fun n => p n x) l)
  (by
    intro x y
    calc
      limsup (fun n => p n (x + y)) l ≤
          limsup (fun n => p n x + p n y) l :=
        limsup_le_limsup (Eventually.of_forall (fun n => map_add_le_add (p n) x y))
          (seminormSequence_cobounded p l (x + y))
          ⟨(C : ℝ) * ‖x‖ + (C : ℝ) * ‖y‖,
            eventually_map.mpr
              (Eventually.of_forall (fun n => add_le_add (hbound n x) (hbound n y)))⟩
      _ ≤ limsup (fun n => p n x) l + limsup (fun n => p n y) l :=
        limsup_add_le (seminormSequence_boundedBelow p l x)
          (seminormSequence_boundedAbove p C hbound l x)
          (seminormSequence_cobounded p l y)
          (seminormSequence_boundedAbove p C hbound l y))
  (by
    intro a x
    have hmono : Monotone (fun r : ℝ => ‖a‖ * r) :=
      fun _ _ h => mul_le_mul_of_nonneg_left h (norm_nonneg a)
    have h := hmono.map_limsup_of_continuousAt (fun n => p n x)
      (continuous_const.mul continuous_id).continuousAt
      (seminormSequence_boundedAbove p C hbound l x)
      (seminormSequence_cobounded p l x)
    simpa only [Function.comp_def, map_smul_eq_mul] using h.symm)

theorem limsupSeminorm_le (x : E) :
    limsupSeminorm p C hbound l x ≤ (C : ℝ) * ‖x‖ :=
  limsup_le_of_le (seminormSequence_cobounded p l x)
    (Eventually.of_forall (fun n => hbound n x))

theorem limsupSeminorm_continuous : Continuous (limsupSeminorm p C hbound l) := by
  have hcont : Continuous (C • normSeminorm 𝕜 E : E → ℝ) := by
    change Continuous (fun x : E => (C : ℝ) * ‖x‖)
    exact continuous_const.mul continuous_norm
  exact Seminorm.continuous_of_le (q := C • normSeminorm 𝕜 E) hcont
    (fun x => limsupSeminorm_le p C hbound l x)

theorem limsupSeminorm_eq_zero_of_tendsto (x : E)
    (h : Tendsto (fun n => p n x) l (𝓝 0)) : limsupSeminorm p C hbound l x = 0 :=
  h.limsup_eq

theorem limsup_mul_nonneg (u : ℕ → ℝ) (l : Filter ℕ) [l.NeBot]
    (hupper : l.IsBoundedUnder (· ≤ ·) u)
    (hlower : l.IsCoboundedUnder (· ≤ ·) u) {c : ℝ} (hc : 0 ≤ c) :
    limsup (fun n => c * u n) l = c * limsup u l := by
  have hmono : Monotone (fun r : ℝ => c * r) :=
    fun _ _ h => mul_le_mul_of_nonneg_left h hc
  exact (hmono.map_limsup_of_continuousAt u
    (continuous_const.mul continuous_id).continuousAt hupper hlower).symm

theorem limsupSeminorm_compare
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (q : ℕ → Seminorm 𝕜 F) (D : ℝ≥0)
    (hqbound : ∀ n y, q n y ≤ (D : ℝ) * ‖y‖)
    (x : E) (y : F) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n, p n x ≤ c * q n y) :
    limsupSeminorm p C hbound l x ≤ c * limsupSeminorm q D hqbound l y := by
  change limsup (fun n => p n x) l ≤ c * limsup (fun n => q n y) l
  rw [← limsup_mul_nonneg _ l (seminormSequence_boundedAbove q D hqbound l y)
    (seminormSequence_cobounded q l y) hc]
  exact limsup_le_limsup (Eventually.of_forall h)
    (seminormSequence_cobounded p l x)
    ⟨c * ((D : ℝ) * ‖y‖), eventually_map.mpr
      (Eventually.of_forall (fun n => mul_le_mul_of_nonneg_left (hqbound n y) hc))⟩

theorem limsupSeminorm_compare_lower
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (q : ℕ → Seminorm 𝕜 F) (D : ℝ≥0)
    (hqbound : ∀ n y, q n y ≤ (D : ℝ) * ‖y‖)
    (x : E) (y : F) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n, c * p n x ≤ q n y) :
    c * limsupSeminorm p C hbound l x ≤ limsupSeminorm q D hqbound l y := by
  change c * limsup (fun n => p n x) l ≤ limsup (fun n => q n y) l
  rw [← limsup_mul_nonneg _ l (seminormSequence_boundedAbove p C hbound l x)
    (seminormSequence_cobounded p l x) hc]
  exact limsup_le_limsup (Eventually.of_forall h)
    (isCoboundedUnder_le_of_le l (fun n => mul_nonneg hc (apply_nonneg (p n) x)))
    (seminormSequence_boundedAbove q D hqbound l y)

end PL1CD
