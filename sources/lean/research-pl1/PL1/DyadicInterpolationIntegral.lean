import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Dyadic sampling of the continuous real interpolation integral

All integrals and series take values in ENNReal, so the comparisons include
infinite norms and imply equivalence of the corresponding membership tests.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PL1.DyadicInterpolation

def time (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n
def shell (n : ℕ) : Set ℝ := Ioc (time (n + 1)) (time n)
def weight (n : ℕ) : ℝ := (time n) ^ (-1 / 2 : ℝ)
def sample (k : ℝ → ℝ) (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (weight n * k (time n))
def integrand (k : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (t ^ (-3 / 2 : ℝ) * k t)
def smallIntegral (k : ℝ → ℝ) : ℝ≥0∞ := ∫⁻ t in Ioc (0 : ℝ) 1, integrand k t
def fullIntegral (k : ℝ → ℝ) : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), integrand k t
def lowerConstant : ℝ := (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / 2
def upperConstant : ℝ := (1 / 2 : ℝ) ^ (-3 / 2 : ℝ) / 2

@[simp] theorem time_zero : time 0 = 1 := by simp [time]
theorem time_pos (n : ℕ) : 0 < time n := by unfold time; positivity
theorem time_succ (n : ℕ) : time (n + 1) = time n / 2 := by simp [time, pow_succ, div_eq_mul_inv]
theorem time_antitone : Antitone time := fun _ _ h => pow_le_pow_of_le_one (by norm_num) (by norm_num) h
theorem time_le_one (n : ℕ) : time n ≤ 1 := by simpa using time_antitone (Nat.zero_le n)
theorem tendsto_time : Tendsto time atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
theorem weight_pos (n : ℕ) : 0 < weight n := Real.rpow_pos_of_pos (time_pos n) _
theorem lowerConstant_pos : 0 < lowerConstant := by unfold lowerConstant; positivity
theorem upperConstant_pos : 0 < upperConstant := by unfold upperConstant; positivity

theorem shells_disjoint : Pairwise (fun m n => Disjoint (shell m) (shell n)) := by
  have aux (m n : ℕ) (hlt : m < n) : Disjoint (shell m) (shell n) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h := time_antitone (Nat.succ_le_of_lt hlt)
    exact (not_lt_of_ge (hy.2.trans h)) hx.1
  intro m n hmn
  obtain h | h := lt_or_gt_of_ne hmn
  · exact aux m n h
  · exact (aux n m h).symm

theorem union_shells : (⋃ n, shell n) = Ioc (0 : ℝ) 1 := by
  ext t
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ht
    exact ⟨(time_pos (n + 1)).trans hn.1, hn.2.trans (time_le_one n)⟩
  · intro ht
    have hex : ∃ n, time n < t :=
      (tendsto_time.eventually (gt_mem_nhds ht.1)).exists
    have hfind := Nat.find_spec hex
    have hn0 : Nat.find hex ≠ 0 := by intro he; rw [he, time_zero] at hfind; linarith [ht.2]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change time (n + 1) < t ∧ t ≤ time n
    constructor
    · simpa only [hn] using hfind
    · exact not_lt.mp (Nat.find_min hex (by omega))

theorem smallIntegral_eq_tsum (k : ℝ → ℝ) :
    smallIntegral k = ∑' n, ∫⁻ t in shell n, integrand k t := by
  rw [smallIntegral, ← union_shells]
  exact lintegral_iUnion (fun _ => measurableSet_Ioc) shells_disjoint _

theorem volume_shell (n : ℕ) : volume (shell n) = ENNReal.ofReal (time n / 2) := by
  rw [shell, Real.volume_Ioc, time_succ]
  congr 1
  ring

theorem rpow_length (n : ℕ) :
    (time n) ^ (-3 / 2 : ℝ) * (time n / 2) = weight n / 2 := by
  unfold weight
  rw [← mul_div_assoc]
  congr 1
  calc
    _ = (time n) ^ (-3 / 2 : ℝ) * (time n) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add (time_pos n)]; norm_num

theorem weight_succ (n : ℕ) :
    weight (n + 1) = weight n * (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) := by
  unfold weight time
  rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num)]

theorem lower_length (n : ℕ) :
    lowerConstant * weight (n + 1) = (time n) ^ (-3 / 2 : ℝ) * (time n / 2) := by
  rw [rpow_length, weight_succ]
  have hh : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
  unfold lowerConstant
  nlinarith [congrArg (fun z : ℝ => z * weight n) hh]

theorem upper_length (n : ℕ) :
    (time (n + 1)) ^ (-3 / 2 : ℝ) * (time n / 2) = upperConstant * weight n := by
  have ht : time (n + 1) = time n * (1 / 2) := by rw [time_succ]; ring
  rw [ht, Real.mul_rpow (time_pos n).le (by norm_num)]
  have hr := rpow_length n
  unfold upperConstant
  nlinarith [congrArg (fun z : ℝ => z * (1 / 2 : ℝ) ^ (-3 / 2 : ℝ)) hr]

variable {k : ℝ → ℝ}

theorem shell_bounds (hk : ∀ t ∈ Ici (0 : ℝ), 0 ≤ k t)
    (hmono : MonotoneOn k (Ici (0 : ℝ))) (n : ℕ) :
    ENNReal.ofReal lowerConstant * sample k (n + 1) ≤ ∫⁻ t in shell n, integrand k t ∧
      (∫⁻ t in shell n, integrand k t) ≤ ENNReal.ofReal upperConstant * sample k n := by
  have hlo (t : ℝ) (ht : t ∈ shell n) :
      (time n) ^ (-3 / 2 : ℝ) * k (time (n + 1)) ≤ t ^ (-3 / 2 : ℝ) * k t := by
    have ht0 : 0 < t := (time_pos (n + 1)).trans ht.1
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos ht0 ht.2 (by norm_num))
      (hmono (time_pos _).le ht0.le ht.1.le) (hk _ (time_pos _).le)
      (Real.rpow_nonneg ht0.le _)
  have hhi (t : ℝ) (ht : t ∈ shell n) :
      t ^ (-3 / 2 : ℝ) * k t ≤ (time (n + 1)) ^ (-3 / 2 : ℝ) * k (time n) := by
    have ht0 : 0 < t := (time_pos (n + 1)).trans ht.1
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos (time_pos _) ht.1.le (by norm_num))
      (hmono ht0.le (time_pos _).le ht.2) (hk _ ht0.le)
      (Real.rpow_nonneg (time_pos _).le _)
  have h1 : ENNReal.ofReal ((time n) ^ (-3 / 2 : ℝ) * k (time (n + 1))) * volume (shell n) ≤
      ∫⁻ t in shell n, integrand k t := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_Ioc (fun t ht => ENNReal.ofReal_le_ofReal (hlo t ht))
  have h2 : (∫⁻ t in shell n, integrand k t) ≤
      ENNReal.ofReal ((time (n + 1)) ^ (-3 / 2 : ℝ) * k (time n)) * volume (shell n) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_Ioc (fun t ht => ENNReal.ofReal_le_ofReal (hhi t ht))
  rw [volume_shell, ← ENNReal.ofReal_mul
    (mul_nonneg (Real.rpow_nonneg (time_pos n).le _) (hk _ (time_pos (n + 1)).le))] at h1
  rw [volume_shell, ← ENNReal.ofReal_mul
    (mul_nonneg (Real.rpow_nonneg (time_pos (n + 1)).le _) (hk _ (time_pos n).le))] at h2
  constructor
  · convert h1 using 1
    rw [sample, ← ENNReal.ofReal_mul lowerConstant_pos.le]
    congr 1
    calc
      _ = (lowerConstant * weight (n + 1)) * k (time (n + 1)) := by ring
      _ = _ := by rw [lower_length]; ring
  · convert h2 using 1
    rw [sample, ← ENNReal.ofReal_mul upperConstant_pos.le]
    congr 1
    calc
      _ = (upperConstant * weight n) * k (time n) := by ring
      _ = _ := by rw [← upper_length]; ring

theorem smallIntegral_bounds (hk : ∀ t ∈ Ici (0 : ℝ), 0 ≤ k t)
    (hmono : MonotoneOn k (Ici (0 : ℝ))) :
    ENNReal.ofReal lowerConstant * (∑' n, sample k (n + 1)) ≤ smallIntegral k ∧
      smallIntegral k ≤ ENNReal.ofReal upperConstant * (∑' n, sample k n) := by
  rw [smallIntegral_eq_tsum, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  exact ⟨ENNReal.tsum_le_tsum (fun n => (shell_bounds hk hmono n).1),
    ENNReal.tsum_le_tsum (fun n => (shell_bounds hk hmono n).2)⟩

theorem smallIntegral_ne_top_iff (hk : ∀ t ∈ Ici (0 : ℝ), 0 ≤ k t)
    (hmono : MonotoneOn k (Ici (0 : ℝ))) :
    smallIntegral k ≠ ⊤ ↔ (∑' n, sample k (n + 1)) ≠ ⊤ := by
  obtain ⟨hl, hu⟩ := smallIntegral_bounds hk hmono
  constructor
  · intro h hs
    have hc : ENNReal.ofReal lowerConstant ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr lowerConstant_pos)
    simp [hs, hc, h] at hl
  · intro h
    apply ne_top_of_le_ne_top _ hu
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    rw [tsum_eq_zero_add' ENNReal.summable]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, h⟩

theorem tailIntegral_eq {c : ℝ} (hc : 0 ≤ c)
    (htail : ∀ t, 1 ≤ t → k t = c) :
    (∫⁻ t in Ioi (1 : ℝ), integrand k t) = ENNReal.ofReal (2 * c) := by
  have heq : (∫⁻ t in Ioi (1 : ℝ), integrand k t) =
      ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-3 / 2 : ℝ) * c) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    rw [integrand, htail t ht.le]
  rw [heq]
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)).mul_const c
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun t => t ^ (-3 / 2 : ℝ) * c := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    exact mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ t) _) hc
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_mul_const,
    integral_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
  norm_num

theorem fullIntegral_eq {c : ℝ} (hc : 0 ≤ c)
    (htail : ∀ t, 1 ≤ t → k t = c) :
    fullIntegral k = smallIntegral k + ENNReal.ofReal (2 * c) := by
  have hs : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      by_cases h : t ≤ 1
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨ht, _⟩ | ht) <;> linarith
  have hd : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact (not_lt_of_ge ht.2) ht'
  rw [fullIntegral, hs, lintegral_union measurableSet_Ioi hd, tailIntegral_eq hc htail]
  rfl

theorem fullIntegral_ne_top_iff (hk : ∀ t ∈ Ici (0 : ℝ), 0 ≤ k t)
    (hmono : MonotoneOn k (Ici (0 : ℝ)))
    (htail : ∀ t, 1 ≤ t → k t = k 1) :
    fullIntegral k ≠ ⊤ ↔ (∑' n, sample k (n + 1)) ≠ ⊤ := by
  rw [fullIntegral_eq (hk 1 (by norm_num)) htail, ENNReal.add_ne_top]
  rw [and_iff_left ENNReal.ofReal_ne_top]
  exact smallIntegral_ne_top_iff hk hmono

end PL1.DyadicInterpolation

