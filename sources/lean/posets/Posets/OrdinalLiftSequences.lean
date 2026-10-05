import Posets.OrdinalLiftIterate
import ThesisCommon.Analysis.CountableCompactShells

/-! Relative derivative witnesses can be separated by clopen shells in the
countable target, even when the metric source is uncountable. -/

noncomputable section
open Set Filter Topology ThesisCommon
namespace Posets
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [Countable Y]

theorem ordinalLiftDerivative_late_shell (f : X → Y) (hf : Continuous f)
    {x : X} {A U : Set X} (hx : x ∈ ordinalLiftDerivative f A)
    (hU : IsOpen U) (hxU : x ∈ U) (N : ℕ) :
    ∃ j, N ≤ j ∧ (A ∩ U ∩ f ⁻¹' countableClopenShell (f x) j).Nonempty := by
  let V := U ∩ f ⁻¹' countableClopenNest (f x) N
  have hV : IsOpen V := hU.inter ((countableClopenNest_isClopen (f x) N).isOpen.preimage hf)
  obtain ⟨z, hzA, hzV, hne⟩ := hx.2 V hV ⟨hxU, countableClopenNest_mem (f x) N⟩
  obtain ⟨j, hj⟩ := countableClopenShell_covers (f x) hne
  refine ⟨j, ?_, z, ⟨hzA, hzV.1⟩, hj⟩
  by_contra hNj
  have hjN : j + 1 ≤ N := by omega
  exact hj.2 (countableClopenNest_antitone (f x) hjN hzV.2)

theorem ordinalLiftDerivative_disjoint_sequence (f : X → Y) (hf : Continuous f)
    {x : X} (A : ℕ → Set X) (hx : ∀ n, x ∈ ordinalLiftDerivative f (A n))
    {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ z : ℕ → X, ∃ V : ℕ → Set X, ∃ W : ℕ → Set Y,
      (∀ n, z n ∈ A n ∧ z n ∈ V n ∧ IsOpen (V n) ∧ V n ⊆ U ∧
        V n ⊆ f ⁻¹' W n ∧ V n ⊆ Metric.ball x (1 / ((n : ℝ) + 1))) ∧
      (∀ n, IsClopen (W n) ∧ f x ∉ W n) ∧
      Pairwise (fun n m => Disjoint (W n) (W m)) ∧ Tendsto z atTop (𝓝 x) := by
  classical
  let B (n : ℕ) := U ∩ Metric.ball x (1 / ((n : ℝ) + 1))
  have hB (n : ℕ) : IsOpen (B n) := hU.inter Metric.isOpen_ball
  have hxB (n : ℕ) : x ∈ B n := ⟨hxU, Metric.mem_ball_self (by positivity)⟩
  have hex (n N : ℕ) := ordinalLiftDerivative_late_shell f hf (hx n) (hB n) (hxB n) N
  let next (n N : ℕ) := (hex n N).choose
  have hnext (n N : ℕ) : N ≤ next n N ∧
      (A n ∩ B n ∩ f ⁻¹' countableClopenShell (f x) (next n N)).Nonempty :=
    (hex n N).choose_spec
  let j : ℕ → ℕ := Nat.rec (next 0 0) (fun n prev => next (n + 1) (prev + 1))
  have hjstep (n : ℕ) : j n < j (n + 1) := (hnext (n + 1) (j n + 1)).1
  have hjmono : StrictMono j := strictMono_nat_of_lt_succ hjstep
  have hjmem (n : ℕ) : (A n ∩ B n ∩ f ⁻¹' countableClopenShell (f x) (j n)).Nonempty := by
    cases n with
    | zero => exact (hnext 0 0).2
    | succ n => exact (hnext (n + 1) (j n + 1)).2
  let z (n : ℕ) := (hjmem n).choose
  have hz (n : ℕ) : z n ∈ A n ∩ B n ∩ f ⁻¹' countableClopenShell (f x) (j n) :=
    (hjmem n).choose_spec
  let W (n : ℕ) := countableClopenShell (f x) (j n)
  let V (n : ℕ) := B n ∩ f ⁻¹' W n
  refine ⟨z, V, W, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(hz n).1.1, ⟨(hz n).1.2, (hz n).2⟩,
      (hB n).inter ((countableClopenShell_isClopen (f x) (j n)).isOpen.preimage hf),
      fun _ h => h.1.1, inter_subset_right, fun _ h => h.1.2⟩
  · intro n
    exact ⟨countableClopenShell_isClopen (f x) (j n), countableClopenShell_not_mem (f x) (j n)⟩
  · intro n m hnm
    exact countableClopenShell_disjoint (f x) (hjmono.injective.ne hnm)
  · apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    exact fun n => (hz n).1.2.2.le

end Posets
