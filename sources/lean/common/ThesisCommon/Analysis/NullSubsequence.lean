import ThesisCommon.Analysis.InfiniteFusion
import Mathlib.Analysis.SpecificLimits.Basic

/-! Increasing subsequences with a prescribed positive budget, including
summable subsequences of nonnegative null sequences. -/
noncomputable section
open Filter Topology
namespace ThesisCommon

theorem exists_increasing_small_subsequence {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) {M : Set ℕ} (hM : M.Infinite)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ (∀ k, e k ∈ M) ∧ ∀ k, f (e k) < δ k := by
  classical
  have hex : ∀ k b : ℕ, ∃ n ∈ M, b < n ∧ f n < δ k := by
    intro k b
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hf.eventually_lt_const (hδ k))
    obtain ⟨n, hnM, hn⟩ := (infinite_above hM (max b N)).nonempty
    exact ⟨n, hnM, (le_max_left b N).trans_lt hn,
      hN n ((le_max_right b N).trans hn.le)⟩
  choose next hmem hgt hsmall using hex
  let f : ℕ → ℕ := fun k => Nat.rec (next 0 0) (fun j n => next (j+1) n) k
  have hmono : StrictMono f := strictMono_nat_of_lt_succ (fun k => hgt (k+1) (f k))
  refine ⟨⟨f, hmono.injective⟩, hmono, ?_, ?_⟩
  · intro k
    cases k with
    | zero => exact hmem 0 0
    | succ k => exact hmem (k+1) (f k)
  · intro k
    cases k with
    | zero => exact hsmall 0 0
    | succ k => exact hsmall (k+1) (f k)

theorem exists_increasing_summable_subsequence {f : ℕ → ℝ} (hpos : ∀ n, 0 ≤ f n)
    (hf : Tendsto f atTop (𝓝 0)) {M : Set ℕ} (hM : M.Infinite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ (∀ k, e k ∈ M) ∧
      Summable (fun k => f (e k)) ∧ (∑' k, f (e k)) < ε := by
  obtain ⟨e, he, hmem, hsmall⟩ := exists_increasing_small_subsequence hf hM
    (fun k => (ε/4) * (1/2 : ℝ)^k) (fun _ => by positivity)
  have hs := summable_geometric_two.mul_left (ε/4)
  have hf' : Summable (fun k => f (e k)) :=
    hs.of_nonneg_of_le (fun k => hpos (e k)) (fun k => (hsmall k).le)
  refine ⟨e, he, hmem, hf', ?_⟩
  calc
    (∑' k, f (e k)) ≤ ∑' k, (ε/4) * (1/2 : ℝ)^k :=
      hf'.tsum_le_tsum (fun k => (hsmall k).le) hs
    _ = (ε/4)*2 := (hasSum_geometric_two.mul_left (ε/4)).tsum_eq
    _ < ε := by linarith

end ThesisCommon
