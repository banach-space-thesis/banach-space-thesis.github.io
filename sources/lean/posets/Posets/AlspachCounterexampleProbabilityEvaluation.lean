import Posets.AlspachCounterexampleProbabilityCalculus
import JLMS.AtomicDual

/-! Evaluation of finite probability rows, including their support bound
and compatibility with the actual atomic Banach dual. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
namespace AlspachProbability
variable {𝕜 K L : Type*} [RCLike 𝕜]

def eval : AlspachProbability K → (K → 𝕜) → 𝕜
  | .point k, f => f k
  | .average p q, f => (1 / 2 : 𝕜) * (p.eval f + q.eval f)

@[simp] theorem eval_point (k : K) (f : K → 𝕜) : (point k).eval f = f k := rfl
@[simp] theorem eval_average (p q : AlspachProbability K) (f : K → 𝕜) :
    (average p q).eval f = (1 / 2 : 𝕜) * (p.eval f + q.eval f) := rfl

theorem eval_map (p : AlspachProbability K) (g : K → L) (f : L → 𝕜) :
    (p.map g).eval f = p.eval (fun k => f (g k)) := by
  induction p with
  | point k => rfl
  | average p q hp hq => simp [map, hp, hq]

theorem eval_bind (p : AlspachProbability K) (g : K → AlspachProbability L) (f : L → 𝕜) :
    (p.bind g).eval f = p.eval (fun k => (g k).eval f) := by
  induction p with
  | point k => rfl
  | average p q hp hq => simp [bind, hp, hq]

@[simp] theorem eval_const (p : AlspachProbability K) (c : 𝕜) : p.eval (fun _ => c) = c := by
  induction p with
  | point k => rfl
  | average p q hp hq => rw [eval_average, hp, hq]; ring

theorem eval_add (p : AlspachProbability K) (f g : K → 𝕜) :
    p.eval (fun k => f k + g k) = p.eval f + p.eval g := by
  induction p with
  | point k => rfl
  | average p q hp hq => simp only [eval_average, hp, hq]; ring

theorem eval_sub (p : AlspachProbability K) (f g : K → 𝕜) :
    p.eval (fun k => f k - g k) = p.eval f - p.eval g := by
  induction p with
  | point k => rfl
  | average p q hp hq => simp only [eval_average, hp, hq]; ring

theorem eval_congr (p : AlspachProbability K) {f g : K → 𝕜}
    (h : ∀ k ∈ p.support, f k = g k) : p.eval f = p.eval g := by
  induction p with
  | point k => exact h k (Finset.mem_singleton_self k)
  | average p q hp hq =>
      rw [eval_average, eval_average,
        hp (fun k hk => h k (Finset.mem_union_left _ hk)),
        hq (fun k hk => h k (Finset.mem_union_right _ hk))]

theorem norm_eval_le (p : AlspachProbability K) (f : K → 𝕜) (C : ℝ)
    (h : ∀ k ∈ p.support, ‖f k‖ ≤ C) : ‖p.eval f‖ ≤ C := by
  induction p with
  | point k => exact h k (Finset.mem_singleton_self k)
  | average p q hp hq =>
      have hp' := hp (fun k hk => h k (Finset.mem_union_left _ hk))
      have hq' := hq (fun k hk => h k (Finset.mem_union_right _ hk))
      rw [eval_average, norm_mul]
      have hh : ‖(1 / 2 : 𝕜)‖ = (1 / 2 : ℝ) := by norm_num [norm_div]
      rw [hh]
      have ha := norm_add_le (p.eval f) (q.eval f)
      linarith

theorem continuous_eval {Y : Type*} [TopologicalSpace Y] (p : AlspachProbability K)
    (f : K → Y → 𝕜) (hf : ∀ k ∈ p.support, Continuous (f k)) :
    Continuous (fun y => p.eval (fun k => f k y)) := by
  induction p with
  | point k => exact hf k (Finset.mem_singleton_self k)
  | average p q hp hq =>
      exact continuous_const.mul ((hp (fun k hk => hf k (Finset.mem_union_left _ hk))).add
        (hq (fun k hk => hf k (Finset.mem_union_right _ hk))))

theorem representation_symm_apply [TopologicalSpace K] (M : JLMS.AtomicDualModel 𝕜 K)
    (p : AlspachProbability K) (f : JLMS.CZero 𝕜 K) :
    M.representation.symm p.vector f = p.eval f := by
  induction p with
  | point k => simp [vector, M.pointMass, JLMS.evaluation_apply]
  | average p q hp hq =>
      simp only [vector, map_smul, map_add, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, hp, hq, eval_average, smul_eq_mul]

end AlspachProbability
end Posets

