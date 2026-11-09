import SurveyStatements.P1TriangularSequence

/-! A direct double-Goldstine construction of the bounded nonreflexive
sequence used in the source assembly. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
open Set Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

local instance : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
local instance : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
local instance : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
local instance : NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ X)) := inferInstance

theorem weak_limit_mem_closedSubmodule (S : Submodule ℂ X)
    (hS : IsClosed (S : Set X)) (s : ℕ → X) (hs : ∀ n, s n ∈ S)
    {x : X} (hx : ∀ f : StrongDual ℂ X, Tendsto (fun n => f (s n)) atTop (𝓝 (f x))) :
    x ∈ S := by
  by_contra hnot
  obtain ⟨f, _, hvanish, hfx⟩ := closedSubmodule_exists_bounded_annihilator S hS hnot
  have hzero : Tendsto (fun n => f (s n)) atTop (𝓝 0) := by
    have heq : (fun n => f (s n)) = (fun _ : ℕ => (0 : ℂ)) :=
      funext fun n => hvanish (s n) (hs n)
    rw [heq]
    exact tendsto_const_nhds
  exact hfx (tendsto_nhds_unique (hx f) hzero)

theorem bounded_functionals_vanish_on_closedSpan (s : ℕ → X)
    (f : ℕ → StrongDual ℂ X) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hs : ∀ k, Tendsto (fun n => f n (s k)) atTop (𝓝 0))
    {x : X} (hx : x ∈ (Submodule.span ℂ (range s)).topologicalClosure) :
    Tendsto (fun n => f n x) atTop (𝓝 0) := by
  have hspan (y : X) (hy : y ∈ Submodule.span ℂ (range s)) :
      Tendsto (fun n => f n y) atTop (𝓝 0) := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact hs k
    | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    | add y z hy hz ihy ihz => simpa only [map_add, add_zero] using ihy.add ihz
    | smul a y hy ih =>
      simpa only [map_smul, smul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).smul ih
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hxcl : x ∈ closure (Submodule.span ℂ (range s) : Set X) := hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hxcl (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hspan y hy) (ε / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have hxy' : ‖x - y‖ < ε / 2 := by simpa only [dist_eq_norm] using hxy
  have hyn : ‖f n y‖ < ε / 2 := by simpa only [dist_zero_right] using hN n hn
  have hbound : ‖f n (x - y)‖ ≤ ‖x - y‖ :=
    ((f n).le_opNorm (x - y)).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hf n) (norm_nonneg (x - y)))
  have hnorm : ‖f n x‖ ≤ ‖f n (x - y)‖ + ‖f n y‖ := by
    calc
      ‖f n x‖ = ‖f n (x - y) + f n y‖ := by rw [map_sub, sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [dist_zero_right]
  linarith

theorem nonreflexive_exists_bounded_no_weakly_convergent_subsequence [CompleteSpace X]
    (hRef : ¬ SurveyStatements.P4.IsReflexiveNormedSpace ℂ X) :
    ∃ s : ℕ → X, (∀ n, ‖s n‖ ≤ 1) ∧
      ¬ ∃ ν : ℕ → ℕ, StrictMono ν ∧ ∃ x : X,
        ∀ f : StrongDual ℂ X, Tendsto (fun n => f (s (ν n))) atTop (𝓝 (f x)) := by
  classical
  let S : Submodule ℂ (StrongDual ℂ (StrongDual ℂ X)) :=
    SurveyStatements.P4.bidualImage ℂ X
  have hnot : ¬ ∀ z : StrongDual ℂ (StrongDual ℂ X), z ∈ S := by
    intro h
    exact hRef h
  obtain ⟨z, hz⟩ := not_forall.mp hnot
  have hpos : 0 < ‖z‖ + 1 := by positivity
  have hne : ((‖z‖ + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  let ξ : StrongDual ℂ (StrongDual ℂ X) := ((‖z‖ + 1 : ℝ) : ℂ)⁻¹ • z
  have hξnorm : ‖ξ‖ ≤ 1 := by
    simp only [ξ, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    rw [inv_mul_le_iff₀ hpos]
    linarith
  have hξnot : ξ ∉ S := by
    intro hξS
    have h := S.smul_mem (((‖z‖ + 1 : ℝ) : ℂ)) hξS
    have heq : (((‖z‖ + 1 : ℝ) : ℂ)) • ξ = z := by
      simp only [ξ, smul_smul, mul_inv_cancel₀ hne, one_smul]
    exact hz (heq ▸ h)
  obtain ⟨ψ, hψnorm, hψvanish, hψξ⟩ := closedSubmodule_exists_bounded_annihilator S
    (SurveyStatements.P4.isClosed_bidualImage (𝕜 := ℂ) (F := X)) hξnot
  have hvanish (x : X) : ψ (NormedSpace.inclusionInDoubleDual ℂ X x) = 0 :=
    hψvanish _ ⟨x, rfl⟩
  obtain ⟨s, f, hsnorm, hfnorm, hcol, hlow, hupp⟩ :=
    exists_goldstine_triangular_sequence ξ ψ hξnorm hψnorm hvanish
  refine ⟨s, hsnorm, ?_⟩
  rintro ⟨ν, hν, x, hx⟩
  let V := (Submodule.span ℂ (range s)).topologicalClosure
  have hxV : x ∈ V := weak_limit_mem_closedSubmodule V
    (Submodule.isClosed_topologicalClosure _) (s ∘ ν)
    (fun n => (Submodule.span ℂ (range s)).le_topologicalClosure (Submodule.subset_span ⟨ν n, rfl⟩))
    hx
  have hfxzero := bounded_functionals_vanish_on_closedSpan s f hfnorm hlow hxV
  have heq (k : ℕ) : f k x = ξ (f k) :=
    tendsto_nhds_unique (hx (f k)) ((hupp k).comp hν.tendsto_atTop)
  have hfxψ : Tendsto (fun n => f n x) atTop (𝓝 (ψ ξ)) := by
    simpa only [heq] using hcol
  exact hψξ (tendsto_nhds_unique hfxψ hfxzero)

end SurveyStatements.P1
