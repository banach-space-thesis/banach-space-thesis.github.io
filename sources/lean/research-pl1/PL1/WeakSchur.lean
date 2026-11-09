import PL1.Definitions
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Weak convergence, the Schur property, and Dunford–Pettis projections

These lemmas concern the reviewed predicates in `PL1.Definitions`. In particular,
all weak convergence statements use the full continuous dual. No construction of
the main counterexamples is assumed or asserted in this module.
-/

noncomputable section

open Filter
open scoped Topology

namespace PL1

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Every continuous linear map preserves weak sequential convergence. -/
theorem WeaklyConverges.map {x : ℕ → E} {a : E}
    (hx : WeaklyConverges 𝕜 E x a) (T : E →L[𝕜] F) :
    WeaklyConverges 𝕜 F (fun n => T (x n)) (T a) := by
  intro φ
  exact hx (φ.comp T)

/-- Norm convergence implies weak convergence. -/
theorem weaklyConverges_of_tendsto {x : ℕ → E} {a : E}
    (hx : Tendsto x atTop (𝓝 a)) : WeaklyConverges 𝕜 E x a := by
  intro φ
  exact (φ.continuous.tendsto a).comp hx

theorem weaklyConverges_const (a : E) :
    WeaklyConverges 𝕜 E (fun _ : ℕ => a) a :=
  weaklyConverges_of_tendsto tendsto_const_nhds

theorem WeaklyConverges.sub {x y : ℕ → E} {a b : E}
    (hx : WeaklyConverges 𝕜 E x a) (hy : WeaklyConverges 𝕜 E y b) :
    WeaklyConverges 𝕜 E (fun n => x n - y n) (a - b) := by
  intro φ
  simpa only [map_sub] using (hx φ).sub (hy φ)

/-- Subtracting the proposed limit converts weak convergence into weak nullity. -/
theorem weaklyConverges_iff_sub_const {x : ℕ → E} {a : E} :
    WeaklyConverges 𝕜 E x a ↔
      WeaklyConverges 𝕜 E (fun n => x n - a) 0 := by
  constructor
  · intro hx
    simpa using hx.sub (weaklyConverges_const a)
  · intro hx φ
    have h := (hx φ).add (tendsto_const_nhds (x := φ a))
    simpa only [map_sub, map_zero, sub_add_cancel, zero_add] using h

/-- A continuous linear equivalence preserves and reflects weak convergence. -/
theorem weaklyConverges_equiv_iff (e : E ≃L[𝕜] F) {x : ℕ → E} {a : E} :
    WeaklyConverges 𝕜 F (fun n => e (x n)) (e a) ↔
      WeaklyConverges 𝕜 E x a := by
  constructor
  · intro hx
    simpa using hx.map e.symm.toContinuousLinearMap
  · intro hx
    exact hx.map e.toContinuousLinearMap

/-- The Schur property is invariant under Banach-space isomorphisms. -/
theorem hasSchurProperty_equiv_iff (e : E ≃L[𝕜] F) :
    HasSchurProperty 𝕜 E ↔ HasSchurProperty 𝕜 F := by
  constructor
  · intro h x a hx
    have h' := h (fun n => e.symm (x n)) (e.symm a)
      (hx.map e.symm.toContinuousLinearMap)
    simpa [Function.comp_def] using (e.continuous.tendsto (e.symm a)).comp h'
  · intro h x a hx
    have h' := h (fun n => e (x n)) (e a) (hx.map e.toContinuousLinearMap)
    simpa [Function.comp_def] using (e.symm.continuous.tendsto (e a)).comp h'

/-- Every linear subspace of a Schur space is Schur, with its induced norm. -/
theorem HasSchurProperty.submodule (h : HasSchurProperty 𝕜 E)
    (V : Submodule 𝕜 E) : HasSchurProperty 𝕜 V := by
  intro x a hx
  apply tendsto_subtype_rng.mpr
  exact h _ _ (hx.map V.subtypeL)

/-- A space isomorphic to a closed subspace of a Schur space is Schur. -/
theorem HasSchurProperty.of_containsIsomorphicCopy (h : HasSchurProperty 𝕜 E)
    (hcopy : ContainsIsomorphicCopy 𝕜 F E) : HasSchurProperty 𝕜 F := by
  obtain ⟨V, _, ⟨e⟩⟩ := hcopy
  exact (hasSchurProperty_equiv_iff e).mpr (h.submodule V)

/-- Consequently a Schur space cannot contain an isomorphic copy of a non-Schur space. -/
theorem HasSchurProperty.not_containsIsomorphicCopy (h : HasSchurProperty 𝕜 E)
    (hF : ¬ HasSchurProperty 𝕜 F) : ¬ ContainsIsomorphicCopy 𝕜 F E := by
  intro hcopy
  exact hF (h.of_containsIsomorphicCopy hcopy)

/-- Any operator with Schur codomain is Dunford–Pettis. -/
theorem HasSchurProperty.isDunfordPettis (h : HasSchurProperty 𝕜 F)
    (T : E →L[𝕜] F) : IsDunfordPettis T := by
  intro x a hx
  exact h _ _ (hx.map T)

/-- Precomposition by a bounded operator preserves the Dunford–Pettis property. -/
theorem IsDunfordPettis.comp_right {T : F →L[𝕜] G}
    (hT : IsDunfordPettis T) (S : E →L[𝕜] F) : IsDunfordPettis (T.comp S) := by
  intro x a hx
  exact hT _ _ (hx.map S)

/-- Postcomposition by a bounded operator preserves the Dunford–Pettis property. -/
theorem IsDunfordPettis.comp_left {T : E →L[𝕜] F}
    (hT : IsDunfordPettis T) (S : F →L[𝕜] G) : IsDunfordPettis (S.comp T) := by
  intro x a hx
  exact (S.continuous.tendsto (T a)).comp (hT x a hx)

/-- The reviewed all-limits definition agrees with the weak-null definition in the paper. -/
theorem isDunfordPettis_iff_weaklyNull (T : E →L[𝕜] F) :
    IsDunfordPettis T ↔
      ∀ x : ℕ → E, WeaklyConverges 𝕜 E x 0 →
        Tendsto (fun n => T (x n)) atTop (𝓝 0) := by
  constructor
  · intro h x hx
    simpa only [map_zero] using h x 0 hx
  · intro h x a hx
    have h' := h (fun n => x n - a) (weaklyConverges_iff_sub_const.mp hx)
    have h'' := h'.add (tendsto_const_nhds (x := T a))
    simpa only [map_sub, sub_add_cancel, zero_add] using h''

/-- An idempotent continuous operator is the identity on its range. -/
theorem IsProjection.apply_range {P : E →L[𝕜] E} (hP : IsProjection P)
    (x : P.range) : P x = (x : E) := by
  obtain ⟨y, hy⟩ := x.property
  change P y = (x : E) at hy
  have h := DFunLike.congr_fun hP y
  simpa only [ContinuousLinearMap.comp_apply, hy] using h

/-- The range of any continuous projection is closed. -/
theorem IsProjection.isClosed_range {P : E →L[𝕜] E} (hP : IsProjection P) :
    IsClosed (P.range : Set E) := by
  apply ContinuousLinearMap.IsIdempotentElem.isClosed_range
  exact hP

/-- The key abstract implication in Proposition 4.3: a Dunford–Pettis projection
has a Schur range, with the actual inherited range norm. -/
theorem IsProjection.hasSchurProperty_range {P : E →L[𝕜] E}
    (hP : IsProjection P) (hDP : IsDunfordPettis P) :
    HasSchurProperty 𝕜 P.range := by
  intro x a hx
  apply tendsto_subtype_rng.mpr
  have h := hDP (fun n => (x n : E)) (a : E) (hx.map P.range.subtypeL)
  simpa only [hP.apply_range] using h

/-- An operator whose actual range is Schur is Dunford–Pettis. No idempotence
is needed for this direction. -/
theorem isDunfordPettis_of_hasSchurProperty_range (T : E →L[𝕜] F)
    (h : HasSchurProperty 𝕜 T.range) : IsDunfordPettis T := by
  intro x a hx
  have h' := h (fun n => T.rangeRestrict (x n)) (T.rangeRestrict a)
    (hx.map T.rangeRestrict)
  exact tendsto_subtype_rng.mp h'

/-- A continuous projection is Dunford–Pettis exactly when its range is Schur. -/
theorem IsProjection.isDunfordPettis_iff_hasSchurProperty_range
    {P : E →L[𝕜] E} (hP : IsProjection P) :
    IsDunfordPettis P ↔ HasSchurProperty 𝕜 P.range :=
  ⟨hP.hasSchurProperty_range, isDunfordPettis_of_hasSchurProperty_range P⟩

end PL1
