import BanachIsometric.ExactSectionMaps
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.FiberBundle.Basic

/-!
# The actual body-automorphism torsors and exact-section bundle

The structure group consists of genuine invertible continuous real-linear
operators preserving the fixed model body. Fibers consist of actual injective
operators with the prescribed range and exact body image. Their torsor
coordinates are constructed from those operators, rather than postulated.
-/

namespace BanachIsometric

open Set Filter Bundle
open scoped Topology NNReal

noncomputable section

section BodyGroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual real body automorphism group, with its inherited topology as
a subgroup of the units in the operator algebra. -/
def bodyAutomorphismGroup (S : Set E) : Subgroup (E →L[ℝ] E)ˣ where
  carrier := {g | (g : E →L[ℝ] E) '' S = S}
  one_mem' := by
    change (ContinuousLinearMap.id ℝ E) '' S = S
    exact image_id S
  mul_mem' := by
    intro g h hg hh
    change ((g : E →L[ℝ] E) * (h : E →L[ℝ] E)) '' S = S
    calc
      _ = (g : E →L[ℝ] E) '' ((h : E →L[ℝ] E) '' S) := by rw [image_image]; rfl
      _ = S := by rw [hh, hg]
  inv_mem' := by
    intro g hg
    let e := ContinuousLinearEquiv.ofUnit g
    change e.symm '' S = S
    calc
      e.symm '' S = e.symm '' (e '' S) := congrArg (Set.image e.symm) hg.symm
      _ = S := ContinuousLinearEquiv.symm_image_image e S

end BodyGroup

section Torsor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A fiber element is an actual operator identifying the model body with
the actual prescribed section. Its topology is the operator-subspace topology.
-/
abbrev ExactBodyMap (S : Set E) (K : Set F) (H : Submodule ℝ F) :=
  {A : E →L[ℝ] F // Function.Injective A ∧ LinearMap.range A.toLinearMap = H ∧
    A '' S = K ∩ (H : Set F)}

variable {S : Set E} {K : Set F} {H : Submodule ℝ F}

def exactBodyMapEquiv (A : ExactBodyMap S K H) : E ≃L[ℝ] H :=
  (LinearEquiv.ofBijective
    (A.val.toLinearMap.codRestrict H (fun x => by
      exact A.property.2.1.le (LinearMap.mem_range_self A.val.toLinearMap x)))
    ⟨fun x y h => A.property.1 (congrArg Subtype.val h), by
      intro y
      have hy : (y : F) ∈ LinearMap.range A.val.toLinearMap := A.property.2.1.ge y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩).toContinuousLinearEquiv

@[simp] theorem exactBodyMapEquiv_apply_coe (A : ExactBodyMap S K H) (x : E) :
    (exactBodyMapEquiv A x : F) = A.val x := rfl

theorem exactBodyMapEquiv_image_body (A : ExactBodyMap S K H) :
    exactBodyMapEquiv A '' S = {y : H | y.val ∈ K} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hmem : A.val x ∈ K ∩ (H : Set F) := by
      exact A.property.2.2.le (mem_image_of_mem A.val hx)
    exact hmem.1
  · intro hy
    have hmem : y.val ∈ A.val '' S := A.property.2.2.ge ⟨hy, y.property⟩
    obtain ⟨x, hx, hxy⟩ := hmem
    exact ⟨x, hx, Subtype.ext hxy⟩

/-- Right composition by an actual body automorphism. -/
def exactBodyMapRight (A : ExactBodyMap S K H) (g : bodyAutomorphismGroup S) :
    ExactBodyMap S K H := by
  let e := ContinuousLinearEquiv.ofUnit g.val
  refine ⟨A.val.comp (g.val : E →L[ℝ] E), A.property.1.comp e.injective, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact A.property.2.1.le (LinearMap.mem_range_self A.val.toLinearMap (e x))
    · intro hy
      obtain ⟨x, rfl⟩ := A.property.2.1.ge hy
      refine ⟨e.symm x, ?_⟩
      change A.val (e (e.symm x)) = A.val x
      rw [ContinuousLinearEquiv.apply_symm_apply]
  · calc
      _ = A.val '' ((g.val : E →L[ℝ] E) '' S) := by rw [image_image]; rfl
      _ = A.val '' S := congrArg (Set.image A.val) g.property
      _ = K ∩ (H : Set F) := A.property.2.2

/-- The unique actual automorphism changing one exact frame to another. -/
def exactBodyMapCoordinate (A B : ExactBodyMap S K H) : bodyAutomorphismGroup S := by
  let eA := exactBodyMapEquiv A
  let eB := exactBodyMapEquiv B
  let e := eB.trans eA.symm
  refine ⟨e.toUnit, ?_⟩
  change e '' S = S
  calc
    _ = eA.symm '' (eB '' S) := by rw [image_image]; rfl
    _ = eA.symm '' {y : H | y.val ∈ K} := by rw [exactBodyMapEquiv_image_body]
    _ = eA.symm '' (eA '' S) := by rw [exactBodyMapEquiv_image_body]
    _ = S := ContinuousLinearEquiv.symm_image_image eA S

theorem exactBodyMapCoordinate_apply (A B : ExactBodyMap S K H) (x : E) :
    ((exactBodyMapCoordinate A B).val : E →L[ℝ] E) x =
      (exactBodyMapEquiv A).symm (exactBodyMapEquiv B x) := rfl

theorem exactBodyMapRight_coordinate (A B : ExactBodyMap S K H) :
    exactBodyMapRight A (exactBodyMapCoordinate A B) = B := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change A.val (((exactBodyMapCoordinate A B).val : E →L[ℝ] E) x) = B.val x
  rw [exactBodyMapCoordinate_apply]
  exact congrArg Subtype.val
    ((exactBodyMapEquiv A).apply_symm_apply (exactBodyMapEquiv B x))

omit [FiniteDimensional ℝ E] in
theorem exactBodyMapRight_injective (A : ExactBodyMap S K H) :
    Function.Injective (exactBodyMapRight A) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  apply ContinuousLinearMap.ext
  intro x
  apply A.property.1
  exact congrArg (fun B : ExactBodyMap S K H => B.val x) hgh

/-- Every nonempty exact-map fiber is a torsor for the actual body
automorphism group. -/
def exactBodyMapTorsorEquiv (A : ExactBodyMap S K H) :
    bodyAutomorphismGroup S ≃ ExactBodyMap S K H where
  toFun := exactBodyMapRight A
  invFun := exactBodyMapCoordinate A
  left_inv g := by
    apply exactBodyMapRight_injective A
    exact exactBodyMapRight_coordinate A (exactBodyMapRight A g)
  right_inv := exactBodyMapRight_coordinate A

end Torsor

section LocalLeftInverses

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Actual local operator-Lipschitz left inverses are constructed by the
Gram formula. The reference operator is isometric, as in the exact-map
construction. Invertibility and local Lipschitz regularity are proved.
-/
theorem exists_lipschitz_local_leftInverse_family
    (A : P → E →L[ℝ] F) (a₀ : P) {U : Set P} (hU : U ∈ 𝓝 a₀)
    {L : ℝ≥0} (hA : LipschitzOnWith L A U)
    (hGram : (A a₀).adjoint.comp (A a₀) = ContinuousLinearMap.id ℝ E) :
    ∃ B : P → F →L[ℝ] E, ∃ W : Set P, ∃ K : ℝ≥0,
      IsOpen W ∧ a₀ ∈ W ∧ W ⊆ U ∧ B a₀ = (A a₀).adjoint ∧
        LipschitzOnWith K B W ∧
        ∀ a ∈ W, (B a).comp (A a) = ContinuousLinearMap.id ℝ E := by
  have hAdj : LipschitzOnWith L (fun a => (A a).adjoint) U := by
    simpa only [one_mul] using ContinuousLinearMap.adjoint.lipschitz.lipschitzOnWith.comp hA
      (fun _ _ => mem_univ _)
  let G : P → E →L[ℝ] E := fun a => (A a).adjoint.comp (A a)
  obtain ⟨VG, KG, hVG, ha₀VG, hVGU, hG⟩ := exists_lipschitzOnWith_clm_comp_family
    (fun a => (A a).adjoint) A a₀ hU hAdj hA
  have hG0 : G a₀ = 1 := hGram
  have hunit0 : IsUnit (G a₀) := by rw [hG0]; exact isUnit_one
  obtain ⟨VI, KI, hVI, ha₀VI, hVIVG, hInv⟩ :=
    exists_lipschitzOnWith_ringInverse_family G a₀ (hVG.mem_nhds ha₀VG) hG hunit0
  have hGcont : ContinuousAt G a₀ := hG.continuousOn.continuousAt (hVG.mem_nhds ha₀VG)
  have hGunits : G ⁻¹' {T | IsUnit T} ∈ 𝓝 a₀ :=
    hGcont.preimage_mem_nhds (Units.isOpen.mem_nhds hunit0)
  obtain ⟨W₀, hW₀sub, hW₀, ha₀W₀⟩ :=
    mem_nhds_iff.mp (inter_mem (hVI.mem_nhds ha₀VI) hGunits)
  have hW₀VI : W₀ ⊆ VI := hW₀sub.trans inter_subset_left
  have hW₀U : W₀ ⊆ U := hW₀VI.trans (hVIVG.trans hVGU)
  let B : P → F →L[ℝ] E := fun a => (Ring.inverse (G a)).comp (A a).adjoint
  obtain ⟨W, KW, hW, ha₀W, hWW₀, hB⟩ := exists_lipschitzOnWith_clm_comp_family
    (fun a => Ring.inverse (G a)) (fun a => (A a).adjoint) a₀
    (hW₀.mem_nhds ha₀W₀) (hInv.mono hW₀VI) (hAdj.mono hW₀U)
  refine ⟨B, W, KW, hW, ha₀W, hWW₀.trans hW₀U, ?_, hB, ?_⟩
  · change (Ring.inverse (G a₀)).comp (A a₀).adjoint = _
    rw [hG0, Ring.inverse_one]
    exact ContinuousLinearMap.id_comp _
  · intro a ha
    have hunit : IsUnit (G a) := (hW₀sub (hWW₀ ha)).2
    calc
      (B a).comp (A a) = (Ring.inverse (G a)).comp (G a) := by
        rw [ContinuousLinearMap.comp_assoc]
      _ = ContinuousLinearMap.id ℝ E := Ring.inverse_mul_cancel _ hunit

end LocalLeftInverses

end
end BanachIsometric
