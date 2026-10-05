import ThesisCommon.Analysis.BandOrderConvergence
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Interval.Set.OrderIso
import Mathlib.Algebra.Module.Submodule.Equiv

/-! The lattice-isomorphism statement of PEMS Proposition 3.2.

The paper calls a linear map a lattice homomorphism when `x ⊓ y = 0`
implies `Ψ x ⊓ Ψ y = 0`. This is the raw infimum, not the absolute-value
disjointness relation. We use exactly that hypothesis. It implies positivity
by taking `y = 0`, and preservation of arbitrary infima by subtracting
`x ⊓ y` from both arguments. Injectivity then reflects order; bijectivity
produces an actual order isomorphism, rather than assuming one as data.

The resulting map preserves order-convergent filters and order intervals.
Only the additive lattice order and real linearity are needed: there is no
norm, topology, completeness, or countability assumption.
-/
noncomputable section
open Set Filter
namespace ThesisCommon
variable {E F : Type*}
variable [AddCommGroup E] [Module ℝ E] [Lattice E] [IsOrderedAddMonoid E]
variable [AddCommGroup F] [Module ℝ F] [Lattice F] [IsOrderedAddMonoid F]

/-- The paper's literal lattice-homomorphism condition, before bijectivity
or any order-isomorphism conclusion is imposed. -/
def IsLatticeLinearHom (Ψ : E →ₗ[ℝ] F) : Prop :=
  ∀ x y, x ⊓ y = 0 → Ψ x ⊓ Ψ y = 0

namespace IsLatticeLinearHom
variable {Ψ : E →ₗ[ℝ] F} (hΨ : IsLatticeLinearHom Ψ)
include hΨ

omit [IsOrderedAddMonoid E] [IsOrderedAddMonoid F] in
theorem nonneg {x : E} (hx : 0 ≤ x) : 0 ≤ Ψ x := by
  have h := hΨ x 0 (inf_eq_right.mpr hx)
  rw [map_zero] at h
  exact inf_eq_right.mp h

theorem monotone : Monotone Ψ := by
  intro x y hxy
  have h := hΨ.nonneg (sub_nonneg.mpr hxy)
  simpa only [map_sub, sub_nonneg] using h

/-- Subtracting the common infimum gives two positive vectors whose
infimum is zero. The source hypothesis then gives preservation of infima. -/
theorem map_inf (x y : E) : Ψ (x ⊓ y) = Ψ x ⊓ Ψ y := by
  have hzero : (x - (x ⊓ y)) ⊓ (y - (x ⊓ y)) = 0 := by
    rw [← inf_sub, sub_self]
  have h := hΨ (x - (x ⊓ y)) (y - (x ⊓ y)) hzero
  rw [map_sub, map_sub, ← inf_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem le_iff_of_injective (hinj : Function.Injective Ψ) {x y : E} :
    Ψ x ≤ Ψ y ↔ x ≤ y := by
  constructor
  · intro hxy
    apply inf_eq_left.mp
    apply hinj
    rw [hΨ.map_inf, inf_eq_left.mpr hxy]
  · exact fun hxy => hΨ.monotone hxy

/-- The actual order isomorphism deduced from the paper's linear
lattice-homomorphism condition and bijectivity. -/
def orderIso (hbij : Function.Bijective Ψ) : E ≃o F where
  toEquiv := (LinearEquiv.ofBijective Ψ hbij).toEquiv
  map_rel_iff' := hΨ.le_iff_of_injective hbij.injective

@[simp] theorem orderIso_apply (hbij : Function.Bijective Ψ) (x : E) :
    hΨ.orderIso hbij x = Ψ x := rfl

theorem map_abs (hbij : Function.Bijective Ψ) (x : E) : Ψ |x| = |Ψ x| := by
  change Ψ (x ⊔ -x) = Ψ x ⊔ -Ψ x
  simpa only [orderIso_apply, map_neg] using (hΨ.orderIso hbij).map_sup x (-x)

theorem inverse_nonneg (hbij : Function.Bijective Ψ) {y : F} (hy : 0 ≤ y) :
    0 ≤ (LinearEquiv.ofBijective Ψ hbij).symm y := by
  apply (hΨ.le_iff_of_injective hbij.injective).mp
  rw [map_zero]
  change 0 ≤ (LinearEquiv.ofBijective Ψ hbij) ((LinearEquiv.ofBijective Ψ hbij).symm y)
  simpa only [LinearEquiv.apply_symm_apply] using hy

/-- An arbitrary control family, its infimum, and its eventual bounds are
transported through the proved order isomorphism. -/
theorem orderConverges (hbij : Function.Bijective Ψ) {α : Type*}
    {f : α → E} {l : Filter α} {x : E} (hf : OrderConverges f l x) :
    OrderConverges (fun i => Ψ (f i)) l (Ψ x) := by
  obtain ⟨hl, B, hB, hBpos, hBdir, hBglb, hbound⟩ := hf
  refine ⟨hl, Ψ '' B, hB.image Ψ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact hΨ.nonneg (hBpos b hb)
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    obtain ⟨d, hd, hbd, hcd⟩ := hBdir b hb c hc
    exact ⟨Ψ d, ⟨d, hd, rfl⟩, hΨ.monotone hbd, hΨ.monotone hcd⟩
  · have h := (hΨ.orderIso hbij).isGLB_image'.mpr hBglb
    change IsGLB (Ψ '' B) (Ψ 0) at h
    simpa only [map_zero] using h
  · rintro _ ⟨b, hb, rfl⟩
    apply (hbound b hb).mono
    intro i hi
    have h := hΨ.monotone hi
    simpa only [hΨ.map_abs hbij, map_sub] using h

/-- Images of arbitrary closed order intervals are the corresponding
closed order intervals. This also includes empty intervals. -/
theorem image_Icc (hbij : Function.Bijective Ψ) (a b : E) :
    Ψ '' Icc a b = Icc (Ψ a) (Ψ b) :=
  (hΨ.orderIso hbij).image_Icc a b

theorem image_Icc_zero (hbij : Function.Bijective Ψ) (x : E) :
    Ψ '' Icc 0 x = Icc 0 (Ψ x) := by
  simpa only [map_zero] using hΨ.image_Icc hbij 0 x

end IsLatticeLinearHom

/-- Source consumer for Proposition 3.2. Order continuity is stated for
arbitrary proper filters, hence includes every directed net. Interval
preservation explicitly includes positivity and the positive intervals.
The hypotheses are precisely real linearity, the source's raw infimum-zero
condition, and bijectivity; the order isomorphism is a proved consequence. -/
theorem latticeLinearIso_orderContinuous_intervalPreserving
    (Ψ : E →ₗ[ℝ] F) (hΨ : IsLatticeLinearHom Ψ) (hbij : Function.Bijective Ψ) :
    (∀ {α : Type*} (f : α → E) (l : Filter α) (x : E),
      OrderConverges f l x → OrderConverges (fun i => Ψ (f i)) l (Ψ x)) ∧
    (∀ x, 0 ≤ x → 0 ≤ Ψ x) ∧
    ∀ x, 0 ≤ x → Ψ '' Icc 0 x = Icc 0 (Ψ x) := by
  refine ⟨fun f l x hf => hΨ.orderConverges hbij hf, fun x hx => hΨ.nonneg hx, ?_⟩
  exact fun x _ => hΨ.image_Icc_zero hbij x

end ThesisCommon
