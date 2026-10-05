import ThesisCommon.Analysis.SigmaComplexLatticeStructure
import ThesisCommon.Analysis.SigmaComplexClassPrimariness
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Tactic.FunProp

/-! The actual pointwise complex Banach lattice C(K,ℂ), with real part C(K,ℝ)
and the least-upper-bound definition of complex modulus. -/
noncomputable section
universe u
namespace ThesisCommon

instance complexCKRealOrderedAdd (K : Type u) [TopologicalSpace K] :
    IsOrderedAddMonoid C(K,ℝ) where
  add_le_add_left := by
    intro f g h a x
    exact add_le_add_left (h x) (a x)

instance complexCKRealOrderedModule (K : Type u) [TopologicalSpace K] :
    IsOrderedModule ℝ C(K,ℝ) where
  smul_le_smul_of_nonneg_left := by
    intro r hr f g h x
    exact mul_le_mul_of_nonneg_left (h x) hr
  smul_le_smul_of_nonneg_right := by
    intro f hf r s h x
    exact mul_le_mul_of_nonneg_right h (hf x)

instance complexCKRealSolidNorm (K : Type u) [TopologicalSpace K] [CompactSpace K] :
    HasSolidNorm C(K,ℝ) where
  solid := by
    intro f g h
    apply (ContinuousMap.norm_le _ (norm_nonneg g)).mpr
    intro x
    exact (show ‖f x‖ ≤ ‖g x‖ from HasSolidNorm.solid (h x)).trans (g.norm_coe_le_norm x)

def complexCKRealLattice (K : Type u) [TopologicalSpace K] [CompactSpace K] : RealBanachLattice.{u} :=
  { Carrier := C(K,ℝ)
    lattice := inferInstance
    orderedAdd := inferInstance
    orderedModule := inferInstance
    solidNorm := inferInstance }

def complexCKRe {K : Type u} [TopologicalSpace K] (f : C(K,ℂ)) : C(K,ℝ) :=
  ⟨fun x => (f x).re,Complex.continuous_re.comp f.continuous⟩

def complexCKIm {K : Type u} [TopologicalSpace K] (f : C(K,ℂ)) : C(K,ℝ) :=
  ⟨fun x => (f x).im,Complex.continuous_im.comp f.continuous⟩

def complexCKCoordinates (K : Type u) [TopologicalSpace K] [CompactSpace K] :
    C(K,ℂ) ≃L[ℝ] (C(K,ℝ) × C(K,ℝ)) := by
  let e : C(K,ℂ) ≃ₗ[ℝ] (C(K,ℝ) × C(K,ℝ)) :=
    { toFun := fun f => (complexCKRe f,complexCKIm f)
      invFun := fun fg => ⟨fun x => (fg.1 x : ℂ) + (fg.2 x : ℂ) * Complex.I,by fun_prop⟩
      left_inv := by intro f; ext x; exact Complex.re_add_im (f x)
      right_inv := by intro fg; apply Prod.ext <;> ext x <;> simp [complexCKRe,complexCKIm]
      map_add' := by intro f g; apply Prod.ext <;> ext x <;> simp [complexCKRe,complexCKIm]
      map_smul' := by intro r f; apply Prod.ext <;> ext x <;> simp [complexCKRe,complexCKIm] }
  apply LinearEquiv.toContinuousLinearEquivOfBounds e 1 2
  · intro f
    change max ‖complexCKRe f‖ ‖complexCKIm f‖ ≤ 1 * ‖f‖
    rw [one_mul]
    apply max_le
    · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      exact (Complex.abs_re_le_norm (f x)).trans (f.norm_coe_le_norm x)
    · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      exact (Complex.abs_im_le_norm (f x)).trans (f.norm_coe_le_norm x)
  · intro fg
    apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ 2 * ‖fg‖)).mpr
    intro x
    change ‖(fg.1 x : ℂ)+(fg.2 x : ℂ)*Complex.I‖ ≤ 2 * max ‖fg.1‖ ‖fg.2‖
    have hnorm : ‖(fg.1 x : ℂ)+(fg.2 x : ℂ)*Complex.I‖ ≤ |fg.1 x|+|fg.2 x| := by
      simpa using norm_add_le (fg.1 x : ℂ) ((fg.2 x : ℂ)*Complex.I)
    have h1 := fg.1.norm_coe_le_norm x
    have h2 := fg.2.norm_coe_le_norm x
    have h3 := le_max_left ‖fg.1‖ ‖fg.2‖
    have h4 := le_max_right ‖fg.1‖ ‖fg.2‖
    rw [Real.norm_eq_abs] at h1 h2
    linarith

@[simp] theorem complexCKCoordinates_apply {K : Type u} [TopologicalSpace K] [CompactSpace K]
    (f : C(K,ℂ)) : complexCKCoordinates K f = (complexCKRe f,complexCKIm f) := rfl

theorem complexCKCoordinates_I {K : Type u} [TopologicalSpace K] [CompactSpace K]
    (f : C(K,ℂ)) :
    complexCKCoordinates K (Complex.I • f) = (-(complexCKCoordinates K f).2,(complexCKCoordinates K f).1) := by
  apply Prod.ext <;> ext x <;> simp [complexCKRe,complexCKIm]

def complexCKModulus {K : Type u} [TopologicalSpace K] (f : C(K,ℂ)) : C(K,ℝ) :=
  ⟨fun x => ‖f x‖,f.continuous.norm⟩

theorem complexCKModulus_spec {K : Type u} [TopologicalSpace K] [CompactSpace K]
    (f : C(K,ℂ)) :
    IsComplexLatticeModulus (complexCKRe f) (complexCKIm f) (complexCKModulus f) := by
  constructor
  · rintro _ ⟨c,hc,rfl⟩ x
    exact complexLatticePhase_scalar_le (f x).re (f x).im c hc
  · intro g hg x
    obtain ⟨c,hc,he⟩ := complexLatticePhase_scalar_attains (f x).re (f x).im
    have h := hg ⟨c,hc,rfl⟩ x
    change c.re*(f x).re-c.im*(f x).im ≤ g x at h
    change ‖f x‖ ≤ g x
    rw [he] at h
    exact h

theorem complexCKModulus_norm {K : Type u} [TopologicalSpace K] [CompactSpace K]
    (f : C(K,ℂ)) : ‖f‖ = ‖complexCKModulus f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    simpa only [complexCKModulus,ContinuousMap.coe_mk,norm_norm] using
      (complexCKModulus f).norm_coe_le_norm x
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    exact (norm_norm (f x)).le.trans (f.norm_coe_le_norm x)

/-- The faithful complex Banach lattice of continuous complex-valued functions. -/
def complexCKBanachLattice (K : Type u) [TopologicalSpace K] [CompactSpace K] :
    ComplexBanachLattice.{u} :=
  { Carrier := C(K,ℂ)
    RealPart := complexCKRealLattice K
    coordinates := complexCKCoordinates K
    coordinates_I := complexCKCoordinates_I
    modulus := complexCKModulus
    modulus_spec := complexCKModulus_spec
    norm_modulus := complexCKModulus_norm }

theorem complex_ck_isomorphicToBanachLattice (K : Compactum.{u}) :
    IsomorphicToComplexBanachLattice C(K,ℂ) :=
  ⟨complexCKBanachLattice K,⟨ContinuousLinearEquiv.refl ℂ C(K,ℂ)⟩⟩

theorem isomorphicToComplexCK_implies_lattice {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : IsomorphicToComplexCK E) : IsomorphicToComplexBanachLattice E := by
  obtain ⟨K,⟨e⟩⟩ := h
  obtain ⟨F,⟨f⟩⟩ := complex_ck_isomorphicToBanachLattice K
  exact ⟨F,⟨e.trans f⟩⟩

end ThesisCommon

