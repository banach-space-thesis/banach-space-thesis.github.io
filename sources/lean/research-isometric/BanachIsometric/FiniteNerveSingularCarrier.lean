import BanachIsometric.FiniteNerveImageCarrier
import BanachIsometric.FiniteNerveConeReducedContraction

/-! Actual nested carriers of literal singular simplices. A simplex whose
image lies in one open vertex star has an actual finite cone carrier, with
explicit finite-chain fillers in all positive degrees and in augmented
degree zero, as well as actual singular acyclicity of its carrier space. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open SingularPrism
variable {ι : Type} [LinearOrder ι] [Fintype ι]

def singularVertexImage (K : Complex ι) {n : ℕ} (σ : RawSingularSimplex K.space n) :
    Set (ι → ℝ) := Set.range (fun z => (σ z).val)

def singularFaceCarrier (K : Complex ι) {n : ℕ} (σ : RawSingularSimplex K.space n) : Complex ι :=
  K.faceImageCarrier (singularVertexImage K σ)

theorem singularVertexImage_subset (K : Complex ι) {n : ℕ} (σ : RawSingularSimplex K.space n) :
    singularVertexImage K σ ⊆ K.space := by
  rintro w ⟨z, rfl⟩
  exact (σ z).property

theorem singularVertexImage_nonempty (K : Complex ι) {n : ℕ} (σ : RawSingularSimplex K.space n) :
    (singularVertexImage K σ).Nonempty :=
  ⟨(σ (stdSimplex.vertex 0)).val, stdSimplex.vertex 0, rfl⟩

theorem singularFaceCarrier_face_subset (K : Complex ι) {n : ℕ}
    (σ : RawSingularSimplex K.space (n + 1)) (i : Fin (n + 2)) :
    (singularFaceCarrier K (σ.comp (face i))).faces ⊆ (singularFaceCarrier K σ).faces := by
  apply K.faceImageCarrier_mono
  rintro w ⟨z, rfl⟩
  exact ⟨face i z, rfl⟩

def singularCarrierSimplex (K : Complex ι) {n : ℕ} (σ : RawSingularSimplex K.space n) :
    RawSingularSimplex (singularFaceCarrier K σ).space n where
  toFun z := ⟨(σ z).val, K.subset_space_faceImageCarrier (singularVertexImage_subset K σ) ⟨z, rfl⟩⟩
  continuous_toFun := (continuous_subtype_val.comp σ.continuous).subtype_mk _

theorem singularFaceCarrier_insert (K : Complex ι) {n : ℕ} (σ : RawSingularSimplex K.space n)
    (i : ι) (hi : ∀ z, 0 < (σ z).val i) (s : Finset ι)
    (hs : s ∈ (singularFaceCarrier K σ).faces) :
    insert i s ∈ (singularFaceCarrier K σ).faces :=
  K.insert_mem_faceImageCarrier_faces i (by rintro _ ⟨z, rfl⟩; exact hi z) s hs

theorem singularFaceCarrier_apex_mem (K : Complex ι) {n : ℕ}
    (σ : RawSingularSimplex K.space n) (i : ι) (hi : ∀ z, 0 < (σ z).val i) :
    {i} ∈ (singularFaceCarrier K σ).faces := by
  let z : Simplex n := stdSimplex.vertex (0 : Fin (n + 1))
  obtain ⟨s, hs, _hσs⟩ := (Complex.mem_space_iff _ _).mp (singularCarrierSimplex K σ z).property
  apply (singularFaceCarrier K σ).downward _ (singularFaceCarrier_insert K σ i hi s hs) _
  · exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
  · exact Finset.singleton_nonempty _

theorem singularFaceCarrier_cycle_fills (K : Complex ι) {m : ℕ}
    (σ : RawSingularSimplex K.space m) (i : ι) (hi : ∀ z, 0 < (σ z).val i)
    (n : ℕ) (x : FiniteRationalChains (singularFaceCarrier K σ) (n + 1))
    (hx : finiteRationalBoundary (singularFaceCarrier K σ) n x = 0) :
    ∃ y : FiniteRationalChains (singularFaceCarrier K σ) (n + 2),
      finiteRationalBoundary (singularFaceCarrier K σ) (n + 1) y = x :=
  exists_boundary_of_cycle_cone (singularFaceCarrier K σ) i
    (singularFaceCarrier_insert K σ i hi) n x hx

theorem singularFaceCarrier_augmented_cycle_fills (K : Complex ι) {m : ℕ}
    (σ : RawSingularSimplex K.space m) (i : ι) (hi : ∀ z, 0 < (σ z).val i)
    (x : FiniteRationalChains (singularFaceCarrier K σ) 0)
    (hx : finiteAugmentation (singularFaceCarrier K σ) x = 0) :
    ∃ y : FiniteRationalChains (singularFaceCarrier K σ) 1,
      finiteRationalBoundary (singularFaceCarrier K σ) 0 y = x :=
  exists_boundary_of_augmentation_zero_cone (singularFaceCarrier K σ) i
    (singularFaceCarrier_insert K σ i hi) (singularFaceCarrier_apex_mem K σ i hi) x hx

theorem singularFaceCarrier_contractibleSpace (K : Complex ι) {n : ℕ}
    (σ : RawSingularSimplex K.space n) (i : ι) (hi : ∀ z, 0 < (σ z).val i) :
    ContractibleSpace (singularFaceCarrier K σ).space :=
  K.faceImageCarrier_contractibleSpace (singularVertexImage_subset K σ)
    (singularVertexImage_nonempty K σ) i (by rintro _ ⟨z, rfl⟩; exact hi z)

end BanachIsometric.FiniteNerve
