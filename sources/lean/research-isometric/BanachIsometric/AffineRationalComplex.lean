import BanachIsometric.AffineRationalCone

/-! The explicit affine chains form an augmented chain complex. Their
realization into genuine singular chains is injective and commutes with the
boundary. The degree-zero cone formula includes the actual augmentation. -/

noncomputable section
namespace BanachIsometric.SingularPrism

def affineAugmentation (E : Type*) : AffineRationalChains E 0 →ₗ[ℚ] ℚ :=
  Finsupp.lsum ℚ (fun _ => LinearMap.id)

theorem affineAugmentation_single (E : Type*) (v : Fin 1 → E) (a : ℚ) :
    affineAugmentation E (Finsupp.single v a) = a := Finsupp.lsum_single _ _ _ _

theorem affineAugmentation_boundary (E : Type*) :
    (affineAugmentation E).comp (affineBoundary 0) = 0 := by
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, affineBoundary_single, map_sum, map_zsmul,
    affineAugmentation_single, LinearMap.zero_apply]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val • a) = 0
  simp [Fin.sum_univ_two]

theorem affineBoundary_cone_zero_single {E : Type*} (b : E) (v : Fin 1 → E) (a : ℚ) :
    affineBoundary 0 (affineCone b 0 (Finsupp.single v a)) =
      Finsupp.single v a - Finsupp.single (fun _ : Fin 1 => b) a := by
  rw [affineCone_single, affineBoundary_single]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val •
    Finsupp.single ((Fin.cons b v) ∘ i.succAbove) a) = _
  have hb : (Fin.cons b v) ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 => b := by
    funext j
    fin_cases j
    rfl
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_one_smul, affineCons_face_zero, hb, sub_eq_add_neg]

theorem affineBoundary_cone_zero {E : Type*} (b : E) (c : AffineRationalChains E 0) :
    affineBoundary 0 (affineCone b 0 c) =
      c - Finsupp.single (fun _ : Fin 1 => b) (affineAugmentation E c) := by
  have he : (affineBoundary 0).comp (affineCone b 0) =
      LinearMap.id - (Finsupp.lsingle (fun _ : Fin 1 => b)).comp (affineAugmentation E) := by
    apply Finsupp.lhom_ext
    intro v a
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      affineAugmentation_single, Finsupp.lsingle_apply] using affineBoundary_cone_zero_single b v a
  exact LinearMap.congr_fun he c

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineSingularSimplex_vertex {n : ℕ} (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    affineSingularSimplex v ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩ = v i := by
  classical
  change (∑ j, (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) j • v j) = v i
  simp [Pi.single_apply, eq_comm]

theorem affineSingularSimplex_injective (n : ℕ) :
    Function.Injective (affineSingularSimplex : (Fin (n + 1) → E) → RawSingularSimplex E n) := by
  intro v w h
  funext i
  simpa only [affineSingularSimplex_vertex] using
    ContinuousMap.congr_fun h ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩

theorem affineChainRealization_injective (n : ℕ) :
    Function.Injective (affineChainRealization (E := E) n) :=
  Finsupp.mapDomain_injective (affineSingularSimplex_injective n)

theorem affineBoundary_squared (n : ℕ) :
    (affineBoundary (E := E) n).comp (affineBoundary (n + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply affineChainRealization_injective n
  change affineChainRealization n (affineBoundary n (affineBoundary (n + 1) c)) =
    affineChainRealization n 0
  have h₁ := LinearMap.congr_fun (affineChainRealization_boundary n) (affineBoundary (n + 1) c)
  have h₂ := LinearMap.congr_fun (affineChainRealization_boundary (n + 1)) c
  simp only [LinearMap.comp_apply] at h₁ h₂
  calc
    _ = rawBoundary n (affineChainRealization (n + 1) (affineBoundary (n + 1) c)) := h₁.symm
    _ = rawBoundary n (rawBoundary (n + 1) (affineChainRealization (n + 2) c)) :=
      congrArg (rawBoundary n) h₂.symm
    _ = 0 := LinearMap.congr_fun (rawBoundary_squared n) (affineChainRealization (n + 2) c)
    _ = _ := (map_zero _).symm

end BanachIsometric.SingularPrism
