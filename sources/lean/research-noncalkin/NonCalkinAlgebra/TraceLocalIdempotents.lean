import NonCalkinAlgebra.TraceIdempotents
import NonCalkinAlgebra.RieszCircleIdempotence
import NonCalkinAlgebra.FiniteSpectrumEmbedding
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open Complex Filter Metric Set
open scoped Topology
universe u
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

private theorem halfCircle_resolvent (e : A) (he : e * e = e)
    (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (1 / 2)) : z ∈ resolventSet ℂ e := by
  have hn : ‖z‖ = (1 / 2 : ℝ) := by simpa [mem_sphere, dist_zero_right] using hz
  have hz₀ : z ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  have hz₁ : z ≠ 1 := by intro h; rw [h, norm_one] at hn; norm_num at hn
  exact ⟨⟨algebraMap ℂ A z - e, idempotentResolvent e z,
    idempotent_resolvent_mul e he z hz₀ hz₁, idempotent_mul_resolvent e he z hz₀ hz₁⟩,
    rfl⟩

/-- The entire contour stays in the resolvent set under small perturbations,
with uniform control of the resolvent. -/
theorem eventually_halfCircle_resolvent_close (e : A) (he : e * e = e)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a in 𝓝 e, ∀ z ∈ sphere (0 : ℂ) (1 / 2),
      z ∈ resolventSet ℂ a ∧ ‖resolvent a z - resolvent e z‖ < δ := by
  apply (isCompact_sphere (0 : ℂ) (1 / 2)).eventually_forall_of_forall_eventually
  intro z hz
  let f : A × ℂ → A := fun p => algebraMap ℂ A p.2 - p.1
  let g : A × ℂ → A := fun p => algebraMap ℂ A p.2 - e
  have hf : Continuous f := ((continuous_algebraMap ℂ A).comp continuous_snd).sub continuous_fst
  have hg : Continuous g := ((continuous_algebraMap ℂ A).comp continuous_snd).sub continuous_const
  have hu : IsUnit (f (e, z)) := halfCircle_resolvent e he z hz
  obtain ⟨u, hu_eq⟩ := hu
  have hi : ContinuousAt (Ring.inverse : A → A) (f (e, z)) :=
    hu_eq ▸ NormedRing.inverse_continuousAt u
  have hif : ContinuousAt (fun p => Ring.inverse (f p)) (e, z) :=
    hi.comp hf.continuousAt
  have hig : ContinuousAt (fun p => Ring.inverse (g p)) (e, z) :=
    (show ContinuousAt (Ring.inverse : A → A) (g (e, z)) from hi).comp hg.continuousAt
  have hsmall : ∀ᶠ p in 𝓝 (e, z), ‖Ring.inverse (f p) - Ring.inverse (g p)‖ < δ :=
    (hif.sub hig).norm.eventually_lt continuousAt_const (by simpa [f, g] using hδ)
  have hunit : ∀ᶠ p in 𝓝 (e, z), IsUnit (f p) :=
    hf.continuousAt (Units.isOpen.mem_nhds ⟨u, hu_eq⟩)
  filter_upwards [hunit, hsmall] with p hp hq
  exact ⟨hp, hq⟩

theorem eventually_halfCircle_idempotent_close (e : A) (he : e * e = e)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a in 𝓝 e, (∀ z ∈ sphere (0 : ℂ) (1 / 2), z ∈ resolventSet ℂ a) ∧
      ‖(1 - rieszCircle a (1 / 2)) - e‖ < ε := by
  let c : ℂ := (2 * Real.pi * Complex.I : ℂ)⁻¹
  let K : ℝ := ‖c‖ * (2 * Real.pi * (1 / 2))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let δ := ε / (K + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hKδ : K * δ < ε := by
    have heq : δ * (K + 1) = ε := div_mul_cancel₀ ε (by linarith)
    nlinarith only [heq, hδ]
  filter_upwards [eventually_halfCircle_resolvent_close e he δ hδ] with a ha
  have hres : ∀ z ∈ sphere (0 : ℂ) (1 / 2), z ∈ resolventSet ℂ a :=
    fun z hz => (ha z hz).1
  refine ⟨hres, ?_⟩
  have hIa := resolvent_circleIntegrable a (1 / 2) (by norm_num) hres
  have hIe := resolvent_circleIntegrable e (1 / 2) (by norm_num) (halfCircle_resolvent e he)
  have hnorm : ‖rieszCircle a (1 / 2) - rieszCircle e (1 / 2)‖ ≤ K * δ := by
    unfold rieszCircle
    rw [← smul_sub, norm_smul, ← circleIntegral.integral_sub hIa hIe]
    change ‖c‖ * _ ≤ K * δ
    calc
      _ ≤ ‖c‖ * (2 * Real.pi * (1 / 2) * δ) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
        exact circleIntegral.norm_integral_le_of_norm_le_const (by norm_num)
          (fun z hz => (ha z hz).2.le)
      _ = K * δ := by dsimp [K]; ring
  have hproj := rieszCircle_of_idempotent e he (1 / 2) (by norm_num) (by norm_num)
  have hdiff : (1 - rieszCircle a (1 / 2)) - e =
      -(rieszCircle a (1 / 2) - rieszCircle e (1 / 2)) := by rw [hproj]; abel
  rw [hdiff, norm_neg]
  exact hnorm.trans_lt hKδ

/-- Every idempotent can be approximated by an actual idempotent in a
finite-dimensional subalgebra from a norm-dense union. -/
theorem exists_local_idempotent_close (S : Set (Subalgebra ℂ A))
    (hfinite : ∀ B ∈ S, FiniteDimensional ℂ B)
    (hdense : Dense (⋃ B ∈ S, (B : Set A))) (e : A) (he : e * e = e)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B ∈ S, ∃ p : B, p * p = p ∧ ‖(p : A) - e‖ < ε := by
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp (eventually_halfCircle_idempotent_close e he ε hε)
  obtain ⟨a, ha, hdist⟩ := Metric.mem_closure_iff.mp (hdense e) η hη
  obtain ⟨B, hB⟩ := Set.mem_iUnion.mp ha
  obtain ⟨hBS, haB⟩ := Set.mem_iUnion.mp hB
  let x : B := ⟨a, haB⟩
  letI : FiniteDimensional ℂ B := hfinite B hBS
  letI : CompleteSpace B := FiniteDimensional.complete ℂ B
  let L : B →L[ℂ] A := B.val.toLinearMap.mkContinuous 1 (fun y => by
    change ‖(y : A)‖ ≤ 1 * ‖y‖
    rw [one_mul]
    rfl)
  obtain ⟨hres, hclose⟩ := hball (show a ∈ ball e η by simpa [mem_ball, dist_comm] using hdist)
  have hresB : ∀ z ∈ sphere (0 : ℂ) (1 / 2), z ∈ resolventSet ℂ x := by
    intro z hz
    change IsUnit (algebraMap ℂ B z - x)
    apply (isUnit_map_iff_of_finiteDimensional B.val Subtype.val_injective _).mp
    rw [map_sub, B.val.commutes]
    exact hres z hz
  let p : B := 1 - rieszCircle x (1 / 2)
  have hid := rieszCircle_isIdempotent x (1 / 2) (by norm_num) hresB
  have hp : p * p = p := by
    simp only [p, sub_mul, mul_sub, one_mul, mul_one, hid]
    abel
  have hmap : B.val (rieszCircle x (1 / 2)) = rieszCircle a (1 / 2) := by
    change L (rieszCircle x (1 / 2)) = _
    exact continuousLinearMap_rieszCircle L x a (1 / 2) (by norm_num)
      (resolvent_circleIntegrable x (1 / 2) (by norm_num) hresB)
      (fun z hz => algHom_map_resolvent B.val x z (hresB z hz))
  refine ⟨B, hBS, p, hp, ?_⟩
  change ‖B.val (1 - rieszCircle x (1 / 2)) - e‖ < ε
  rw [map_sub, map_one, hmap]
  exact hclose

/-- A bounded trace takes exactly a local idempotent value on any idempotent
in the completed algebra. This preserves membership in a prescribed ring
of weights, without taking its real or complex closure. -/
theorem exists_local_idempotent_trace_value (S : Set (Subalgebra ℂ A))
    (hfinite : ∀ B ∈ S, FiniteDimensional ℂ B)
    (hdense : Dense (⋃ B ∈ S, (B : Set A))) {τ : A →L[ℂ] ℂ}
    (hτ : IsNormalizedTrace τ) (e : A) (he : e * e = e) :
    ∃ B ∈ S, ∃ p : B, p * p = p ∧ τ (p : A) = τ e := by
  let K := ‖e + e - 1‖
  have hK : 0 ≤ K := norm_nonneg _
  have hK' : 0 < K + 1 := by linarith
  let ε := 1 / (K + 1)
  obtain ⟨B, hB, p, hp, hclose⟩ :=
    exists_local_idempotent_close S hfinite hdense e he ε (one_div_pos.mpr hK')
  have hpA : (p : A) * (p : A) = (p : A) := congrArg Subtype.val hp
  have hd : ‖e - (p : A)‖ < ε := (norm_sub_rev _ _).trans_lt hclose
  have heq : ε * (K + 1) = 1 := div_mul_cancel₀ _ hK'.ne'
  have hlt := (mul_lt_mul_of_pos_right hd hK').trans_eq heq
  have hle : ‖e - (p : A)‖ * K ≤ ‖e - (p : A)‖ * (K + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  exact ⟨B, hB, p, hp, (trace_eq_of_close_idempotents hτ he hpA (hle.trans_lt hlt)).symm⟩

end NonCalkinAlgebra
