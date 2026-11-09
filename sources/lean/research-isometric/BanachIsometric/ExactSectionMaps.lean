import BanachIsometric.SectionRadialRegularity
import BanachIsometric.RadialFamilyLift

/-!
# Actual locally Lipschitz maps onto exact moving sections

Moving isometric frames pull the sections into genuine Euclidean space. The
proved radial-family lifting theorem corrects those frames to exact section
maps. The equivalence hypothesis concerns the original subspace sections;
neither exact local maps nor a bundle chart is assumed.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal

noncomputable section

section FrameCoordinates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]

/-- A frame with its actual prescribed range, as a genuine equivalence to
that submodule. -/
def frameEquivToSubmodule (J : E →ₗᵢ[ℝ] F) (H : Submodule ℝ F)
    (hJ : LinearMap.range J.toLinearMap = H) : E ≃L[ℝ] H :=
  (LinearEquiv.ofBijective
    (J.toLinearMap.codRestrict H (fun x => by
      rw [← hJ]
      exact LinearMap.mem_range_self J.toLinearMap x))
    ⟨fun x y h => J.injective (congrArg Subtype.val h), by
      intro y
      have hy : (y : F) ∈ LinearMap.range J.toLinearMap := by rw [hJ]; exact y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩).toContinuousLinearEquiv

omit [FiniteDimensional ℝ F] in
@[simp] theorem frameEquivToSubmodule_apply_coe (J : E →ₗᵢ[ℝ] F)
    (H : Submodule ℝ F) (hJ : LinearMap.range J.toLinearMap = H) (x : E) :
    (frameEquivToSubmodule J H hJ x : F) = J x := rfl

omit [FiniteDimensional ℝ F] in
theorem frameEquivToSubmodule_image_body (p : F → ℝ) (J : E →ₗᵢ[ℝ] F)
    (H : Submodule ℝ F) (hJ : LinearMap.range J.toLinearMap = H) :
    frameEquivToSubmodule J H hJ '' pulledBackGaugeBody p J = {x : H | p x.val ≤ 1} := by
  let e := frameEquivToSubmodule J H hJ
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change p (J (e.symm y)) ≤ 1
    have he : J (e.symm y) = y.val := congrArg Subtype.val (e.apply_symm_apply y)
    rwa [he]

/-- Transport actual real-linear equivalence of subspace sections to their
Euclidean frame coordinates. -/
theorem exists_frame_body_equiv_of_section_equiv (p : F → ℝ)
    (J₀ J₁ : E →ₗᵢ[ℝ] F) (H₀ H₁ : Submodule ℝ F)
    (hJ₀ : LinearMap.range J₀.toLinearMap = H₀)
    (hJ₁ : LinearMap.range J₁.toLinearMap = H₁)
    (e : H₀ ≃ₗ[ℝ] H₁)
    (he : e '' {x : H₀ | p x.val ≤ 1} = {x : H₁ | p x.val ≤ 1}) :
    ∃ d : E ≃L[ℝ] E, d '' pulledBackGaugeBody p J₀ = pulledBackGaugeBody p J₁ := by
  let f₀ := frameEquivToSubmodule J₀ H₀ hJ₀
  let f₁ := frameEquivToSubmodule J₁ H₁ hJ₁
  let e' := e.toContinuousLinearEquiv
  refine ⟨f₀.trans (e'.trans f₁.symm), ?_⟩
  calc
    _ = f₁.symm '' (e' '' (f₀ '' pulledBackGaugeBody p J₀)) := by
      simp only [image_image]
      rfl
    _ = f₁.symm '' (e' '' {x : H₀ | p x.val ≤ 1}) := by
      rw [frameEquivToSubmodule_image_body]
    _ = f₁.symm '' {x : H₁ | p x.val ≤ 1} := by rw [show e' '' _ = _ from he]
    _ = pulledBackGaugeBody p J₁ := by
      rw [← frameEquivToSubmodule_image_body p J₁ H₁ hJ₁]
      exact ContinuousLinearEquiv.symm_image_image _ _

end FrameCoordinates

section ExactMaps

variable {P F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Exact section maps in any actual Lipschitz family of isometric frames.
Their range is the prescribed subspace, and the reference pulled-back body
is mapped onto the actual ambient section. -/
theorem exists_lipschitz_exact_section_maps_from_frames {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    {p : F → ℝ} (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (J : P → EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] F) {L : ℝ≥0}
    (hJ : LipschitzWith L (fun a => (J a).toContinuousLinearMap))
    (H : P → Submodule ℝ F)
    (hRange : ∀ a, LinearMap.range (J a).toLinearMap = H a)
    (a₀ : P)
    (hequiv : ∀ a, ∃ e : H a₀ ≃ₗ[ℝ] H a,
      e '' {x : H a₀ | p x.val ≤ 1} = {x : H a | p x.val ≤ 1}) :
    ∃ A : P → EuclideanSpace ℝ (Fin m) →L[ℝ] F, ∃ U : Set P, ∃ K : ℝ≥0,
      IsOpen U ∧ a₀ ∈ U ∧ A a₀ = (J a₀).toContinuousLinearMap ∧
        LipschitzOnWith K A U ∧
        ∀ a ∈ U, Function.Injective (A a) ∧ LinearMap.range (A a).toLinearMap = H a ∧
          A a '' pulledBackGaugeBody p (J a₀) = {y : F | p y ≤ 1} ∩ (H a : Set F) := by
  obtain ⟨r, R, D, hr, hR, hcompact, hlo, hhi, hparam⟩ :=
    exists_uniform_radial_pulledBackGauge_data hp hC J hJ
  obtain ⟨Cp, hCp⟩ := hp.exists_lipschitzWith hC
  have hreg : closure (interior (radialBody (pulledBackGaugeRadius p (J a₀)))) =
      radialBody (pulledBackGaugeRadius p (J a₀)) := by
    rw [← pulledBackGaugeBody_eq_radialBody hp]
    exact ((hp.comp_linearIsometry (J a₀)).sublevel_eq_closure_interior
      (hCp.comp (J a₀).lipschitz).continuous).symm
  have hFrameEquiv : ∀ a, ∃ d : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      d '' radialBody (pulledBackGaugeRadius p (J a₀)) =
        radialBody (pulledBackGaugeRadius p (J a)) := by
    intro a
    obtain ⟨e, he⟩ := hequiv a
    simpa only [← pulledBackGaugeBody_eq_radialBody hp] using
      exists_frame_body_equiv_of_section_equiv p (J a₀) (J a) (H a₀) (H a)
        (hRange a₀) (hRange a) e he
  obtain ⟨d, U, KD, hU, ha₀U, hd0, hdLip, hdImage⟩ :=
    exists_lipschitz_radial_family_lift μ (fun a => pulledBackGaugeRadius p (J a))
      hcompact hr hR hlo hhi hparam a₀ hreg hFrameEquiv
  let A : P → EuclideanSpace ℝ (Fin m) →L[ℝ] F := fun a =>
    (J a).toContinuousLinearMap.comp (d a).toContinuousLinearMap
  obtain ⟨W, KW, hW, ha₀W, hWU, hALip⟩ := exists_lipschitzOnWith_clm_comp_family
    (fun a => (J a).toContinuousLinearMap) (fun a => (d a).toContinuousLinearMap) a₀
    (hU.mem_nhds ha₀U) hJ.lipschitzOnWith hdLip
  refine ⟨A, W, KW, hW, ha₀W, ?_, hALip, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    change J a₀ (d a₀ x) = J a₀ x
    rw [hd0]
    rfl
  · intro a ha
    refine ⟨(J a).injective.comp (d a).injective, ?_, ?_⟩
    · ext y
      constructor
      · rintro ⟨x, rfl⟩
        rw [← hRange a]
        exact LinearMap.mem_range_self (J a).toLinearMap (d a x)
      · intro hy
        rw [← hRange a] at hy
        obtain ⟨x, rfl⟩ := hy
        refine ⟨(d a).symm x, ?_⟩
        change J a (d a ((d a).symm x)) = J a x
        rw [ContinuousLinearEquiv.apply_symm_apply]
    · have hd : d a '' pulledBackGaugeBody p (J a₀) = pulledBackGaugeBody p (J a) := by
        simpa only [← pulledBackGaugeBody_eq_radialBody hp] using hdImage a (hWU ha)
      calc
        A a '' pulledBackGaugeBody p (J a₀) = J a '' (d a '' pulledBackGaugeBody p (J a₀)) := by
          rw [image_image]
          rfl
        _ = J a '' pulledBackGaugeBody p (J a) := by rw [hd]
        _ = {y : F | p y ≤ 1} ∩ (H a : Set F) :=
          image_pulledBackGaugeBody_eq_section p (J a) (H a) (hRange a)

/-- The complete local exact-section construction from the actual prescribed
subspaces and their Lipschitz orthogonal projections. Frames and exact body
maps are both constructed, rather than assumed. -/
theorem exists_lipschitz_exact_subspace_section_maps {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    {p : F → ℝ} (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (H : P → Submodule ℝ F) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun a => (H a).starProjection))
    (hrank : ∀ a, Module.finrank ℝ (H a) = Module.finrank ℝ (EuclideanSpace ℝ (Fin m)))
    (a₀ : P)
    (hequiv : ∀ a, ∃ e : H a₀ ≃ₗ[ℝ] H a,
      e '' {x : H a₀ | p x.val ≤ 1} = {x : H a | p x.val ≤ 1}) :
    ∃ R : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] F,
      LinearMap.range R.toLinearMap = H a₀ ∧
      ∃ A : P → EuclideanSpace ℝ (Fin m) →L[ℝ] F, ∃ U : Set P, ∃ K : ℝ≥0,
        IsOpen U ∧ a₀ ∈ U ∧ A a₀ = R.toContinuousLinearMap ∧
          LipschitzOnWith K A U ∧
          ∀ a ∈ U, Function.Injective (A a) ∧ LinearMap.range (A a).toLinearMap = H a ∧
            A a '' pulledBackGaugeBody p R = {y : F | p y ≤ 1} ∩ (H a : Set F) := by
  classical
  obtain ⟨J₀, V, KJ, hV, ha₀V, hJ₀Lip, hJ₀⟩ :=
    exists_lipschitz_isometric_subspace_frames H hLip hrank a₀
  let J : V → EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] F := fun a =>
    { (J₀ a.val).toLinearMap with
      norm_map' := (J₀ a.val).norm_map_iff_adjoint_comp_self.mpr (hJ₀ a.val a.property).1 }
  have hJLip : LipschitzWith KJ (fun a => (J a).toContinuousLinearMap) := hJ₀Lip.to_restrict
  have hJRange : ∀ a : V, LinearMap.range (J a).toLinearMap = H a.val :=
    fun a => (hJ₀ a.val a.property).2
  let aV : V := ⟨a₀, ha₀V⟩
  obtain ⟨B, W, KB, hW, haVW, hB0, hBLip, hB⟩ :=
    exists_lipschitz_exact_section_maps_from_frames μ hp hC J hJLip
      (fun a : V => H a.val) hJRange aV (fun a => hequiv a.val)
  let A : P → EuclideanSpace ℝ (Fin m) →L[ℝ] F :=
    fun a => if ha : a ∈ V then B ⟨a, ha⟩ else 0
  let U : Set P := Subtype.val '' W
  refine ⟨J aV, hJRange aV, A, U, KB, hV.isOpenMap_subtype_val W hW,
    ⟨aV, haVW, rfl⟩, ?_, ?_, ?_⟩
  · simpa only [A, dif_pos ha₀V] using hB0
  · apply LipschitzOnWith.of_dist_le_mul
    rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
    simpa only [A, dif_pos a'.property, dif_pos b'.property] using
      hBLip.dist_le_mul a' ha' b' hb'
  · rintro a ⟨a', ha', rfl⟩
    simpa only [A, dif_pos a'.property] using hB a' ha'

end ExactMaps

end
end BanachIsometric
