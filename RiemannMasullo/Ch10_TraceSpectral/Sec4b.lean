module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
public import RiemannMasullo.AppC_LCTVS.Sec3b
import RiemannMasullo.Ch10_TraceSpectral.Sec1

import all RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.AppC_LCTVS.Sec2a_part2
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Completion

/-!
# Spectral kernels

Masullo, §10.4.3, pp. 464–474. The first factor of a tensor is in the
reciprocal-weight Sobolev space. A kernel written as a function of `(x,y)`
has output coordinate `x` and input coordinate `y`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing TensorProduct Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 900000

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (logIdeleClassNorm F)
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs))
local notation "w(" α ", " s ")" => (fun g : C𝔽 ↦ intervalSobolevDensity (-α) α s (logNorm g))
local notation "ν(" α ", " s ")" => ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (w(α, s) g))
local notation "ν'(" α ", " s ")" => ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (w(α, s) g)⁻¹)
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s
local notation "W'(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s true
local notation "Π(" E ", " G ")" => Completion (ProjectiveTensor E G)
local notation "Θ(" a ", " hα ", " hs ")" => globalThetaSobolev F a (hStrip(hα)) hs
local notation "H(" a ", " hα ", " hs ")" => spectralSobolevQuotient F a (hStrip(hα)) hs
local notation "Q(" a ", " hα ", " hs ")" => (Θ(a, hα, hs)).mkQL
local notation "S(" a ", " hα ", " hs ")" =>
  (fun u : H(a, hα, hs) ↦
    ((Θ(a, hα, hs)).quotientEquivOrthogonal u).val)
local notation "A(" hα ", " hs ", " φ ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs φ
local notation "Aq(" a ", " hα ", " hs ", " φ ")" =>
  spectralConvolution (F := F) a (hStrip(hα)) hs φ
local notation "Pspec(" a ", " hα ", " hs ")" => spectralProjection (F := F) a hα hs
local notation "Pgeom(" a ", " hα ", " hs ")" => geometricProjection (F := F) a hα hs

-- TODO(paper-gap): The displayed regularization (10.4.3.1) misses the translated
-- poles for nonzero norm twists. Use the regularization of §7.1.
-- TODO(paper-gap): In (10.4.3.2) injectivity on the quotient requires a closure
-- intersection identity in the weaker Sobolev norm. First twist the whole
-- middle row by multiplication by |.|^a, or take its quotient by the
-- already twisted theta subspace. Bare completion need not descend from
-- the quotient by the untwisted theta subspace.
-- TODO(paper-gap): The biorthogonal Schwartz representatives in (10.4.3.5)
-- can be changed by adding any polar-free theta vector. The construction
-- below uses the quotient basis and its orthogonal representatives.

section ProjectiveKernels

variable {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

local notation "T" =>
  (modulatedIntervalSobolev_dual m𝔽
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    μ𝔽 (-α) α s (hStrip(hα)) hs).exists.choose

/-- Paper: Theorem 10.4.3.1(3), p. 467, and Theorem 10.4.3.5(3), p. 473.
The canonical projective kernel map applies the inverse Sobolev duality
to the first factor and sends the resulting tensor to an operator. -/
def sobolevProjectiveKernelOperator :
    Π(W'(α, s), W(α, s)) →L[ℂ] (W(α, s) →L[ℂ] W(α, s)) :=
  let f := (T).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let g := ContinuousLinearMap.id ℂ (W(α, s))
  completedProjectiveTensorToOperators.comp
    (⟨projectiveTensorMap f.toLinearMap g.toLinearMap,
      projectiveTensorMap_continuous f g⟩ :
        ProjectiveTensor W'(α, s) W(α, s) →L[ℂ]
          ProjectiveTensor (StrongDual ℂ W(α, s)) W(α, s)).completion

local notation "ξ" => sobolevProjectiveKernelOperator (F := F) hα hs

/-- The kernel composite of `sobolevProjectiveKernelOperator`, for general normed spaces,
evaluated on an elementary tensor. -/
private theorem sobolevProjectiveKernelOperator_tmul_aux {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (e : StrongDual ℂ E ≃ₗᵢ[ℂ] X) (u : X) (v x : E) :
    (completedProjectiveTensorToOperators.comp
      (⟨projectiveTensorMap e.symm.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.id ℂ E).toLinearMap,
        projectiveTensorMap_continuous e.symm.toContinuousLinearEquiv.toContinuousLinearMap
          (ContinuousLinearMap.id ℂ E)⟩ :
          ProjectiveTensor X E →L[ℂ] ProjectiveTensor (StrongDual ℂ E) E).completion)
      ((show ProjectiveTensor X E from u ⊗ₜ[ℂ] v) : Completion (ProjectiveTensor X E)) x =
      e.symm u x • v := by
  exact congrArg (fun A : E →L[ℂ] E ↦ A x)
    ((congrArg completedProjectiveTensorToOperators
      (ContinuousLinearMap.completion_apply_coe _
        (show ProjectiveTensor X E from u ⊗ₜ[ℂ] v))).trans
      (completedProjectiveTensorToOperators_coe _))

/-- Paper: Theorem 10.4.3.1(3), p. 467, and Theorem 10.4.3.5(3), p. 473.
On an elementary tensor the operator pairs the input with the reciprocal-weight
factor and scales the positive-weight factor. -/
theorem sobolevProjectiveKernelOperator_tmul
    (u : W'(α, s)) (v f : W(α, s)) :
    ξ (((show ProjectiveTensor W'(α, s) W(α, s) from u ⊗ₜ[ℂ] v) : Π(W'(α, s), W(α, s)))) f =
      spectralSobolevPairing (F := F) f u • v := by
  have hspec := ((modulatedIntervalSobolev_dual m𝔽
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    μ𝔽 (-α) α s (hStrip(hα)) hs).exists.choose_spec ((T).symm u) f).2
  rw [LinearIsometryEquiv.apply_symm_apply] at hspec
  have h := sobolevProjectiveKernelOperator_tmul_aux (T) u v f
  refine h.trans ?_
  rw [hspec]
  rfl

/-- Paper: Theorem 10.4.3.1(3), p. 467, and Theorem 10.4.3.5(3), p. 473.
The canonical map from completed projective kernels to operators is injective. -/
theorem sobolevProjectiveKernelOperator_injective : Injective ξ := by
  have (V : Type _) [NormedAddCommGroup V] [NormedSpace ℂ V] :
      PolynormableSpace ℂ (StrongDual ℂ V) :=
    (norm_withSeminorms ℂ (StrongDual ℂ V)).toPolynormableSpace
  have (V : Type _) [UniformSpace V] : T2Space (Completion V) := inferInstance
  have inj {X E : Type _} [NormedAddCommGroup X] [NormedSpace ℂ X]
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (e : StrongDual ℂ E ≃ₗᵢ[ℂ] X) :
      let f := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
      let i : ProjectiveTensor X E →L[ℂ] ProjectiveTensor (StrongDual ℂ E) E :=
        ⟨projectiveTensorMap f.toLinearMap (LinearMap.id : E →ₗ[ℂ] E),
          projectiveTensorMap_continuous f (ContinuousLinearMap.id ℂ E)⟩
      Injective ((completedProjectiveTensorToOperators (E := E) (F := E)).comp i.completion) := by
    intro f i
    let g := e.toContinuousLinearEquiv.toContinuousLinearMap
    let j : ProjectiveTensor (StrongDual ℂ E) E →L[ℂ] ProjectiveTensor X E :=
      ⟨projectiveTensorMap g.toLinearMap (LinearMap.id : E →ₗ[ℂ] E),
        projectiveTensorMap_continuous g (ContinuousLinearMap.id ℂ E)⟩
    have hi (z : ProjectiveTensor X E) : j (i z) = z := by
      induction z using TensorProduct.inductionOn with
      | tmul v x => exact congrArg (fun w : X ↦ w ⊗ₜ[ℂ] x) (e.apply_symm_apply v)
      | add x y hx hy =>
        exact (congrArg j (i.map_add x y)).trans
          ((j.map_add (i x) (i y)).trans (congrArg₂ (fun a b : ProjectiveTensor X E ↦ a + b) hx hy))
    have hji (z : Completion (ProjectiveTensor X E)) : j.completion (i.completion z) = z := by
      refine Completion.induction_on z (isClosed_eq (j.completion.continuous.comp i.completion.continuous)
        continuous_id) fun w ↦ ?_
      rw [i.completion_apply_coe, j.completion_apply_coe, hi]
    obtain ⟨t, ht, -⟩ := (exists_projectiveTensorCompletion_traceClassIsometry (E := E) (F := E)).2
    intro v w he
    have hh := t.injective (Subtype.ext ((ht (i.completion v)).trans (he.trans (ht (i.completion w)).symm)))
    exact (hji v).symm.trans ((congrArg j.completion hh).trans (hji w))
  exact inj (T)

end ProjectiveKernels

private theorem sobolevProjectiveKernel_transported_iff {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (e : StrongDual ℂ E ≃ₗᵢ[ℂ] X) (A : E →L[ℂ] E) :
    let f := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
    let i : ProjectiveTensor X E →L[ℂ] ProjectiveTensor (StrongDual ℂ E) E :=
      ⟨projectiveTensorMap f.toLinearMap (LinearMap.id : E →ₗ[ℂ] E),
        projectiveTensorMap_continuous f (ContinuousLinearMap.id ℂ E)⟩
    (∃ K, completedProjectiveTensorToOperators (i.completion K) = A) ↔ IsNuclearOperator A := by
  intro f i
  rw [isNuclearOperator_iff_isBanachNuclear, isBanachNuclear_iff_mem_range]
  constructor
  · rintro ⟨K, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨z, hz⟩
    have onto : Surjective i.completion := completedProjectiveTensorMap_surjective f
      (ContinuousLinearMap.id ℂ E) e.symm.toHomeomorph.isQuotientMap Topology.IsQuotientMap.id
    obtain ⟨K, hK⟩ := onto z
    exact ⟨K, (congrArg (completedProjectiveTensorToOperators (E := E) (F := E)) hK).trans hz⟩

/-- The weighted tensor required in (10.4.3.45), p. 473, exists uniquely exactly when
the specified ambient operator is nuclear. -/
theorem existsUnique_sobolevProjectiveKernel_iff_nuclear {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (A : W(α, s) →L[ℂ] W(α, s)) :
    (∃! K, sobolevProjectiveKernelOperator (F := F) ha hs K = A) ↔ IsNuclearOperator A := by
  have h := sobolevProjectiveKernel_transported_iff
    ((modulatedIntervalSobolev_dual m𝔽 ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      μ𝔽 _ _ _ (hStrip(ha)) hs).exists.choose) A
  change (∃ K, sobolevProjectiveKernelOperator (F := F) ha hs K = A) ↔ IsNuclearOperator A at h
  refine ⟨fun hu ↦ h.mp hu.exists, fun hn ↦ ?_⟩
  obtain ⟨K, hK⟩ := h.mpr hn
  exact ⟨K, hK, fun L hL ↦ sobolevProjectiveKernelOperator_injective ha hs (hL.trans hK.symm)⟩

/-- Every admissible finite cutoff in Definition 10.4.1.5, p. 458, has a unique
reciprocal-weight projective kernel for convolution after the spectral projection. -/
theorem spectralRestriction_existsUnique_projectiveKernel (a : ℝ) {α s : ℝ}
    (ha : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽) {R ε : ℝ} {ρ : C𝔽 → ℝ}
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) (hband : 0 < R⁻¹+ε ∧ R⁻¹+ε < R-ε) :
    ∃! K, sobolevProjectiveKernelOperator (F := F) ha hs K = spectralRestriction a ha hs hρ φ :=
  (existsUnique_sobolevProjectiveKernel_iff_nuclear ha hs _).mpr
    (spectralRestriction_nuclear a ha hs hρ hband φ)

private theorem cutoffKernel_tensor_finite_range {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (z : StrongDual ℂ H ⊗[ℂ] H) :
    FiniteDimensional ℂ (tensorToFiniteRank z).toLinearMap.range := by
  induction z using TensorProduct.inductionOn with
  | tmul φ y =>
    have := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton y)
    apply Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ y)
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨φ x, (tensorToFiniteRank_tmul φ y x).symm⟩
  | add z w hz hw =>
    rw [map_add, ContinuousLinearMap.toLinearMap_add]
    exact Submodule.finiteDimensional_of_le (LinearMap.range_add_le _ _)

private theorem cutoffKernel_traceNorm_null
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Q : ℝ → H →L[ℂ] H) (hQ : ∀ x, Tendsto (fun R ↦ Q R x) atTop (𝓝 0))
    (hbound : ∀ R, ‖Q R‖ ≤ 2) (T : nuclearEndomorphisms H) :
    Tendsto (fun R ↦ traceNorm ⟨Q R * T.val, mul_mem_nuclearEndomorphisms_left (Q R) T⟩) atTop (𝓝 0) := by
  let product (R : ℝ) (A : nuclearEndomorphisms H) : nuclearEndomorphisms H :=
    ⟨Q R * A.val, mul_mem_nuclearEndomorphisms_left (Q R) A⟩
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hcore := (traceNorm_normedSpaceCore (H := H)).toCore
  have hnonneg (A : nuclearEndomorphisms H) : 0 ≤ traceNorm A := hcore.norm_nonneg A
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨z, hz⟩ := exists_tensorToFiniteRank_traceNorm_sub_lt T (by positivity : 0 < ε / 4)
  let F : nuclearEndomorphisms H :=
    ⟨tensorToFiniteRank z, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩
  obtain ⟨_, hF⟩ := tendsto_traceNorm_mul_finiteRank Q hQ F.val (cutoffKernel_tensor_finite_range z)
  have hF' : Tendsto (fun R ↦ traceNorm (product R F)) atTop (𝓝 0) := hF
  filter_upwards [Metric.tendsto_nhds.mp hF' (ε / 2) (half_pos hε)] with R hR
  have hsplit : product R T = product R (T - F) + product R F := by
    apply Subtype.ext
    simp [product, mul_sub]
  have hle : traceNorm (product R (T - F)) ≤ 2 * traceNorm (T - F) :=
    (traceNorm_mul_left_le (Q R) (T - F)).trans
      (mul_le_mul_of_nonneg_right (hbound R) (hnonneg (T - F)))
  have htriangle : traceNorm (product R T) ≤
      traceNorm (product R (T - F)) + traceNorm (product R F) := by
    rw [hsplit]
    exact hcore.norm_triangle _ _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg (product R F))] at hR
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg (product R T))]
  change traceNorm (T - F) < ε / 4 at hz
  linarith

private theorem cutoffKernel_contraction_limit {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ℝ → H →L[ℂ] H) (hP : ∀ R, ‖P R‖ ≤ 1)
    (hlim : ∀ x, Tendsto (fun R ↦ P R x) atTop (𝓝 x)) (T : nuclearEndomorphisms H) :
    let D (R : ℝ) : nuclearEndomorphisms H := ⟨P R * T.val, mul_mem_nuclearEndomorphisms_left (P R) T⟩
    Tendsto (fun R ↦ traceNorm (D R - T)) atTop (𝓝 0) ∧
      Tendsto (fun R ↦ hilbertTrace (D R)) atTop (𝓝 (hilbertTrace T)) := by
  intro D
  have hnorm : Tendsto (fun R ↦ traceNorm (D R - T)) atTop (𝓝 0) := by
    let Q (R : ℝ) := P R - 1
    have hq (x : H) : Tendsto (fun R ↦ Q R x) atTop (𝓝 0) := by
      simpa [Q] using (hlim x).sub (tendsto_const_nhds (x := x))
    have hb (R : ℝ) : ‖Q R‖ ≤ 2 := (norm_sub_le _ _).trans (by
      linarith [hP R, show ‖(1 : H →L[ℂ] H)‖ ≤ 1 from ContinuousLinearMap.norm_id_le])
    have hdiff (R : ℝ) : D R - T = ⟨Q R * T.val, mul_mem_nuclearEndomorphisms_left (Q R) T⟩ := by
      apply Subtype.ext
      change P R * T.val - T.val = (P R - 1) * T.val
      rw [sub_mul, one_mul]
    simp_rw [hdiff]
    exact cutoffKernel_traceNorm_null _ Q hq hb T
  refine ⟨hnorm, ?_⟩
  obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
  have he (R : ℝ) : hilbertTrace (D R) - hilbertTrace T = hilbertTrace (D R - T) := by
    rw [← hL, ← hL, ← hL, map_sub]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun R ↦ ‖hilbertTrace (D R) - hilbertTrace T‖) atTop (𝓝 0)
  simp_rw [he]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun R ↦ norm_hilbertTrace_le (D R - T)) hnorm

/-- If the untruncated kernel in (12.5.1.4), p. 520, exists, every expanding
admissible family of the actual finite restrictions converges in trace norm.
Their Hilbert traces converge to the trace of convolution after projection. -/
theorem spectralRestriction_traceNorm_tendsto_of_projectiveKernel (a : ℝ) {α s : ℝ}
    (ha : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (hK : ∃ K, sobolevProjectiveKernelOperator (F := F) ha hs K = ((A(ha, hs, φ)).comp (Pspec(a, ha, hs))))
    (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ) (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹+ε R ∧ R⁻¹+ε R < R-ε R) :
    ∃ (T : nuclearEndomorphisms (W(α, s))) (D : ℝ → nuclearEndomorphisms (W(α, s))),
      T.val = ((A(ha, hs, φ)).comp (Pspec(a, ha, hs))) ∧
      (∀ R (hc : IsModulatedCutoff m𝔽 R (ε R) (ρ R)), (D R).val = spectralRestriction a ha hs hc φ) ∧
      Tendsto (fun R ↦ traceNorm (D R - T)) atTop (𝓝 0) ∧
      Tendsto (fun R ↦ hilbertTrace (D R)) atTop (𝓝 (hilbertTrace T)) := by
  obtain ⟨K, hk⟩ := hK
  have hn := (existsUnique_sobolevProjectiveKernel_iff_nuclear ha hs _).mp
    ⟨K, hk, fun L hL ↦ sobolevProjectiveKernelOperator_injective ha hs (hL.trans hk.symm)⟩
  let T : nuclearEndomorphisms (W(α, s)) := ⟨_, hn⟩
  have hfamily : ∃ P : ℝ → W(α,s) →L[ℂ] W(α,s),
      (∀ R, ‖P R‖ ≤ 1) ∧ (∀ u, Tendsto (fun R ↦ P R u) atTop (𝓝 u)) ∧
      ∀ R (hc : IsModulatedCutoff m𝔽 R (ε R) (ρ R)), P R = modulatedCutoffOperator m𝔽
        ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logNorm g))) hc := by
    with_unfolding_all
      exact exists_stronglyConvergent_modulatedCutoffOperators C𝔽 m𝔽
        ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logNorm g))) ε ρ hε hρ
  obtain ⟨P, hP, hlim, hcut⟩ := hfamily
  let D (R : ℝ) : nuclearEndomorphisms (W(α, s)) := ⟨P R * T.val, mul_mem_nuclearEndomorphisms_left (P R) T⟩
  have h := cutoffKernel_contraction_limit P hP hlim T
  refine ⟨T, D, rfl, fun R hc ↦ ?_, h.1, h.2⟩
  change P R * T.val = _
  rw [hcut R hc]
  rfl

section FiniteTensors

variable {Z J E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Paper: (10.4.3.13)–(10.4.3.14), p. 467, and (10.4.3.42)–(10.4.3.43),
p. 472. Sum the tensor terms for all jets of the zeros in the finite rectangle. -/
def spectralKernelRectangle (e : Z ↪ ℕ × ℕ) (N : Z → ℕ)
    (jet : (z : Z) → Fin (N z) → J) (u : J → E) (v : J → G) (ij : ℕ × ℕ) :
    Π(E, G) :=
  ↑(∑ z ∈ ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn,
      ∑ m : Fin (N z), u (jet z m) ⊗ₜ[ℂ] v (jet z m) : ProjectiveTensor E G)

/-- Paper: (10.4.3.13)–(10.4.3.14), p. 467. A rectangle with just one
zero and one jet gives the elementary kernel tensor. -/
theorem spectralKernelRectangle_single (e : Unit ↪ ℕ × ℕ) (ij : ℕ × ℕ)
    (_h₁ : (e ()).1 ≤ ij.1) (_h₂ : (e ()).2 ≤ ij.2)
    (j : J) (u : J → E) (v : J → G) :
    spectralKernelRectangle e (fun _ ↦ 1) (fun _ _ ↦ j) u v ij =
      ((show ProjectiveTensor E G from u j ⊗ₜ[ℂ] v j) : Π(E, G)) := by
  have hpre : ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn =
      Finset.univ := by
    ext z
    obtain rfl : z = () := Subsingleton.elim _ _
    simp [Finset.mem_product, _h₁, _h₂]
  unfold spectralKernelRectangle
  rw [hpre]
  simp
  exact congrArg _ (Finset.sum_singleton _ _)

end FiniteTensors

section LineTensors

variable (a : ℝ) {s : ℝ} (hs : 1 < s)

local notation "Q₀" => Q(a, (le_refl (0 : ℝ)), hs₀(hs))
local notation "S₀" => (fun u : H(a, (le_refl (0 : ℝ)), hs₀(hs)) ↦
  ((Θ(a, (le_refl (0 : ℝ)), hs₀(hs))).quotientEquivOrthogonal u : W(0, s)))

/-- Paper: Theorem 10.4.3.1(1), p. 467. The isometric image of a quotient
basis vector is the spectral projection of any representative.
Deviation: The identity is stated for any quotient vector. -/
theorem spectralLineKernel_orthogonalLift (_ha : 0 < a)
    (x : H(a, (le_refl (0 : ℝ)), hs₀(hs))) (v : W(0, s)) (_hv : Q₀ v = x) :
    S₀ x = Pspec(a, (le_refl (0 : ℝ)), hs₀(hs)) v := by
  subst x
  exact (spectralQuotient_orthogonalRepresentative (F := F) a (le_refl (0 : ℝ)) hs₀(hs) _ha v).1

local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ // 0 < order(χ z.1, shift(a, z.2))}
local notation "N(" χ ", " z ")" => spectralBoundaryMultiplicity s (mult(χ (z).val.1,
  shift(a, (z).val.2)))
local notation "jet" => (fun z m ↦ ⟨(z.val.1, z.val.2, m.val), m.isLt⟩)
local notation "A₀(" φ ")" => A((le_refl (0 : ℝ)), hs₀(hs), φ)
local notation "Aq₀(" φ ")" => Aq(a, (le_refl (0 : ℝ)), hs₀(hs), φ)
local notation "D₀" => spectralSobolevDualEmbedding F a
  (hStrip(le_refl (0 : ℝ))) hs₀(hs)

local notation "Bases₀(" χ ", " x ", " f ")" => (IsSpectralMarkushevichBasis x f ∧
  ∀ j, D₀ (f j) =
    cast (congrArg (fun l : ℝ ↦ CompactIntervalSobolev μ𝔽 logNorm l 0 s true) neg_zero.symm)
      ((spectralLineJet_memLp χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2)))
local notation "Order₀(" χ ", " e ")" => (∀ z z' : Z(χ), z.val.1 = z'.val.1 → (e z).2 ≤ (e z').2 →
  |z.val.2| ≤ |z'.val.2|)

-- TODO(paper-gap): The lexicographic initial segments need not be finite.
-- The double limit uses rectangles with the product order on their end points.
-- The convergence argument invokes the uniform estimate flagged in ERRATA R5.

open scoped ComplexOrder in
/-- The projective gauge of the unit pure tensors controls every zero-neighborhood. -/
private theorem spectralLineQuotientKernel_tendsto_gauge {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (U : Set (ProjectiveTensor X Y)) (hU : U ∈ 𝓝 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ProjectiveTensor X Y,
      gauge (convexHull ℝ (image2 (TensorProduct.tmul ℂ)
        (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))) z < ε → z ∈ U := by
  let B (r s : ℝ) : Set (ProjectiveTensor X Y) :=
    image2 (TensorProduct.tmul ℂ) (Metric.closedBall 0 r) (Metric.closedBall 0 s)
  let : PolynormableSpace ℂ X := (norm_withSeminorms ℂ X).toPolynormableSpace
  let : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  let : IsScalarTower ℝ ℂ (ProjectiveTensor X Y) := IsScalarTower.restrictScalars ℝ ℂ _
  let : ContinuousSMul ℂ (ProjectiveTensor X Y) := PolynormableSpace.continuousSMul ℂ _
  let : ContinuousSMul ℝ (ProjectiveTensor X Y) := IsScalarTower.continuousSMul ℂ
  have hb := projectiveTensor_zero_basis (E := X) (F := Y) (Metric.nhds_basis_closedBall (x := (0 : X)))
    (Metric.nhds_basis_closedBall (x := (0 : Y)))
  have hbal : Balanced ℂ (B 1 1) := by
    intro c hc
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    refine ⟨c • x, ?_, y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg x)).trans
      (by simpa using hx)
  have hrect : absConvexHull ℂ (B 1 1) ⊆ convexHull ℝ (B 1 1) := by
    rw [absConvexHull_eq_convexHull_balancedHull, show balancedHull ℂ (B 1 1) = B 1 1 from
      le_antisymm (hbal.balancedHull_subset_of_subset Subset.rfl) (subset_balancedHull ℂ)]
    exact convexHull_min (subset_convexHull ..) (convex_RCLike_iff_convex_real.mpr (convex_convexHull ..))
  have hunit : convexHull ℝ (B 1 1) ∈ 𝓝 (0 : ProjectiveTensor X Y) :=
    Filter.mem_of_superset (hb.mem_of_mem (i := (1, 1)) ⟨one_pos, one_pos⟩) hrect
  obtain ⟨⟨r, s⟩, ⟨hr, hs⟩, hsub⟩ := hb.mem_iff.mp hU
  refine ⟨r * s, mul_pos hr hs, fun z hz ↦ ?_⟩
  obtain ⟨t, ht, htrs, hz⟩ := exists_lt_of_gauge_lt (absorbent_nhds_zero hunit) hz
  apply hsub
  rw [← convexHull_smul] at hz
  refine convexHull_min ?_ (convex_absConvexHull.lift ℝ) hz
  rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  apply subset_absConvexHull
  refine ⟨(t / s : ℝ) • x, ?_, s • y, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (div_nonneg ht.le hs.le)]
    exact (mul_le_of_le_one_right (div_nonneg ht.le hs.le) (by simpa using hx)).trans
      ((div_lt_iff₀ hs).mpr htrs).le
  · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hs.le]
    exact mul_le_of_le_one_right hs.le (by simpa using hy)
  · rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, div_mul_cancel₀ _ hs.ne']
    rfl

/-- Trace-norm Cauchy rectangles of finite-rank operators give Cauchy tensor rectangles. -/
private theorem spectralLineQuotientKernel_tendsto_of_traceCauchy {H Z J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (f : J → StrongDual ℂ H) (e : Z ↪ ℕ × ℕ)
    (N : Z → ℕ) (i : (z : Z) → Fin (N z) → J)
    (hc : SpectralRectanglesTraceCauchy (fun ij ↦ spectralConvolutionFiniteSum A x f
      (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn) N i)) :
    ∃ K, Tendsto (spectralKernelRectangle e N i (fun j ↦ (f j).comp A) x) atTop (𝓝 K) := by
  classical
  let P := ProjectiveTensor (StrongDual ℂ H) H
  let box (ij : ℕ × ℕ) := ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
  let w (ij : ℕ × ℕ) : P := ∑ z ∈ box ij, ∑ m : Fin (N z), (f (i z m)).comp A ⊗ₜ[ℂ] x (i z m)
  have hop (ij) : tensorToFiniteRank (w ij) = spectralConvolutionFiniteSum A x f (box ij) N i := by
    change tensorToFiniteRank (∑ z ∈ box ij, ∑ m : Fin (N z), (f (i z m)).comp A ⊗ₜ[ℂ] x (i z m)) = _
    simp only [map_sum, spectralConvolutionFiniteSum]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro m _
    exact ContinuousLinearMap.ext fun y ↦ tensorToFiniteRank_tmul _ _ y
  obtain ⟨huc, equiv, hval, hnorm⟩ := exists_projectiveTensorCompletion_traceClassIsometry (E := H) (F := H)
  have hcauchy : CauchySeq w := by
    apply (cauchySeq_iff_sub_mem w).mpr
    intro U hU
    obtain ⟨ε, hε, hball⟩ := spectralLineQuotientKernel_tendsto_gauge U hU
    obtain ⟨b, hb⟩ := hc ε hε
    refine ⟨b, fun j hj k hk ↦ hball _ ?_⟩
    obtain ⟨T, hT, hsmall⟩ := hb j k hj hk
    have heq : (equiv ((w j - w k : P) : Completion P)).val = T.val := by
      rw [hval, completedProjectiveTensorToOperators_coe]
      exact (map_sub tensorToFiniteRank (w j : StrongDual ℂ H ⊗[ℂ] H) (w k)).trans
        ((congrArg₂ (· - ·) (hop j) (hop k)).trans hT.symm)
    have hnorm' := (hnorm ((w j - w k : P) : Completion P)).trans (Completion.extension_coe huc _)
    exact hnorm'.symm.trans_lt ((congrArg schattenNorm (Subtype.ext heq)).trans_lt
      ((schattenNorm_one_eq_traceNorm T).trans_lt hsmall))
  exact cauchySeq_tendsto_of_complete
    (UniformContinuous.comp_cauchySeq (Completion.uniformContinuous_coe (α := P)) hcauchy)

/-- Transport the line trace estimate from the endpoint zero to an equal endpoint. -/
private theorem spectralLineQuotientKernel_tendsto_traceCauchy {F : Type*} [Field F] [NumberField F]
    (a : ℝ) {s : ℝ} (hs : 1 < s)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (eχ : PontryaginDual (ideleClassNorm F).ker ↪ ℕ)
    (e : {z : PontryaginDual (ideleClassNorm F).ker × ℝ // 0 < order(χ z.1, shift(a, z.2))} ↪ ℕ × ℕ)
    (hχ : IsSpectralBasepointChoice χ) (he : ∀ z, (e z).1 = eχ z.val.1)
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) (l : ℝ) (hl : 0 = l) (hI : l ≤ 0)
    (x' : SpectralLineJetIndex χ a s → spectralSobolevQuotient F a hI hs₀(hs))
    (f' : SpectralLineJetIndex χ a s → StrongDual ℂ (spectralSobolevQuotient F a hI hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x' f')
    (hj : ∀ j, spectralSobolevDualEmbedding F a hI hs₀(hs) (f' j) =
      cast (congrArg (fun r : ℝ ↦ CompactIntervalSobolev (ideleClassTamagawaMeasure F)
        (fun g ↦ Real.log ((ideleClassNorm F g).val : ℝ)) r 0 s true) hl)
        ((spectralLineJet_memLp χ hs j).toLp
          (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))) :
    SpectralRectanglesTraceCauchy (fun ij ↦ spectralConvolutionFiniteSum
      (spectralConvolution (F := F) a hI hs₀(hs) φ) x' f'
      (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
      (fun z ↦ spectralBoundaryMultiplicity s (mult(χ z.val.1, shift(a, z.val.2)))) jet) := by
  subst l
  exact spectralLineConvolution_traceCauchy (F := F) a χ hχ hs φ eχ e he x' f' hb hj

/-- Paper: Theorem 10.4.3.1(2), p. 467, equation (10.4.3.13). The quotient
kernel tensors converge along the directed net of finite rectangles.
Deviation: The injections allow empty and finite zero sets. Use the strict
boundary multiplicity from §10.2 and the product order on rectangle endpoints. -/
theorem spectralLineQuotientKernel_tendsto (_ha : 0 < a)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ)
    (x : SpectralLineJetIndex χ a s → H(a, (le_refl (0 : ℝ)), hs₀(hs)))
    (f : SpectralLineJetIndex χ a s → StrongDual ℂ H(a, (le_refl (0 : ℝ)), hs₀(hs)))
    (_hχ : IsSpectralBasepointChoice χ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (_horder : Order₀(χ, e)) (_hb : Bases₀(χ, x, f)) (φ : BruhatCompactSupport C𝔽) :
    ∃ K, Tendsto (spectralKernelRectangle e (fun z ↦ N(χ, z)) jet
      (fun j ↦ (f j).comp (Aq₀(φ))) x) atTop (𝓝 K) := by
  exact spectralLineQuotientKernel_tendsto_of_traceCauchy (Aq₀(φ)) x f e _ _
    (spectralLineQuotientKernel_tendsto_traceCauchy a hs χ eχ e _hχ _he φ _ neg_zero.symm _ x f _hb.1 _hb.2)

/-- Paper: Theorem 10.4.3.1(2), p. 467, equation (10.4.3.14). The ambient
kernel tensors converge in the completed projective tensor product.
Deviation: Use the same rectangles and strict boundary multiplicity. -/
theorem spectralLineAmbientKernel_tendsto (_ha : 0 < a)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ)
    (x : SpectralLineJetIndex χ a s → H(a, (le_refl (0 : ℝ)), hs₀(hs)))
    (f : SpectralLineJetIndex χ a s → StrongDual ℂ H(a, (le_refl (0 : ℝ)), hs₀(hs)))
    (_hχ : IsSpectralBasepointChoice χ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (_horder : Order₀(χ, e)) (_hb : Bases₀(χ, x, f)) (φ : BruhatCompactSupport C𝔽) :
    ∃ K, Tendsto (spectralKernelRectangle e (fun z ↦ N(χ, z)) jet
      (fun j ↦ D₀ ((f j).comp (Aq₀(φ)))) (fun j ↦ S₀ (x j))) atTop (𝓝 K) := by
  have lift {Z J E G X Y : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]
      [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup X] [NormedSpace ℂ X]
      [NormedAddCommGroup Y] [NormedSpace ℂ Y]
      (d : E →L[ℂ] X) (j : G →L[ℂ] Y) (e : Z ↪ ℕ × ℕ) (N : Z → ℕ)
      (i : (z : Z) → Fin (N z) → J) (u : J → E) (v : J → G)
      (h : ∃ K, Tendsto (spectralKernelRectangle e N i u v) atTop (𝓝 K)) :
      ∃ K, Tendsto (spectralKernelRectangle e N i (fun z ↦ d (u z)) (fun z ↦ j (v z))) atTop (𝓝 K) := by
    let L : ProjectiveTensor E G →L[ℂ] ProjectiveTensor X Y :=
      ⟨projectiveTensorMap d.toLinearMap j.toLinearMap, projectiveTensorMap_continuous d j⟩
    obtain ⟨K, hK⟩ := h
    refine ⟨L.completion K, (L.completion.continuous.continuousAt.tendsto.comp hK).congr ?_⟩
    intro ij
    unfold Function.comp spectralKernelRectangle
    rw [ContinuousLinearMap.completion_apply_coe]
    apply congrArg ((↑) : ProjectiveTensor X Y → Π(X, Y))
    change projectiveTensorMap d.toLinearMap j.toLinearMap _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro z _
    exact (map_sum (TensorProduct.map d.toLinearMap j.toLinearMap)
      (fun m : Fin (N z) ↦ u (i z m) ⊗ₜ[ℂ] v (i z m)) Finset.univ).trans
      (Finset.sum_congr rfl fun m _ ↦ TensorProduct.map_tmul _ _ _ _)
  let E := H(a, (le_refl (0 : ℝ)), hs₀(hs))
  let θ := Θ(a, (le_refl (0 : ℝ)), hs₀(hs))
  let d : StrongDual ℂ E →L[ℂ] W'(0, s) := ⟨D₀,
    (spectralSobolevDualEmbedding_isometry_range (F := F) a (hStrip((le_refl (0 : ℝ)))) hs₀(hs)).1.continuous⟩
  let j : E →L[ℂ] W(0, s) := θ.orthogonal.subtypeL.comp
    θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  exact lift d j e _ _ _ _ (spectralLineQuotientKernel_tendsto (F := F) a hs _ha χ eχ e x f _hχ _he _horder _hb φ)

/-- A rectangle eventually contains the only jet that contributes to a single coordinate. -/
private theorem spectralLineAmbientKernel_operator_single {Z J V : Type*} [AddCommMonoid V]
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (j : (z : Z) → Fin (N z) → J)
    (hj : Bijective (fun p : (z : Z) × Fin (N z) ↦ j p.1 p.2))
    (i : J) (c : J → V) (hc : ∀ k, k ≠ i → c k = 0) :
    ∀ᶠ ij : ℕ × ℕ in atTop,
      (∑ z ∈ ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn,
        ∑ m : Fin (N z), c (j z m)) = c i := by
  classical
  obtain ⟨p, hp⟩ := hj.surjective i
  filter_upwards [eventually_ge_atTop (e p.1)] with ij hij
  rw [Finset.sum_sigma', Finset.sum_eq_single_of_mem p]
  · exact congrArg c hp
  · simp [Finset.mem_product, hij.1, hij.2]
  · intro q _ hq
    exact hc _ (fun h ↦ hq (hj.injective (h.trans hp.symm)))

/-- Evaluation of the ambient kernel rectangle is the finite sum of its rank-one actions. -/
private theorem spectralLineAmbientKernel_operator_eval {Z J : Type*} {α s : ℝ}
    (a : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (e : Z ↪ ℕ × ℕ) (N : Z → ℕ)
    (j : (z : Z) → Fin (N z) → J) (f : J → StrongDual ℂ H(a, hα, hs))
    (y : J → W(α, s)) (ij : ℕ × ℕ) (v : W(α, s)) :
    sobolevProjectiveKernelOperator (F := F) hα hs
      (spectralKernelRectangle e N j (fun k ↦ spectralSobolevDualEmbedding F a (hStrip(hα)) hs (f k))
        y ij) v =
      ∑ z ∈ ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn,
        ∑ m : Fin (N z), f (j z m) (Q(a, hα, hs) v) • y (j z m) := by
  let M := (((ContinuousLinearMap.apply ℂ (W(α, s)) v).comp
    (sobolevProjectiveKernelOperator (F := F) hα hs)).comp
    (Completion.toComplL : ProjectiveTensor W'(α, s) W(α, s) →L[ℂ] _))
  change M _ = _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  let term (m : Fin (N z)) : ProjectiveTensor W'(α, s) W(α, s) :=
    spectralSobolevDualEmbedding F a (hStrip(hα)) hs (f (j z m)) ⊗ₜ[ℂ] y (j z m)
  refine (map_sum M term Finset.univ).trans (Finset.sum_congr rfl ?_)
  intro m _
  apply (sobolevProjectiveKernelOperator_tmul hα hs _ _ v).trans
  exact congrArg (fun c : ℂ ↦ c • y (j z m))
    (spectralSobolevPairing_dual (hStrip(hα)) hs ((f (j z m)).comp (Q(a, hα, hs))) v).2.symm

/-- A limit of lifted biorthogonal partial sums recovers its prescribed quotient coordinates. -/
private theorem spectralLineAmbientKernel_operator_limit {Z J H V : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (q : V →L[ℂ] H) (S : H →L[ℂ] V) (hq : ∀ u, q (S u) = u)
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (j : (z : Z) → Fin (N z) → J)
    (hj : Bijective (fun p : (z : Z) × Fin (N z) ↦ j p.1 p.2))
    (x : J → H) (f : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x f)
    (u : H) (w : V)
    (h : Tendsto (fun ij : ℕ × ℕ ↦
      ∑ z ∈ ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn,
        ∑ m : Fin (N z), f (j z m) u • S (x (j z m))) atTop (𝓝 w)) :
    w = S u := by
  let b (ij : ℕ × ℕ) := ∑ z ∈ ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn,
    ∑ m : Fin (N z), f (j z m) u • x (j z m)
  have hS : Tendsto (fun ij ↦ S (b ij)) atTop (𝓝 w) := by simpa only [b, map_sum, map_smul] using h
  have hq' : Tendsto b atTop (𝓝 (q w)) := by
    simpa only [Function.comp_def, hq] using (q.continuous.tendsto w).comp hS
  have he : ContinuousLinearMap.apply ℂ ℂ (q w) = ContinuousLinearMap.apply ℂ ℂ u := by
    apply ContinuousLinearMap.ext_on hb.2.2.2
    rintro _ ⟨i, rfl⟩
    change f i (q w) = f i u
    apply tendsto_nhds_unique ((f i).continuous.continuousAt.tendsto.comp hq')
    apply tendsto_const_nhds.congr'
    have hcoord := spectralLineAmbientKernel_operator_single e N j hj i
      (fun k ↦ f k u * f i (x k)) (fun k hk ↦ by rw [hb.2.1 k i hk, mul_zero])
    filter_upwards [hcoord] with ij hij
    simpa only [Function.comp_apply, b, map_sum, map_smul, smul_eq_mul, hb.1, mul_one] using hij.symm
  have hqu : q w = u := (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    (fun ℓ ↦ DFunLike.congr_fun he ℓ)
  rw [← hqu]
  exact tendsto_nhds_unique hS ((S.continuous.tendsto _).comp hq')

/-- Paper: Theorem 10.4.3.1(3), p. 467. The limit of the ambient kernels
represents spectral projection after convolution. -/
theorem spectralLineAmbientKernel_operator (_ha : 0 < a)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ)
    (x : SpectralLineJetIndex χ a s → H(a, (le_refl (0 : ℝ)), hs₀(hs)))
    (f : SpectralLineJetIndex χ a s → StrongDual ℂ H(a, (le_refl (0 : ℝ)), hs₀(hs)))
    (_hχ : IsSpectralBasepointChoice χ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (_horder : Order₀(χ, e)) (_hb : Bases₀(χ, x, f)) (φ : BruhatCompactSupport C𝔽)
    (K : Π(W'(0, s), W(0, s)))
    (_hK : Tendsto (spectralKernelRectangle e (fun z ↦ N(χ, z)) jet
      (fun j ↦ D₀ ((f j).comp (Aq₀(φ)))) (fun j ↦ S₀ (x j))) atTop (𝓝 K)) :
    sobolevProjectiveKernelOperator (F := F) (le_refl (0 : ℝ)) hs₀(hs) K =
      (Pspec(a, (le_refl (0 : ℝ)), hs₀(hs))).comp (A₀(φ)) := by
  let θ := Θ(a, (le_refl (0 : ℝ)), hs₀(hs))
  let lift := θ.orthogonal.subtypeL.comp θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hsection (u) : θ.mkQL (lift u) = u :=
    (θ.quotientEquivOrthogonal_symm_eq_mk _ (θ.quotientEquivOrthogonal u).property).symm.trans
      (θ.quotientEquivOrthogonal.symm_apply_apply u)
  let key (z : Z(χ)) (m : Fin N(χ, z)) : SpectralLineJetIndex χ a s :=
    ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
  let index : ((z : Z(χ)) × Fin N(χ, z)) ≃ SpectralLineJetIndex χ a s :=
    ⟨fun p ↦ key p.1 p.2,
      fun j ↦ ⟨⟨(j.val.1, j.val.2.1), SpectralLineJetIndex.order_pos j⟩, ⟨j.val.2.2, j.property⟩⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  apply Eq.trans _ (spectralProjection_convolution_factor (F := F) a (le_refl (0 : ℝ)) hs₀(hs) φ).symm
  apply ContinuousLinearMap.ext
  intro v
  apply spectralLineAmbientKernel_operator_limit θ.mkQL lift hsection e (fun z ↦ N(χ, z)) key
    index.bijective x f _hb.1 ((Aq₀(φ)) (θ.mkQL v))
  let ev := (ContinuousLinearMap.apply ℂ (W(0, s)) v).comp
    (sobolevProjectiveKernelOperator (F := F) (le_refl (0 : ℝ)) hs₀(hs))
  refine ((ev.continuous.tendsto K).comp _hK).congr fun ij ↦ ?_
  exact spectralLineAmbientKernel_operator_eval a (le_refl (0 : ℝ)) hs₀(hs) e (fun z ↦ N(χ, z)) key
    (fun j ↦ (f j).comp (Aq₀(φ))) (fun j ↦ lift (x j)) ij v

end LineTensors

section MeasurableKernels

variable {α s : ℝ}

local notation "L²mixed" => Lp ℂ 2 ((ν(α, s)).prod (ν'(α, s)))
local notation "integrates(" μ ", " B ", " k ")" =>
  (∀ u : W(α, s), ∀ᵐ x ∂μ,
    Integrable (fun y ↦ k (x, y) * u y) μ ∧
    (B u : C𝔽 → ℂ) x = ∫ y, k (x, y) * u y ∂μ)

section MixedProjectiveKernel

open scoped ENNReal NNReal

/-- Dividing a mixed-weight kernel by its input weight changes square integrability
from the reciprocal input measure to the positive input measure. -/
private theorem spectralStripKernel_hilbertSchmidt_memLp {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SFinite μ]
    (w : X → ℝ≥0) (hw : Measurable w) (hp : ∀ x, 0 < w x)
    {k : X × X → ℂ} (hm : StronglyMeasurable k)
    (hk : MemLp k 2 (ν.prod (μ.withDensity fun y ↦ ↑((w y)⁻¹)))) :
    MemLp (fun p : X × X ↦ ((w p.2 : ℝ)⁻¹) • k p) 2
      (ν.prod (μ.withDensity fun y ↦ ↑(w y))) := by
  have hmeas : Measurable fun p : X × X ↦ (w p.2 : ℝ)⁻¹ :=
    (NNReal.continuous_coe.measurable.comp (hw.comp measurable_snd)).inv
  have hw' : Measurable (fun y ↦ (w y : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp hw
  have hwi : Measurable (fun y ↦ (((w y)⁻¹ : ℝ≥0) : ℝ≥0∞)) := by fun_prop
  have hw2 : Measurable (fun p : X × X ↦ w p.2) := hw.comp measurable_snd
  have him : Measurable (fun p : X × X ↦ (w p.2)⁻¹) := by fun_prop
  have hsq := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hk
  rw [prod_withDensity_right (μ := ν) (ν := μ) hwi,
    integrable_withDensity_iff_integrable_smul him] at hsq
  apply (memLp_two_iff_integrable_sq_norm (f := fun p : X × X ↦ (w p.2 : ℝ)⁻¹ • k p)
    (hmeas.stronglyMeasurable.smul hm).aestronglyMeasurable).mpr
  rw [prod_withDensity_right (μ := ν) (ν := μ) hw',
    integrable_withDensity_iff_integrable_smul hw2]
  apply hsq.congr
  refine Filter.Eventually.of_forall fun p ↦ ?_
  change ((w p.2)⁻¹ : ℝ≥0) * (‖k p‖ ^ 2 : ℝ) = (w p.2 : ℝ) * ‖(w p.2 : ℝ)⁻¹ • k p‖ ^ 2
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (w p.2).coe_nonneg), NNReal.coe_inv]
  field_simp [(NNReal.coe_pos.mpr (hp p.2)).ne']

/-- Integration against the normalized kernel with the weighted measure realizes
the operator given by integration against the original kernel with Haar measure. -/
private theorem spectralStripKernel_hilbertSchmidt_operator {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [SFinite μ] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular] [SFinite ν]
    (w : X → ℝ≥0) (hw : Measurable w) (hp : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity fun y ↦ ↑(w y))
    (op : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (k : X × X → ℂ) (hm : StronglyMeasurable k)
    (hk : MemLp k 2 (ν.prod (μ.withDensity fun y ↦ ↑((w y)⁻¹))))
    (hrow : ∀ u : Lp ℂ 2 ν, ∀ᵐ x ∂μ, op u x = ∫ y, k (x, y) * u y ∂μ) :
    let K (p : X × X) := ((w p.2 : ℝ)⁻¹) • k p
    ∃ h : MemLp K 2 (ν.prod ν), (integralKernelOperator ν (h.toLp K)).val = op := by
  intro K
  have hK : MemLp K 2 (ν.prod ν) := by
    simpa only [← hν] using spectralStripKernel_hilbertSchmidt_memLp μ ν w hw hp hm hk
  have integral_weighted (g : X → ℂ) : (∫ y, g y ∂ν) = ∫ y, w y • g y ∂μ := by
    rw [hν, integral_withDensity_eq_integral_smul hw]
  refine ⟨hK, ?_⟩
  ext u
  have hμν : ν ≪ μ := hν ▸ withDensity_absolutelyContinuous _ _
  filter_upwards [integralKernelOperator_apply ν (hK.toLp K) u,
    Measure.ae_ae_of_ae_prod hK.coeFn_toLp, hμν.ae_le (hrow u)] with x hx hrep hB
  rw [hx.2, hB]
  calc
    _ = ∫ y, K (x, y) * u y ∂ν :=
      integral_congr_ae (hrep.mono fun y hy ↦ congrArg (· * u y) hy)
    _ = ∫ y, k (x, y) * u y ∂μ := by
      rw [integral_weighted]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
      change (w y : ℝ) • (((w y : ℝ)⁻¹ • k (x, y)) * u y) = _
      rw [← smul_mul_assoc, smul_smul, mul_inv_cancel₀ (NNReal.coe_pos.mpr (hp y)).ne', one_smul]

/-- Every nuclear Hilbert endomorphism is Hilbert–Schmidt. -/
private theorem sobolevProjectiveKernel_mem_hilbertSchmidt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) (hT : IsNuclearOperator T) : T ∈ hilbertSchmidtOperators H H := by
  obtain ⟨A, B, rfl⟩ := exists_hilbertSchmidt_factorization T hT
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  apply (mem_hilbertSchmidtOperators_iff_summable_basis b _).2
  have hs := (mem_hilbertSchmidtOperators_iff_summable_basis b B.val).1 B.property
  apply (hs.mul_left (‖A.val‖ ^ 2)).of_nonneg_of_le (fun i ↦ sq_nonneg _)
  intro i
  simpa only [ContinuousLinearMap.comp_apply, mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 (A.val.le_opNorm (B.val (b i)))

/-- A nuclear operator on a weighted L² space has a unique mixed-weight kernel
that realizes it by integration against the underlying measure. -/
private theorem sobolevProjectiveKernel_mixed_existsUnique {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [SFinite μ] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular] [SFinite ν]
    (w : X → ℝ≥0) (hw : Measurable w) (hp : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity fun y ↦ ↑(w y))
    (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (hT : IsNuclearOperator T) :
    let ν' := μ.withDensity fun y ↦ ↑((w y)⁻¹)
    ∃! k : Lp ℂ 2 (ν.prod ν'), ∀ u : Lp ℂ 2 ν, ∀ᵐ x ∂μ,
      Integrable (fun y ↦ k (x, y) * u y) μ ∧ T u x = ∫ y, k (x, y) * u y ∂μ := by
  intro ν'
  let S : hilbertSchmidtOperators (Lp ℂ 2 ν) (Lp ℂ 2 ν) := ⟨T, sobolevProjectiveKernel_mem_hilbertSchmidt T hT⟩
  obtain ⟨K, hK⟩ := (bijective_integralKernelOperator ν).surjective S
  let raw (p : X × X) : ℂ := (w p.2 : ℝ) • K p
  have hraw : MemLp raw 2 (ν.prod ν') := by
    let v : X → ℝ≥0 := fun y ↦ (w y)⁻¹
    have hv : Measurable v := hw.inv
    have hKmem : MemLp (K : X × X → ℂ) 2 (ν.prod (μ.withDensity fun y ↦ ↑((v y)⁻¹))) := by
      simpa only [v, inv_inv, ← hν] using Lp.memLp K
    have h := spectralStripKernel_hilbertSchmidt_memLp μ ν v hv (fun y ↦ inv_pos.mpr (hp y))
      (Lp.stronglyMeasurable K) hKmem
    simpa only [v, NNReal.coe_inv, inv_inv, raw, ν'] using h
  let k := hraw.toLp raw
  have hrep : (k : X × X → ℂ) =ᵐ[ν.prod ν'] raw := hraw.coeFn_toLp
  have hμν : μ ≪ ν := by
    rw [hν]
    exact withDensity_absolutelyContinuous' (ENNReal.continuous_coe.measurable.comp hw).aemeasurable
      (.of_forall fun y ↦ ENNReal.coe_ne_zero.mpr (hp y).ne')
  have hμν' : μ ≪ ν' :=
    withDensity_absolutelyContinuous'
      (show Measurable (fun y ↦ (((w y)⁻¹ : ℝ≥0) : ℝ≥0∞)) by fun_prop).aemeasurable
      (.of_forall fun y ↦ ENNReal.coe_ne_zero.mpr (inv_pos.mpr (hp y)).ne')
  have hi (g : X → ℂ) : Integrable g ν ↔ Integrable (fun y ↦ w y • g y) μ := by
    rw [hν, integrable_withDensity_iff_integrable_smul hw]
  have hInt (g : X → ℂ) : (∫ y, g y ∂ν) = ∫ y, w y • g y ∂μ := by
    rw [hν, integral_withDensity_eq_integral_smul hw]
  refine ⟨k, ?_, ?_⟩
  · intro u
    have rows := integralKernelOperator_apply ν K u
    rw [hK] at rows
    filter_upwards [hμν.ae_le rows, hμν.ae_le (Measure.ae_ae_of_ae_prod hrep)] with x hx hxr
    have hrow : (fun y ↦ w y • (K (x, y) * u y)) =ᵐ[μ] fun y ↦ k (x, y) * u y := by
      filter_upwards [hμν'.ae_le hxr] with y hy
      rw [hy]
      change (w y : ℝ) • (K (x, y) * u y) = ((w y : ℝ) • K (x, y)) * u y
      rw [smul_mul_assoc]
    exact ⟨((hi _).1 hx.1).congr hrow, hx.2.trans ((hInt _).trans (integral_congr_ae hrow))⟩
  · intro b hb
    obtain ⟨h, he⟩ := spectralStripKernel_hilbertSchmidt_operator μ ν w hw hp hν T b
      (Lp.stronglyMeasurable b) (Lp.memLp b) (fun u ↦ (hb u).mono fun _ hu ↦ hu.2)
    have hequal : h.toLp _ = K := (bijective_integralKernelOperator ν).injective
      (Subtype.ext (he.trans (congrArg Subtype.val hK).symm))
    have hae : (fun p : X × X ↦ (w p.2 : ℝ)⁻¹ • b p) =ᵐ[ν.prod ν] K :=
      h.coeFn_toLp.symm.trans (by rw [hequal])
    have hac : ν.prod ν' ≪ ν.prod ν :=
      Measure.AbsolutelyContinuous.rfl.prod ((withDensity_absolutelyContinuous μ _).trans hμν)
    apply Lp.ext
    filter_upwards [hac.ae_le hae, hrep] with p hp' hk'
    rw [hk']
    change b p = (w p.2 : ℝ) • K p
    rw [← hp']
    rw [smul_smul, mul_inv_cancel₀ (NNReal.coe_pos.mpr (hp p.2)).ne', one_smul]

end MixedProjectiveKernel

/-- Paper: (10.4.3.23)–(10.4.3.25), p. 470. A projective kernel has a unique
square-integrable mixed-weight kernel whose unweighted integral realizes its operator.
Deviation: The product has positive weight in the output coordinate and reciprocal
weight in the input coordinate. The Sobolev duality is already unweighted, so
(10.4.3.25) needs no additional weight in the integral. The same correspondence
is used on compact symmetric intervals. -/
theorem sobolevProjectiveKernel_existsUnique_l2 (hα : 0 ≤ α) (hs : 0 ≤ s)
    (K : Π(W'(α, s), W(α, s))) :
    ∃! k : L²mixed, integrates(μ𝔽, sobolevProjectiveKernelOperator (F := F) hα hs K, k) :=
  by
    let ν := ν(α, s)
    let wi (y : C𝔽) := w(α, s) y
    have hp (y : C𝔽) : 0 < wi y := intervalSobolevDensity_pos' _ _ _ _
    let wNN (y : C𝔽) : ℝ≥0 := ⟨wi y, (hp y).le⟩
    have hw : Continuous wi :=
      (continuous_intervalSobolevDensity (-α) α s).comp (continuous_logModule' m𝔽)
    have hwNN : Continuous wNN := hw.subtype_mk _
    have hν : ν = (μ𝔽).withDensity (fun y ↦ (wNN y : ENNReal)) :=
      congrArg (μ𝔽).withDensity (funext fun y ↦ ENNReal.ofReal_eq_coe_nnreal (hp y).le)
    have hν' : ν'(α, s) = (μ𝔽).withDensity (fun y ↦ (((wNN y)⁻¹ : ℝ≥0) : ENNReal)) := by
      apply congrArg (μ𝔽).withDensity
      funext y
      exact ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr (hp y).le)
    let : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
    let op := sobolevProjectiveKernelOperator (F := F) hα hs K
    have hn : IsNuclearOperator op := (isNuclearOperator_iff_isBanachNuclear _).2
      ((isBanachNuclear_iff_mem_range _).2 ⟨_, rfl⟩)
    let pred (η : Measure C𝔽) := ∃! k : Lp ℂ 2 (ν.prod η), integrates(μ𝔽, op, k)
    change pred (ν'(α, s))
    rw [hν']
    exact sobolevProjectiveKernel_mixed_existsUnique μ𝔽 ν wNN hwNN.measurable hp hν op hn

/-- Paper: (10.4.3.23)–(10.4.3.25), p. 470.
The product of two weighted square-integrable functions lies in the mixed product space. -/
private theorem sobolevProjectiveKernel_l2_tmul_memLp
    {F : Type*} [Field F] [NumberField F]
    {α s : ℝ}
    (v : (CompactIntervalSobolev (ideleClassTamagawaMeasure F) (fun g : IdeleClassGroup (𝓞 F) F ↦
        Real.log ((ideleClassNorm F g).val : ℝ)) (-α) α s true)) (u : (CompactIntervalSobolev
        (ideleClassTamagawaMeasure F) (fun g : IdeleClassGroup (𝓞 F) F ↦ Real.log ((ideleClassNorm F
        g).val : ℝ)) (-α) α s)) :
    MemLp (fun p : (IdeleClassGroup (𝓞 F) F) × (IdeleClassGroup (𝓞 F) F) ↦ v p.2 * u p.1) 2
      ((((ideleClassTamagawaMeasure F).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity
          (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ))))).prod (((ideleClassTamagawaMeasure
          F).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (Real.log
          ((ideleClassNorm F g).val : ℝ)))⁻¹))) := by
  have hu := Lp.memLp u
  have hv := Lp.memLp v
  have hm : AEStronglyMeasurable (fun p : (IdeleClassGroup (𝓞 F) F) × (IdeleClassGroup (𝓞 F) F) ↦ v
      p.2 * u p.1)
      ((((ideleClassTamagawaMeasure F).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity
          (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ))))).prod (((ideleClassTamagawaMeasure
          F).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (Real.log
          ((ideleClassNorm F g).val : ℝ)))⁻¹))) :=
    hv.aestronglyMeasurable.comp_snd.mul hu.aestronglyMeasurable.comp_fst
  refine (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top (by norm_num)
    (by norm_num) hm).mpr ?_
  simp only [eNorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (2 : ENNReal).toReal)]
  simp_rw [mul_comm (‖v _‖ₑ ^ (2 : ENNReal).toReal)]
  rw [lintegral_prod_mul (f := fun x ↦ ‖u x‖ₑ ^ (2 : ENNReal).toReal)
    (g := fun y ↦ ‖v y‖ₑ ^ (2 : ENNReal).toReal)
    (by fun_prop) (by fun_prop)]
  exact ENNReal.mul_lt_top
    (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num) hu.eLpNorm_lt_top)
    (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num) hv.eLpNorm_lt_top)

/-- Paper: (10.4.3.23)–(10.4.3.25), p. 470.
An almost-everywhere product representative integrates to the elementary tensor operator. -/
private theorem sobolevProjectiveKernel_l2_tmul_integrates
    {F : Type*} [Field F] [NumberField F] {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) (v : (CompactIntervalSobolev (ideleClassTamagawaMeasure F) (fun g :
        IdeleClassGroup (𝓞 F) F ↦ Real.log ((ideleClassNorm F g).val : ℝ)) (-α) α s true)) (u :
        (CompactIntervalSobolev (ideleClassTamagawaMeasure F) (fun g : IdeleClassGroup (𝓞 F) F ↦
        Real.log ((ideleClassNorm F g).val : ℝ)) (-α) α s))
    (k : Lp ℂ 2 ((((ideleClassTamagawaMeasure F).withDensity fun g ↦ ENNReal.ofReal
        (intervalSobolevDensity (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ))))).prod
        (((ideleClassTamagawaMeasure F).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity
        (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹))))
    (hk : (k : (IdeleClassGroup (𝓞 F) F) × (IdeleClassGroup (𝓞 F) F) → ℂ)
        =ᵐ[(((ideleClassTamagawaMeasure F).withDensity fun g ↦ ENNReal.ofReal
        (intervalSobolevDensity (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ))))).prod
        (((ideleClassTamagawaMeasure F).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity
        (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹))]
      (fun p ↦ v p.2 * u p.1)) :
    ∀ f : (CompactIntervalSobolev (ideleClassTamagawaMeasure F) (fun g : IdeleClassGroup (𝓞 F) F ↦
        Real.log ((ideleClassNorm F g).val : ℝ)) (-α) α s), ∀ᵐ x ∂(ideleClassTamagawaMeasure F),
      Integrable (fun y ↦ k (x, y) * f y) (ideleClassTamagawaMeasure F) ∧
      (sobolevProjectiveKernelOperator (F := F) hα hs
      ((show ProjectiveTensor (CompactIntervalSobolev (ideleClassTamagawaMeasure F) (fun g :
          IdeleClassGroup (𝓞 F) F ↦ Real.log ((ideleClassNorm F g).val : ℝ)) (-α) α s true)
          (CompactIntervalSobolev (ideleClassTamagawaMeasure F) (fun g : IdeleClassGroup (𝓞 F) F ↦
          Real.log ((ideleClassNorm F g).val : ℝ)) (-α) α s) from v ⊗ₜ[ℂ] u) :
        Completion (ProjectiveTensor (CompactIntervalSobolev (ideleClassTamagawaMeasure F) (fun g :
            IdeleClassGroup (𝓞 F) F ↦ Real.log ((ideleClassNorm F g).val : ℝ)) (-α) α s true)
            (CompactIntervalSobolev (ideleClassTamagawaMeasure F) (fun g : IdeleClassGroup (𝓞 F) F ↦
            Real.log ((ideleClassNorm F g).val : ℝ)) (-α) α s))) f : (IdeleClassGroup (𝓞 F) F) → ℂ)
            x = ∫ y, k (x, y) * f y ∂(ideleClassTamagawaMeasure F) := by
  have hw : Measurable ((fun g : IdeleClassGroup (𝓞 F) F ↦ intervalSobolevDensity (-α) α s (Real.log
      ((ideleClassNorm F g).val : ℝ)))) :=
    ((continuous_intervalSobolevDensity (-α) α s).comp
      (continuous_logModule' (continuousIdeleClassNorm F :
          IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ))).measurable
  have hp (x : (IdeleClassGroup (𝓞 F) F)) : 0 < (fun g : IdeleClassGroup (𝓞 F) F ↦
      intervalSobolevDensity (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ))) x :=
      intervalSobolevDensity_pos' _ _ _ _
  have ha (p : (IdeleClassGroup (𝓞 F) F) → Prop) (h : ∀ᵐ x ∂((ideleClassTamagawaMeasure
      F).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (Real.log
      ((ideleClassNorm F g).val : ℝ)))), p x) : ∀ᵐ x ∂(ideleClassTamagawaMeasure F), p x := by
    exact ((ae_withDensity_iff hw.ennreal_ofReal).mp h).mono
      (fun x hx ↦ hx (ne_of_gt (ENNReal.ofReal_pos.mpr (hp x))))
  have ha' (p : (IdeleClassGroup (𝓞 F) F) → Prop) (h : ∀ᵐ x ∂((ideleClassTamagawaMeasure
      F).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (Real.log
      ((ideleClassNorm F g).val : ℝ)))⁻¹), p x) : ∀ᵐ x ∂(ideleClassTamagawaMeasure F), p x := by
    exact ((ae_withDensity_iff hw.inv.ennreal_ofReal).mp h).mono
      (fun x hx ↦ hx (ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hp x)))))
  have hk' := ha _ (Measure.ae_ae_of_ae_prod hk)
  intro f
  let T := (modulatedIntervalSobolev_dual (⟨ideleClassNorm F, (isProperMap_ideleClassNorm
      F).continuous⟩ : IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ)
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    (ideleClassTamagawaMeasure F) (-α) α s ((neg_nonpos.mpr hα).trans hα) hs).exists.choose
  have hi : Integrable (fun y ↦ f y * v y) (ideleClassTamagawaMeasure F) := by
    have hh := (spectralSobolevPairing_dual ((neg_nonpos.mpr hα).trans hα) hs (T.symm v) f).1
    simpa only [T, LinearIsometryEquiv.apply_symm_apply] using hh
  have hu := ha _ (Lp.coeFn_smul (spectralSobolevPairing (F := F) f v) u)
  filter_upwards [hk', hu] with x hx hux
  have he : (fun y ↦ k (x, y) * f y) =ᵐ[(ideleClassTamagawaMeasure F)] (fun y ↦ (f y * v y) * u x)
      := by
    filter_upwards [ha' _ hx] with y hy
    rw [hy]
    ring
  refine ⟨(hi.mul_const (u x)).congr he.symm, ?_⟩
  rw [sobolevProjectiveKernelOperator_tmul, hux, integral_congr_ae he, integral_mul_const]
  rfl

/-- Paper: (10.4.3.23)–(10.4.3.25), p. 470. An elementary tensor has
mixed-weight representative given by the product of its factors.
Deviation: The reciprocal-weight factor is evaluated at the input coordinate. -/
theorem sobolevProjectiveKernel_l2_tmul (hα : 0 ≤ α) (hs : 0 ≤ s)
    (v : W'(α, s)) (u : W(α, s)) :
    ∃ k : L²mixed,
      (k : C𝔽 × C𝔽 → ℂ) =ᵐ[(ν(α, s)).prod (ν'(α, s))] (fun p ↦ v p.2 * u p.1) ∧
      integrates(μ𝔽, sobolevProjectiveKernelOperator (F := F) hα hs
        ((show ProjectiveTensor W'(α, s) W(α, s) from v ⊗ₜ[ℂ] u) : Π(W'(α, s), W(α, s))), k) :=
  by
    let h := sobolevProjectiveKernel_l2_tmul_memLp (F := F) v u
    let k : L²mixed := h.toLp (fun p ↦ v p.2 * u p.1)
    refine ⟨k, ?_, ?_⟩
    · exact h.coeFn_toLp
    · exact sobolevProjectiveKernel_l2_tmul_integrates (F := F) hα hs v u k h.coeFn_toLp

/-- Paper: (10.4.3.23)–(10.4.3.25), p. 470. A projective tensor has
a mixed-weight kernel class giving its operator under Haar integration.
Deviation: The output coordinate comes first. -/
def sobolevProjectiveKernelClass (hα : 0 ≤ α) (hs : 0 ≤ s)
    (K : Π(W'(α, s), W(α, s))) : L²mixed :=
  (sobolevProjectiveKernel_existsUnique_l2 hα hs K).exists.choose

/-- Paper: (10.4.3.23)–(10.4.3.25), p. 470. The tensor kernel has the
stated operator, and two classes giving that operator agree. -/
theorem sobolevProjectiveKernelClass_spec (hα : 0 ≤ α) (hs : 0 ≤ s)
    (K : Π(W'(α, s), W(α, s))) (k : L²mixed) :
    integrates(μ𝔽, sobolevProjectiveKernelOperator (F := F) hα hs K, k) ↔
      k = sobolevProjectiveKernelClass hα hs K := by
  have hu := sobolevProjectiveKernel_existsUnique_l2 (F := F) hα hs K
  constructor
  · exact fun hk ↦ hu.unique hk hu.exists.choose_spec
  · rintro rfl
    exact hu.exists.choose_spec

/-- The continuous Sobolev density is locally bounded on the idèle class group. -/
theorem sobolevKernelWeight_locallyFinite (α s : ℝ) :
    IsLocallyFiniteMeasure (ν(α, s)) := by
  apply IsLocallyFiniteMeasure.withDensity_ofReal
  have ht : Continuous (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) :=
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous))).log fun g ↦
        ne_of_gt (NNReal.coe_pos.mpr (Units.zero_lt _))
  have hw : Continuous (intervalSobolevDensity (-α) α s) := by
    unfold intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
    positivity
  exact hw.comp ht

attribute [local instance] sobolevKernelWeight_locallyFinite

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471, and Theorem 10.4.3.6(2), p. 473.
A representative of an operator's Hilbert-Schmidt kernel is square-integrable
on the product with positive weights and gives the operator by integration in
the input variable against the positive Sobolev measure. -/
def IsSobolevHilbertSchmidtKernel (B : W(α, s) →L[ℂ] W(α, s))
    (k : C𝔽 × C𝔽 → ℂ) : Prop :=
  ∃ hk : MemLp k 2 ((ν(α, s)).prod (ν(α, s))),
    (integralKernelOperator (ν(α, s)) (hk.toLp k)).val = B

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471, and Theorem 10.4.3.6(2), p. 473.
The zero function represents the Hilbert-Schmidt kernel of the zero operator. -/
theorem isSobolevHilbertSchmidtKernel_zero :
    IsSobolevHilbertSchmidtKernel (0 : W(α, s) →L[ℂ] W(α, s)) 0 := by
  have hk : MemLp (0 : C𝔽 × C𝔽 → ℂ) 2 ((ν(α, s)).prod (ν(α, s))) := MemLp.zero
  refine ⟨hk, ?_⟩
  ext f
  have hz : hk.toLp (0 : C𝔽 × C𝔽 → ℂ) = 0 := MemLp.toLp_zero hk
  have h := integralKernelOperator_apply (ν(α, s)) (hk.toLp (0 : C𝔽 × C𝔽 → ℂ)) f
  rw [hz] at h ⊢
  have h0 := Measure.ae_ae_of_ae_prod
    (Lp.coeFn_zero ℂ 2 ((ν(α, s)).prod (ν(α, s))))
  filter_upwards [h, h0, Lp.coeFn_zero ℂ 2 (ν(α, s))] with x hx hx0 hf
  rw [hx.2, ContinuousLinearMap.zero_apply, hf]
  have : (fun y ↦ ((0 : Lp ℂ 2 ((ν(α, s)).prod (ν(α, s)))) : C𝔽 × C𝔽 → ℂ) (x, y) * f y)
      =ᵐ[ν(α, s)] fun _ ↦ 0 := by
    filter_upwards [hx0] with y hy
    rw [hy]; simp
  rw [integral_congr_ae this]
  simp

-- Theorems 10.4.3.4 and 10.4.3.6 state s > 1. The measurable formulas work
-- in that range once the mixed-weight spectral kernel exists.
variable (a : ℝ) (hα : 0 ≤ α) (hs : 1 < s)
  (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
variable {Λ ε : ℝ} {ρ : IdeleClassGroup (𝓞 F) F → ℝ}

local notation "hcut" => IsModulatedCutoff m𝔽 Λ ε ρ
local notation "innerBand" => (0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε)
local notation "Ps" => Pspec(a, hα, hs₀(hs))
local notation "Pg" => Pgeom(a, hα, hs₀(hs))
local notation "B" => A(hα, hs₀(hs), φ)
local notation "Bpre" => ((B).comp Ps)
local notation "kernelFor(" k ", " U ")" => integrates(μ𝔽, U, k)
local notation "weighted(" k ")" => (fun p : C𝔽 × C𝔽 ↦ ((w(α, s) p.2)⁻¹ : ℝ) • k p)
local notation "cut(" k ")" => (fun p : C𝔽 × C𝔽 ↦ ρ p.1 • k p)

section LineRepresentatives

local notation "hline" => (le_refl (0 : ℝ))
local notation "Θline" => Θ(a, hline, hs₀(hs))
local notation "Aline" => A(hline, hs₀(hs), φ)
local notation "Bline" => (Pspec(a, hline, hs₀(hs))).comp Aline
local notation "L²line" => Lp ℂ 2 ((ν(0, s)).prod (ν'(0, s)))

local notation "lineKernelFor(" k ")" =>
  (∀ u : W(0, s), ∀ᵐ x ∂μ𝔽,
    Integrable (fun y ↦ k (x, y) * u y) μ𝔽 ∧
    Bline u x = ∫ y, k (x, y) * u y ∂μ𝔽)

/-- Paper: Theorem 10.4.3.1(3) and Remark 10.4.3.3, pp. 467, 470. The line
operator has a unique mixed-weight kernel. Existence also follows from the
nuclearity and factorization of quotient convolution in §§10.3–10.4.2.
Deviation: That factorization applies to every real twist. -/
theorem spectralLineKernel_existsUnique :
    ∃! k : L²line, lineKernelFor(k) := by
  have hasTensor {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (op : E →L[ℂ] E) (hn : IsNuclearOperator (E := E) (F := E) op) :
      ∃ w : Completion (ProjectiveTensor (StrongDual ℂ E) E),
        completedProjectiveTensorToOperators (E := E) (F := E) w = op :=
    (isBanachNuclear_iff_mem_range (E := E) (F := E) op).mp
      ((isNuclearOperator_iff_isBanachNuclear (E := E) (F := E) op).mp hn)
  have transport {Y X E : Type _} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedAddCommGroup X] [NormedSpace ℂ X]
      [NormedAddCommGroup E] [NormedSpace ℂ E]
      (e : Y ≃ₗᵢ[ℂ] X) :
      let f := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
      let i : ProjectiveTensor X E →L[ℂ] ProjectiveTensor Y E :=
        ⟨projectiveTensorMap f.toLinearMap (LinearMap.id : E →ₗ[ℂ] E),
          projectiveTensorMap_continuous f (ContinuousLinearMap.id ℂ E)⟩
      Surjective i.completion := by
    intro f i
    exact completedProjectiveTensorMap_surjective f (ContinuousLinearMap.id ℂ E)
      e.symm.toHomeomorph.isQuotientMap Topology.IsQuotientMap.id
  let lineOp : W(0, s) →L[ℂ] W(0, s) := Bline
  have hB : IsNuclearOperator (E := W(0, s)) (F := W(0, s)) lineOp := spectralProjection_convolution_nuclear (F := F) a hline hs₀(hs) φ
    (spectralStripConvolution_nuclear (F := F) a hline hs φ)
  let e : StrongDual ℂ W(0, s) ≃ₗᵢ[ℂ] W'(0, s) := (modulatedIntervalSobolev_dual m𝔽
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    μ𝔽 (-(0 : ℝ)) 0 s (hStrip(hline)) hs₀(hs)).exists.choose
  have hrep := hasTensor (E := W(0, s)) lineOp hB
  have hlift := transport (Y := StrongDual ℂ W(0, s)) (E := W(0, s)) (X := W'(0, s)) e hrep.choose
  let K := hlift.choose
  have hEq : sobolevProjectiveKernelOperator (F := F) hline hs₀(hs) K = Bline :=
    (congrArg (completedProjectiveTensorToOperators (E := W(0, s)) (F := W(0, s))) hlift.choose_spec).trans hrep.choose_spec
  let property (op : W(0, s) →L[ℂ] W(0, s)) := ∃! k : L²line,
    ∀ u : W(0, s), ∀ᵐ x ∂μ𝔽, Integrable (fun y ↦ k (x, y) * u y) μ𝔽 ∧
      op u x = ∫ y, k (x, y) * u y ∂μ𝔽
  exact (congrArg property hEq).mp (sobolevProjectiveKernel_existsUnique_l2 (F := F) hline hs₀(hs) K)

/-- Paper: Definition 10.4.3.2(1), p. 470. The global line spectral kernel
is the representative of the unique kernel of projection after convolution.
Deviation: Use the unweighted Haar formula for every s > 1. -/
def globalLineSpectralKernel : L²line :=
  (spectralLineKernel_existsUnique (F := F) a hs φ).exists.choose

local notation "kLine" => globalLineSpectralKernel (F := F) a hs φ
local notation "weightedLine(" f ")" => (fun p : C𝔽 × C𝔽 ↦ ((w(0, s) p.2)⁻¹ : ℝ) • f p)

/-- Paper: Remark 10.4.3.3, p. 470. The global line kernel integrates to the
spectral projection of the convolution against each input. -/
theorem spectralLineKernel_apply : lineKernelFor(kLine) :=
  (spectralLineKernel_existsUnique (F := F) a hs φ).exists.choose_spec

/-- Paper: Definition 10.4.3.2(2), p. 470. Subtract the spectral kernel of
this test from its Haar convolution kernel. -/
def globalLineGeometricKernel (p : C𝔽 × C𝔽) : ℂ :=
  φ.val (p.1 * p.2⁻¹) - kLine p

local notation "geomLine" => globalLineGeometricKernel (F := F) a hs φ

/-- Evaluate the two projection identities on a vector fixed by the geometric projection. -/
private theorem geometricLineKernel_apply_projections {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (P Q A : E →L[ℂ] E) (u : E) (hu : P u = u)
    (hP : P.comp (A.comp P) = A.comp P) (hQ : Q.comp (A.comp P) = 0) :
    P (A u) = A u ∧ Q (A u) = 0 := by
  have hp := DFunLike.congr_fun hP u
  have hq := DFunLike.congr_fun hQ u
  simpa only [ContinuousLinearMap.comp_apply, hu, zero_apply] using And.intro hp hq

/-- Subtracting a spectral row of integral zero leaves the Haar convolution on the
given input. Inversion followed by translation gives the output-first kernel. -/
private theorem geometricLineKernel_apply_sub {G : Type*} [CommGroup G]
    [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsInvInvariant] (φ u A : G → ℂ) (k : G × G → ℂ)
    (hi : ∀ᵐ x ∂μ, Integrable (fun y ↦ φ y * u (y⁻¹ * x)) μ)
    (hA : ∀ᵐ x ∂μ, A x = ∫ y, φ y * u (y⁻¹ * x) ∂μ)
    (hk : ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * u y) μ ∧
      (∫ y, k (x, y) * u y ∂μ) = 0) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ (φ (x * y⁻¹) - k (x, y)) * u y) μ ∧
      A x = ∫ y, (φ (x * y⁻¹) - k (x, y)) * u y ∂μ := by
  filter_upwards [hi, hA, hk] with x hx hAx ⟨hkx, hzero⟩
  let f (g : G) := φ g * u (g⁻¹ * x)
  have hsub (y : G) : f (x / y) = φ (x * y⁻¹) * u y := by simp [f, div_eq_mul_inv]
  have hint : Integrable (fun y ↦ φ (x * y⁻¹) * u y) μ := by
    have hy := ((Measure.measurePreserving_div_left μ x).integrable_comp_emb
      (MeasurableEquiv.divLeft x).measurableEmbedding).mpr hx
    exact hy.congr (.of_forall hsub)
  simp only [sub_mul]
  refine ⟨hint.sub hkx, ?_⟩
  rw [integral_sub hint hkx, hzero, sub_zero, hAx, ← integral_div_left_eq_self f μ x]
  simp_rw [hsub]

/-- On a weighted Sobolev space, subtract the kernel of a vanishing projection block
from the convolution kernel. The positive weight transfers the zero representative to Haar measure. -/
private theorem geometricLineKernel_apply_rows {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)
    [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G)
    (u : CompactIntervalSobolev μ (fun g ↦ Real.log ((m g).val : ℝ)) a b s)
    (k : G × G → ℂ)
    (hk : ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * u y) μ ∧
      (0 : CompactIntervalSobolev μ (fun g ↦ Real.log ((m g).val : ℝ)) a b s) x =
        ∫ y, k (x, y) * u y ∂μ) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ (φ.val (x * y⁻¹) - k (x, y)) * u y) μ ∧
      hardySobolevTestAction μ m a b s hab hs φ u x =
        ∫ y, (φ.val (x * y⁻¹) - k (x, y)) * u y ∂μ := by
  have hc : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 φ.property.1)
  have hi := hc.integrable_of_hasCompactSupport (μ := μ) φ.property.2
  have horbit := hardySobolev_orbit_integral μ m a b s hab hs (φ := φ.val) hi φ.property.2 u
  let w (g : G) := intervalSobolevDensity a b s (Real.log ((m g).val : ℝ))
  have hw : Continuous w := (continuous_intervalSobolevDensity a b s).comp (continuous_logModule' m)
  let ν := μ.withDensity (fun g ↦ ENNReal.ofReal (w g))
  have hμ : μ ≪ ν := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun g ↦ (ENNReal.ofReal_pos.mpr (intervalSobolevDensity_pos' a b s _)).ne')
  apply geometricLineKernel_apply_sub μ φ.val u _ k (horbit.mono fun _ h ↦ h.1)
    (hardySobolevTestAction_apply μ m a b s hab hs φ u)
  filter_upwards [hk, hμ.ae_le (Lp.coeFn_zero ℂ 2 ν)] with x hx hx₀
  exact ⟨hx.1, hx.2.symm.trans hx₀⟩

/-- Paper: Theorem 10.4.3.4(1), p. 470. On a theta vector the global
geometric kernel represents convolution and geometric projection after convolution.
The tested row is Haar integrable almost everywhere. -/
theorem geometricLineKernel_apply (_ha : 0 < a)
    (u : W(0, s)) (_hu : u ∈ Θline) :
    ∀ᵐ x ∂μ𝔽, Integrable (fun y ↦ geomLine (x, y) * u y) μ𝔽 ∧
      Aline u x = (Pgeom(a, hline, hs₀(hs))).comp Aline u x ∧
      Aline u x = ∫ y, geomLine (x, y) * u y ∂μ𝔽 := by
  obtain ⟨hgeom, hspec⟩ := geometricLineKernel_apply_projections
    (Pgeom(a, hline, hs₀(hs))) (Pspec(a, hline, hs₀(hs))) Aline u
    (geometricProjection_apply_of_mem (F := F) a hline hs₀(hs) _hu)
    (geometricProjection_convolution_geometricProjection (F := F) a hline hs₀(hs) φ)
    (spectralProjection_convolution_geometricProjection (F := F) a hline hs₀(hs) φ)
  have hk := spectralLineKernel_apply (F := F) a hs φ u
  let row (v : W(0, s)) := ∀ᵐ x ∂μ𝔽, Integrable (fun y ↦ kLine (x, y) * u y) μ𝔽 ∧
    v x = ∫ y, kLine (x, y) * u y ∂μ𝔽
  have hk₀ : row 0 := Eq.mp (congrArg row hspec) hk
  -- Specialize the Haar identity before inserting the Sobolev vector and kernel.
  let haarRows := geometricLineKernel_apply_rows (G := C𝔽) μ𝔽 m𝔽 (-0) 0 s
    (hStrip(hline)) hs₀(hs) φ
  have hrows := haarRows u (kLine : C𝔽 × C𝔽 → ℂ) hk₀
  filter_upwards [hrows] with x hx
  exact ⟨hx.1, congrArg (fun v : W(0, s) ↦ v x) hgeom.symm, hx.2⟩

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471, first formula. Divide the
global spectral kernel by the input weight to obtain the Hilbert-Schmidt
representative of spectral projection after convolution. -/
theorem spectralLineKernel_hilbertSchmidt (_ha : 0 < a) :
    IsSobolevHilbertSchmidtKernel (F := F) Bline (weightedLine(kLine)) := by
  have hp (y : C𝔽) : 0 < w(0, s) y := intervalSobolevDensity_pos' _ _ _ _
  let wNN (y : C𝔽) : ℝ≥0 := ⟨w(0, s) y, (hp y).le⟩
  have hw : Continuous wNN :=
    ((continuous_intervalSobolevDensity (-0) 0 s).comp (continuous_logModule' m𝔽)).subtype_mk _
  have hν : ν(0, s) = (μ𝔽).withDensity (fun y ↦ (wNN y : ENNReal)) :=
    congrArg (μ𝔽).withDensity (funext fun y ↦ ENNReal.ofReal_eq_coe_nnreal (hp y).le)
  have hν' : ν'(0, s) = (μ𝔽).withDensity (fun y ↦ (((wNN y)⁻¹ : ℝ≥0) : ENNReal)) :=
    congrArg (μ𝔽).withDensity
      (funext fun y ↦ ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr (hp y).le))
  have hk : MemLp (kLine : C𝔽 × C𝔽 → ℂ) 2
      ((ν(0, s)).prod ((μ𝔽).withDensity fun y ↦ ↑((wNN y)⁻¹))) :=
    (congrArg (fun η : Measure C𝔽 ↦ MemLp (kLine : C𝔽 × C𝔽 → ℂ) 2 ((ν(0, s)).prod η)) hν').mp
      (Lp.memLp kLine)
  have hrow := spectralLineKernel_apply (F := F) a hs φ
  exact spectralStripKernel_hilbertSchmidt_operator μ𝔽 (ν(0, s)) wNN hw.measurable hp hν Bline
    kLine (Lp.stronglyMeasurable kLine) hk (fun u ↦ (hrow u).mono fun _ hx ↦ hx.2)

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471, second formula. Output
multiplication gives the representative of truncated spectral convolution.
Deviation: The target is spectral as in the proof on p. 471. The cutoff is
real-valued as in §9.3 and is viewed as a scalar on complex functions. -/
theorem spectralLineTruncatedKernel_hilbertSchmidt (_ha : 0 < a)
    (hρ : hcut) (_hband : innerBand) :
    IsSobolevHilbertSchmidtKernel (F := F) (spectralTruncatedConvolution (F := F) a hline hs₀(hs) hρ φ)
      (cut(weightedLine(kLine))) := by
  have mulKernel {X : Type _} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
      [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
      (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν] [SFinite ν]
      (r : X → ℝ) (hm : Measurable r) (hr : ∀ x, |r x| ≤ 1)
      (M : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (hM : ∀ f : Lp ℂ 2 ν,
        (M f : X → ℂ) =ᵐ[ν] fun x ↦ (r x : ℂ) * f x)
      {k : X × X → ℂ} (hk : MemLp k 2 (ν.prod ν)) :
      ∃ ha : MemLp (fun p : X × X ↦ r p.1 • k p) 2 (ν.prod ν),
        (integralKernelOperator ν (ha.toLp _)).val = M.comp (integralKernelOperator ν (hk.toLp k)).val := by
    have hb : MemLp (fun p : X × X ↦ r p.1) ⊤ (ν.prod ν) :=
      memLp_top_of_bound (hm.comp measurable_fst).aestronglyMeasurable 1
        (.of_forall fun p ↦ hr p.1)
    have ha : MemLp (fun p : X × X ↦ r p.1 • k p) 2 (ν.prod ν) := hb.smul hk
    refine ⟨ha, ?_⟩
    ext1 f
    apply Lp.ext
    filter_upwards [integralKernelOperator_apply ν (ha.toLp _) f,
      integralKernelOperator_apply ν (hk.toLp _) f, Measure.ae_ae_of_ae_prod ha.coeFn_toLp,
      Measure.ae_ae_of_ae_prod hk.coeFn_toLp, hM ((integralKernelOperator ν (hk.toLp _)).val f)]
      with x hx hx' hax hkx hmx
    change (integralKernelOperator ν (ha.toLp _)).val f x =
      M ((integralKernelOperator ν (hk.toLp _)).val f) x
    rw [hx.2, hmx, hx'.2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hax, hkx] with y ha' hk'
    rw [ha', hk']
    exact mul_assoc (r x : ℂ) (k (x, y)) (f y)
  obtain ⟨hk, hB⟩ := spectralLineKernel_hilbertSchmidt (F := F) a hs φ _ha
  let ν := ν(0, s)
  let M := modulatedCutoffOperator m𝔽 ν hρ
  obtain ⟨hg, he⟩ := mulKernel ν ρ hρ.measurable hρ.abs_le_one M (modulatedCutoffOperator_apply m𝔽 ν hρ) hk
  exact ⟨hg, he.trans (congrArg (fun U : W(0, s) →L[ℂ] W(0, s) ↦ M.comp U) hB)⟩

/-- Paper: Theorem 10.4.3.4(3), p. 471. Applying the cutoff in the
output variable and the reciprocal weight in the input variable gives the
Hilbert-Schmidt representative of truncated geometric convolution. -/
theorem geometricLineTruncatedKernel_hilbertSchmidt (_ha : 0 < a)
    (hρ : hcut) (_hband : innerBand) :
    IsSobolevHilbertSchmidtKernel (F := F) (geometricTruncatedConvolution (F := F) a hline hs₀(hs) hρ φ)
      (cut(weightedLine(geomLine))) := by
  have subKernel {X : Type _} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
      [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
      (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν] [SFinite ν]
      {k q g : X × X → ℂ} (hk : MemLp k 2 (ν.prod ν)) (hq : MemLp q 2 (ν.prod ν))
      (he : ∀ p, k p - q p = g p) (T Q G : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
      (ht : ∀ u : Lp ℂ 2 ν, ∀ᵐ x ∂ν, Integrable (fun y ↦ k (x,y) * u y) ν ∧
        T u x = ∫ y, k (x,y) * u y ∂ν)
      (hQ : (integralKernelOperator ν (hq.toLp q)).val = Q) (hsum : T = G + Q) :
      ∃ hg : MemLp g 2 (ν.prod ν), (integralKernelOperator ν (hg.toLp g)).val = G := by
    have hg : MemLp g 2 (ν.prod ν) := (hk.sub hq).ae_eq (.of_forall he)
    refine ⟨hg, ?_⟩
    ext1 u
    apply Lp.ext
    have hqs := integralKernelOperator_apply ν (hq.toLp q) u
    rw [hQ] at hqs
    have hd : (G u : X → ℂ) =ᵐ[ν] fun x ↦ T u x - Q u x := by
      rw [eq_sub_of_add_eq hsum.symm]
      exact Lp.coeFn_sub _ _
    filter_upwards [integralKernelOperator_apply ν (hg.toLp g) u, ht u, hqs, hd,
      Measure.ae_ae_of_ae_prod hg.coeFn_toLp, Measure.ae_ae_of_ae_prod hq.coeFn_toLp]
      with x hx ht' hqs' hd' hGx hQx
    rw [hx.2, hd', ht'.2, hqs'.2, ← integral_sub ht'.1 hqs'.1]
    apply integral_congr_ae
    filter_upwards [hGx, hQx] with y hy hz
    rw [hy, hz, ← he, sub_mul]
  let ν := ν(0, s)
  let M := modulatedCutoffOperator m𝔽 ν hρ
  let k : C𝔽 × C𝔽 → ℂ := fun p ↦ (ρ p.1 : ℂ) * φ.val (p.1 * p.2⁻¹) / (w(0, s) p.2 : ℂ)
  let q := cut(weightedLine(kLine))
  let g := cut(weightedLine(geomLine))
  have hφs := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsur : Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hk, hrow⟩ := truncatedHardySobolevConvolution_hilbertSchmidt μ𝔽 m𝔽 (-0) 0 s
    (hStrip(hline)) hs₀(hs) φ.val hc.aemeasurable φ.property.2 hb hm hsur hρ _hband
  obtain ⟨hq, hQ⟩ := spectralLineTruncatedKernel_hilbertSchmidt (F := F) a hs φ _ha hρ _hband
  have he (p : C𝔽 × C𝔽) : k p - q p = g p := by
    have alg (r w : ℝ) (z t : ℂ) :
        (r : ℂ) * z / (w : ℂ) - r • (w⁻¹ • t) = r • (w⁻¹ • (z - t)) := by
      simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    exact alg (ρ p.1) (w(0, s) p.2) (φ.val (p.1 * p.2⁻¹)) (kLine p)
  let A := A(hline, hs₀(hs), φ)
  let Q := spectralTruncatedConvolution (F := F) a hline hs₀(hs) hρ φ
  let G := geometricTruncatedConvolution (F := F) a hline hs₀(hs) hρ φ
  have hsum : M.comp A = G + Q := by
    exact truncatedConvolution_eq_geometric_add_spectral (F := F) a hline hs₀(hs) hρ φ
  have hconv := hardySobolevConvolution_eq_testAction μ𝔽 m𝔽 (-0) 0 s (hStrip(hline))
    hs₀(hs) φ hc.aemeasurable hb
  have hOp := congrArg (fun U : W(0, s) →L[ℂ] W(0, s) ↦ M.comp U) hconv
  exact subKernel ν hk hq he _ Q G hrow hQ (hOp.trans hsum)

/-- Paper: Definition 10.4.3.2, p. 470. The two line representatives are measurable. -/
theorem globalLineKernels_measurable :
    Measurable (kLine : C𝔽 × C𝔽 → ℂ) ∧ Measurable geomLine := by
  have hk : Measurable (kLine : C𝔽 × C𝔽 → ℂ) := (Lp.stronglyMeasurable kLine).measurable
  have hφ : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  exact ⟨hk, (hφ.comp (continuous_fst.mul continuous_snd.inv)).measurable.sub hk⟩

end LineRepresentatives

section StripTensors

/-- Paper: Theorem 10.4.3.5(1), p. 472. The canonical section of the strip
quotient sends the class of a lift to its orthogonal spectral projection.
Deviation: The identity is stated for any quotient vector. -/
theorem spectralStripKernel_orthogonalLift (_ha : 0 < a)
    (x : H(a, hα, hs₀(hs))) (v : W(α, s)) (_hv : Q(a, hα, hs₀(hs)) v = x) :
    S(a, hα, hs₀(hs)) x = Ps v := by
  subst x
  exact (spectralQuotient_orthogonalRepresentative (F := F) a hα hs₀(hs) _ha v).1

local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))
local notation "jet(" z ", " m ")" => ⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩
local notation "D" => spectralSobolevDualEmbedding F a (hStrip(hα)) hs₀(hs)

local notation "Bases(" χ ", " x ", " f ")" => (IsSpectralMarkushevichBasis x f ∧
  ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp
    (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
local notation "Order(" χ ", " e ")" => (∀ z z' : Z(χ), z.val.1 = z'.val.1 → (e z).2 ≤ (e z').2 →
  |z.val.2.2| ≤ |z'.val.2.2|)
local notation "rectangle(" χ ", " e ")" =>
  spectralKernelRectangle e (fun z ↦ N(χ, z)) (fun z m ↦ jet(z, m))

/-- Paper: Theorem 10.4.3.5(2), pp. 472–473, equation (10.4.3.42).
The quotient tensors converge in the completed projective tensor topology.
Deviation: The zero set is restricted to the strip, and its boundary and interior
multiplicities are those of §10.2. The directed set consists of finite rectangles. -/
theorem spectralStripQuotientKernel_tendsto (_ha : 0 < a)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (_hχ : IsSpectralBasepointChoice χ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (_horder : Order(χ, e)) (_hb : Bases(χ, x, f)) :
    ∃ K, Tendsto (rectangle(χ, e)
      (fun j ↦ (f j).comp (Aq(a, hα, hs₀(hs), φ))) x) atTop (𝓝 K) := by
  exact spectralLineQuotientKernel_tendsto_of_traceCauchy (Aq(a, hα, hs₀(hs), φ)) x f e _ _
    (spectralStripConvolution_traceCauchy (F := F) a χ _hχ hα hs φ eχ e _he x f _hb.1 _hb.2)

/-- Paper: Theorem 10.4.3.5(2), pp. 472–473, equation (10.4.3.43).
The printed ambient rectangles with convolution transposed onto the input
factor converge in the projective topology. Their outputs are spectral. -/
theorem spectralStripTransposedKernel_tendsto (_ha : 0 < a)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (_hχ : IsSpectralBasepointChoice χ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (_horder : Order(χ, e)) (_hb : Bases(χ, x, f)) :
    ∃ K : Π(W'(α, s), W(α, s)),
      Tendsto (rectangle(χ, e) (fun j ↦ D ((f j).comp (Aq(a, hα, hs₀(hs), φ))))
      (fun j ↦ S(a, hα, hs₀(hs)) (x j))) atTop (𝓝 K) := by
  have lift {Z J E G X Y : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]
      [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup X] [NormedSpace ℂ X]
      [NormedAddCommGroup Y] [NormedSpace ℂ Y]
      (d : E →L[ℂ] X) (j : G →L[ℂ] Y) (e : Z ↪ ℕ × ℕ) (N : Z → ℕ)
      (i : (z : Z) → Fin (N z) → J) (u : J → E) (v : J → G)
      (h : ∃ K, Tendsto (spectralKernelRectangle e N i u v) atTop (𝓝 K)) :
      ∃ K, Tendsto (spectralKernelRectangle e N i (fun z ↦ d (u z)) (fun z ↦ j (v z))) atTop (𝓝 K) := by
    let L : ProjectiveTensor E G →L[ℂ] ProjectiveTensor X Y :=
      ⟨projectiveTensorMap d.toLinearMap j.toLinearMap, projectiveTensorMap_continuous d j⟩
    obtain ⟨K, hK⟩ := h
    refine ⟨L.completion K, (L.completion.continuous.continuousAt.tendsto.comp hK).congr ?_⟩
    intro ij
    unfold Function.comp spectralKernelRectangle
    rw [ContinuousLinearMap.completion_apply_coe]
    apply congrArg ((↑) : ProjectiveTensor X Y → Π(X, Y))
    change projectiveTensorMap d.toLinearMap j.toLinearMap _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro z _
    exact (map_sum (TensorProduct.map d.toLinearMap j.toLinearMap)
      (fun m : Fin (N z) ↦ u (i z m) ⊗ₜ[ℂ] v (i z m)) Finset.univ).trans
      (Finset.sum_congr rfl fun m _ ↦ TensorProduct.map_tmul _ _ _ _)
  let E := H(a, hα, hs₀(hs))
  let θ := Θ(a, hα, hs₀(hs))
  let d : StrongDual ℂ E →L[ℂ] W'(α, s) := ⟨D,
    (spectralSobolevDualEmbedding_isometry_range (F := F) a (hStrip(hα)) hs₀(hs)).1.continuous⟩
  let j : E →L[ℂ] W(α, s) := θ.orthogonal.subtypeL.comp
    θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  exact lift d j e _ _ _ _ (spectralStripQuotientKernel_tendsto (F := F) a hα hs φ _ha χ eχ e x f _hχ _he _horder _hb)

-- TODO(paper-gap): The estimate at the end of §10.4.2 does not prove convergence
-- of the ambient net with convolution on the output factor. The quotient net
-- only controls the part of that net with spectral output.

section StripJetConvolution

/-- An integral that annihilates every lower jet also annihilates a translate of the jet. -/
private theorem integral_mul_translated_zeroJet_eq_zero
    (η : PontryaginDual C𝔽) (b t : ℝ) (m : ℕ) (v : C𝔽 → ℂ)
    (hv : ∀ i ≤ m, Integrable (fun x ↦ v x * spectralZeroJet η b t i x) μ𝔽 ∧
      ∫ x, v x * spectralZeroJet η b t i x ∂μ𝔽 = 0) (g : C𝔽) :
    ∫ y, v y * spectralZeroJet η b t m (g * y) ∂μ𝔽 = 0 := by
  let T := ideleClassNormTwist η ((b : ℂ) + (t : ℂ) * Complex.I)
  let L (y : C𝔽) : ℂ := logNorm y
  let c (i : ℕ) := T g * L g ^ (m - i) * (m.choose i : ℂ)
  have hlog (y : C𝔽) : L (g * y) = L y + L g := by
    dsimp only [L, logIdeleClassNorm]
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
      (NNReal.coe_ne_zero.2 (ideleClassNorm F y).ne_zero), Complex.ofReal_add, add_comm]
  have hs (y : C𝔽) : v y * spectralZeroJet η b t m (g * y) =
      ∑ i ∈ Finset.range (m + 1), c i * (v y * spectralZeroJet η b t i y) := by
    change v y * (T (g * y) * L (g * y) ^ m) = _
    rw [map_mul, hlog, add_pow]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change v y * (T g * T y * (L y ^ i * L g ^ (m - i) * (m.choose i : ℂ))) =
      (T g * L g ^ (m - i) * (m.choose i : ℂ)) * (v y * (T y * L y ^ i))
    ring
  simp_rw [hs]
  rw [integral_finsetSum _ fun i hi ↦ ((hv i (Finset.mem_range_succ_iff.mp hi)).1).const_mul (c i)]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [integral_const_mul, (hv i (Finset.mem_range_succ_iff.mp hi)).2, mul_zero]

local notation "raw(" χ ", " j ")" =>
  spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2

/-- A quotient jet functional evaluates on a representative by its explicit Haar moment. -/
private theorem spectralStripJet_eval_mkQ
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (j : SpectralStripJetIndex χ a α s) (f : StrongDual ℂ H(a, hα, hs₀(hs)))
    (hf : D f = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))) (v : W(α, s)) :
    Integrable (fun y ↦ v y * raw(χ, j) y) μ𝔽 ∧
      f (Q(a, hα, hs₀(hs)) v) = ∫ y, v y * raw(χ, j) y ∂μ𝔽 := by
  let w (g : C𝔽) := intervalSobolevDensity (-α) α s (logNorm g)
  have hw : Measurable w := by
    have hD : Continuous (intervalSobolevDensity (-α) α s) := by
      unfold intervalSobolevDensity
      fun_prop
    exact hD.measurable.comp ((NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable.log)
  have habs : μ𝔽 ≪ (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g)⁻¹) := by
    refine withDensity_absolutelyContinuous' hw.inv.ennreal_ofReal.aemeasurable (.of_forall fun g ↦ ?_)
    refine ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ?_)
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hae : (D f : C𝔽 → ℂ) =ᵐ[μ𝔽] raw(χ, j) := by
    rw [hf]
    exact habs.ae_le (MemLp.coeFn_toLp _)
  have he := spectralSobolevPairing_dual (hStrip(hα)) hs₀(hs) (f.comp (Q(a, hα, hs₀(hs)))) v
  change Integrable (fun y ↦ v y * D f y) μ𝔽 ∧
      f (Q(a, hα, hs₀(hs)) v) = ∫ y, v y * D f y ∂μ𝔽 at he
  have hEq := hae.mono fun y hy ↦ congrArg (v y * ·) hy
  exact ⟨he.1.congr hEq, he.2.trans (integral_congr_ae hEq)⟩


/-- Hardy translation preserves simultaneous vanishing of the lower Haar moments of a jet. -/
private theorem integral_hardy_translation_zeroJet_eq_zero
    (η : PontryaginDual C𝔽) (b t : ℝ) (m : ℕ) (v : W(α, s))
    (hv : ∀ i ≤ m, Integrable (fun x ↦ v x * spectralZeroJet η b t i x) μ𝔽 ∧
      ∫ x, v x * spectralZeroJet η b t i x ∂μ𝔽 = 0) (g : C𝔽) :
    let T := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs)
    ∫ y, T g v y * spectralZeroJet η b t m y ∂μ𝔽 = 0 := by
  let J := spectralZeroJet η b t m
  let H (y : C𝔽) := v (g⁻¹ * y) * J y
  intro T
  calc
    _ = ∫ y, H y ∂μ𝔽 := integral_congr_ae
      ((hardySobolevTranslation_apply μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs) g v).mono
        fun y hy ↦ congrArg (· * J y) hy)
    _ = ∫ y, H (g * y) ∂μ𝔽 := (integral_mul_left_eq_self H g).symm
    _ = ∫ y, v y * J (g * y) ∂μ𝔽 := by simp only [H, inv_mul_cancel_left]
    _ = 0 := integral_mul_translated_zeroJet_eq_zero η b t m v hv g

local notation "J(" χ ")" => SpectralStripJetIndex (F := F) χ a α s

/-- A strip zero's entire finite jet block annihilates convolution of a basis vector
belonging to a different zero. -/
private theorem spectralStripConvolution_offBlock
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → H(a, hα, hs₀(hs))) (f : J(χ) → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x f)
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽) {z z' : Z(χ)} (hne : z ≠ z')
    (m : Fin (N(χ, z))) (n : Fin (N(χ, z'))) :
    f (jet(z, m)) (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ (x (jet(z', n)))) = 0 := by
  let θ := globalThetaSobolev F a (hStrip(hα)) hs₀(hs)
  obtain ⟨v, hv⟩ := θ.mkQ_surjective (x (jet(z', n)))
  have heval (j : J(χ)) (w : W(α, s)) := spectralStripJet_eval_mkQ (a := a) hα hs χ j (f j) (hj j) w
  have hmoment (i : ℕ) (hi : i ≤ m.val) :
      Integrable (fun y ↦ v y * spectralZeroJet (χ z.val.1) z.val.2.1 z.val.2.2 i y) μ𝔽 ∧
        ∫ y, v y * spectralZeroJet (χ z.val.1) z.val.2.1 z.val.2.2 i y ∂μ𝔽 = 0 := by
    let k : Fin (N(χ, z)) := ⟨i, hi.trans_lt m.isLt⟩
    have hne' : (jet(z', n) : J(χ)) ≠ jet(z, k) := by
      intro h
      apply hne
      exact Subtype.ext (congrArg (fun u : J(χ) ↦ (u.val.1, u.val.2.1, u.val.2.2.1)) h).symm
    refine ⟨(heval (jet(z, k)) v).1, (heval (jet(z, k)) v).2.symm.trans ?_⟩
    change f (jet(z, k)) (θ.mkQ v) = 0
    rw [hv]
    exact hb.2.1 _ _ hne'
  let j : J(χ) := jet(z, m)
  let T := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs)
  let ℓ := (f j).comp θ.mkQL
  have hT (g : C𝔽) : ℓ (T g v) = 0 := (heval j (T g v)).2.trans
    (integral_hardy_translation_zeroJet_eq_zero hα hs (χ z.val.1) z.val.2.1 z.val.2.2 m.val v hmoment g)
  have hP := bruhatRegularizedAction_apply μ𝔽 T
    (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs)).choose_spec.2 φ v
  have he := congrArg (fun p : PettisWeakCompletion W(α, s) ↦
    (show Module.Dual ℂ (StrongDual ℂ W(α, s)) from p) ℓ) hP.2
  change ℓ (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs) φ v) =
    ∫ g, ℓ (φ.val g • T g v) ∂μ𝔽 at he
  rw [← hv, spectralConvolution_mkQ]
  refine he.trans (integral_eq_zero_of_ae (.of_forall fun g ↦ ?_))
  change ℓ (φ.val g • T g v) = (0 : ℂ)
  exact (map_smul ℓ _ _).trans ((congrArg (φ.val g • ·) (hT g)).trans (smul_zero _))

end StripJetConvolution

section AmbientKernelRectangles

/-- A block-diagonal operator commutes with every finite sum of whole coordinate-block projections. -/
private theorem spectralStripAmbientKernel_tendsto_blocks {E J Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : J → E) (f : J → StrongDual ℂ E) (hb : IsSpectralMarkushevichBasis x f)
    (N : Z → ℕ) (j : (z : Z) → Fin (N z) → J)
    (hj : Bijective (fun p : (z : Z) × Fin (N z) ↦ j p.1 p.2))
    (op : E →L[ℂ] E)
    (hcross : ∀ z z', z ≠ z' → ∀ m n, f (j z m) (op (x (j z' n))) = 0)
    (K : Finset Z) (u : E) :
    (∑ z ∈ K, ∑ m, f (j z m) u • op (x (j z m))) =
      ∑ z ∈ K, ∑ m, f (j z m) (op u) • x (j z m) := by
  classical
  have same (z : Z) (m n : Fin (N z)) :
      f (j z m) (x (j z n)) = if n = m then 1 else 0 := by
    split_ifs with h
    · subst n
      exact hb.1 _
    · apply hb.2.1
      intro e
      exact h (eq_of_heq (Sigma.mk.inj (hj.1 e)).2)
  have other {z z' : Z} (h : z ≠ z') (m : Fin (N z)) (n : Fin (N z')) :
      f (j z m) (x (j z' n)) = 0 := by
    apply hb.2.1
    intro e
    exact h (congrArg Sigma.fst (hj.1 (a₁ := ⟨z', n⟩) (a₂ := ⟨z, m⟩) e)).symm
  have separate {v w : E} (h : ∀ i, f i v = f i w) : v = w := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    have he : ContinuousLinearMap.apply ℂ ℂ v = ContinuousLinearMap.apply ℂ ℂ w := by
      apply ContinuousLinearMap.ext_on hb.2.2.2
      rintro _ ⟨i, rfl⟩
      exact h i
    exact fun ℓ ↦ DFunLike.congr_fun he ℓ
  apply Finset.sum_congr rfl
  intro z _
  let P : E →L[ℂ] E := ∑ m : Fin (N z), (f (j z m)).smulRight (x (j z m))
  have vec (z' : Z) (n : Fin (N z')) :
      P (x (j z' n)) = if z' = z then x (j z' n) else 0 := by
    by_cases h : z' = z
    · subst z'
      simp [P, same, ite_smul]
    · simp [P, other (Ne.symm h), h]
  have coord (z' : Z) (n : Fin (N z')) (v : E) :
      f (j z' n) (P v) = if z' = z then f (j z' n) v else 0 := by
    by_cases h : z' = z
    · subst z'
      simp [P, map_sum, same, smul_eq_mul, mul_ite]
    · simp [P, map_sum, other h, h]
  have comm : op.comp P = P.comp op := by
    apply ContinuousLinearMap.ext_on hb.2.2.1
    rintro _ ⟨i, rfl⟩
    obtain ⟨⟨z', n⟩, rfl⟩ := hj.2 i
    apply separate
    intro k
    obtain ⟨⟨z'', m⟩, rfl⟩ := hj.2 k
    change f (j z'' m) (op (P (x (j z' n)))) = f (j z'' m) (P (op (x (j z' n))))
    rw [vec, coord]
    by_cases hi : z' = z <;> by_cases ho : z'' = z
    · simp [hi, ho]
    · subst z'
      simp [ho, hcross _ _ ho]
    · subst z''
      simp [hi, hcross _ _ (Ne.symm hi)]
    · simp [hi, ho]
  simpa [P, map_sum] using DFunLike.congr_fun comm u

/-- Splitting each output vector splits the rectangular kernel tensor. -/
private theorem spectralStripAmbientKernel_tendsto_add {Z J X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (j : (z : Z) → Fin (N z) → J)
    (u : J → X) (v w : J → Y) (ij : ℕ × ℕ) :
    spectralKernelRectangle e N j u (fun k ↦ v k + w k) ij =
      spectralKernelRectangle e N j u v ij + spectralKernelRectangle e N j u w ij := by
  classical
  unfold spectralKernelRectangle
  rw [← Completion.coe_add]
  apply congrArg ((↑) : ProjectiveTensor X Y → Π(X, Y))
  let K := ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
  change (∑ z ∈ K, ∑ m, u (j z m) ⊗ₜ[ℂ] (v (j z m) + w (j z m)) : X ⊗[ℂ] Y) =
    (∑ z ∈ K, ∑ m, u (j z m) ⊗ₜ[ℂ] v (j z m)) + ∑ z ∈ K, ∑ m, u (j z m) ⊗ₜ[ℂ] w (j z m)
  simp only [TensorProduct.tmul_add, Finset.sum_add_distrib]

/-- If convolution commutes with each finite block projection, lifting and transposing
it give the same rectangular spectral tensor. -/
private theorem spectralStripAmbientKernel_tendsto_swap {Z J : Type*} {α s : ℝ}
    (a : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (j : (z : Z) → Fin (N z) → J)
    (x : J → H(a, hα, hs)) (f : J → StrongDual ℂ H(a, hα, hs))
    (T : H(a, hα, hs) →L[ℂ] H(a, hα, hs)) (lift : H(a, hα, hs) →L[ℂ] W(α, s))
    (hcomm : ∀ (K : Finset Z) (v : H(a, hα, hs)),
      (∑ z ∈ K, ∑ m, f (j z m) v • T (x (j z m))) =
        ∑ z ∈ K, ∑ m, f (j z m) (T v) • x (j z m)) (ij : ℕ × ℕ) :
    spectralKernelRectangle e N j (fun i ↦ spectralSobolevDualEmbedding F a (hStrip(hα)) hs (f i))
        (fun i ↦ lift (T (x i))) ij =
      spectralKernelRectangle e N j
        (fun i ↦ spectralSobolevDualEmbedding F a (hStrip(hα)) hs ((f i).comp T))
        (fun i ↦ lift (x i)) ij := by
  apply sobolevProjectiveKernelOperator_injective (F := F) hα hs
  apply ContinuousLinearMap.ext
  intro v
  have h₁ := spectralLineAmbientKernel_operator_eval (F := F) a hα hs e N j f
    (fun i ↦ lift (T (x i))) ij v
  have h₂ := spectralLineAmbientKernel_operator_eval (F := F) a hα hs e N j
    (fun i ↦ (f i).comp T) (fun i ↦ lift (x i)) ij v
  refine h₁.trans (Eq.trans ?_ h₂.symm)
  let K := ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
  simpa only [map_sum, map_smul, ContinuousLinearMap.comp_apply] using
    congrArg lift (hcomm K (Q(a, hα, hs) v))

/-- A Cauchy geometric part and a convergent spectral part give the limit of their sum. -/
private theorem spectralStripAmbientKernel_tendsto_of_parts {I V : Type*} [AddCommGroup V]
    [UniformSpace V] [IsUniformAddGroup V] [CompleteSpace V] {l : Filter I} [NeBot l]
    {g p t : I → V} (hg : Cauchy (Filter.map g l)) (hp : ∃ v, Tendsto p l (𝓝 v))
    (ht : ∀ i, g i + p i = t i) : ∃ v, Tendsto t l (𝓝 v) := by
  obtain ⟨u, hu⟩ := cauchy_map_iff_exists_tendsto.mp hg
  obtain ⟨v, hv⟩ := hp
  exact ⟨u + v, (hu.add hv).congr ht⟩

end AmbientKernelRectangles

/-- Paper: Theorem 10.4.3.5(2), pp. 472–473, equation (10.4.3.43).
The ambient rectangles for convolution after spectral projection converge.
Deviation: Convolution acts on the lifted output vector. The printed
transposed input factor gives projection after convolution, as in (10.4.3.14).
The geometric-output components are assumed Cauchy in the projective topology.
Section 10.3 supplies the spectral components after grouping all jets of each zero. -/
theorem spectralStripAmbientKernel_tendsto (_ha : 0 < a)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (_hχ : IsSpectralBasepointChoice χ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (_horder : Order(χ, e)) (_hb : Bases(χ, x, f))
    (_hgeom : Cauchy (Filter.map (rectangle(χ, e) (fun j ↦ D (f j))
      (fun j ↦ Pg (B (S(a, hα, hs₀(hs)) (x j))))) atTop)) :
    ∃ K, Tendsto (rectangle(χ, e) (fun j ↦ D (f j))
      (fun j ↦ B (S(a, hα, hs₀(hs)) (x j)))) atTop (𝓝 K) := by
  let θ := Θ(a, hα, hs₀(hs))
  let lift := θ.orthogonal.subtypeL.comp θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  let T := Aq(a, hα, hs₀(hs), φ)
  have hsection (u) : θ.mkQL (lift u) = u :=
    (θ.quotientEquivOrthogonal_symm_eq_mk _ (θ.quotientEquivOrthogonal u).property).symm.trans
      (θ.quotientEquivOrthogonal.symm_apply_apply u)
  have hsplit (u : H(a, hα, hs₀(hs))) : Pg (B (lift u)) + lift (T u) = B (lift u) := by
    have hp := DFunLike.congr_fun (spectralProjection_convolution_factor (F := F) a hα hs₀(hs) φ) (lift u)
    change Ps (B (lift u)) = lift (T (θ.mkQL (lift u))) at hp
    rw [hsection] at hp
    exact (congrArg (Pg (B (lift u)) + ·) hp.symm).trans (θ.starProjection_add_starProjection_orthogonal _)
  let key (z : Z(χ)) (m : Fin N(χ, z)) : SpectralStripJetIndex χ a α s := jet(z, m)
  let index : ((z : Z(χ)) × Fin N(χ, z)) ≃ SpectralStripJetIndex χ a α s :=
    ⟨fun p ↦ key p.1 p.2,
      fun j ↦ ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩,
        ⟨j.val.2.2.2, j.property⟩⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hcross (z z' : Z(χ)) (hne : z ≠ z') (m : Fin N(χ, z)) (n : Fin N(χ, z')) :
      f (key z m) (T (x (key z' n))) = 0 :=
    spectralStripConvolution_offBlock a hα hs χ x f _hb.1 _hb.2 φ hne m n
  have hcomm := spectralStripAmbientKernel_tendsto_blocks x f _hb.1 (fun z : Z(χ) ↦ N(χ, z)) key
    index.bijective T hcross
  refine spectralStripAmbientKernel_tendsto_of_parts (I := ℕ × ℕ) (V := Π(W'(α, s), W(α, s)))
    (l := atTop)
    (g := spectralKernelRectangle e _ key (fun i ↦ D (f i)) (fun i ↦ Pg (B (lift (x i)))))
    (p := spectralKernelRectangle e _ key (fun i ↦ D ((f i).comp T)) (fun i ↦ lift (x i)))
    (t := spectralKernelRectangle e _ key (fun i ↦ D (f i)) (fun i ↦ B (lift (x i)))) _hgeom
    (spectralStripTransposedKernel_tendsto (F := F) a hα hs φ _ha χ eχ e x f
      _hχ _he _horder _hb) ?_
  intro ij
  let geom (i) := Pg (B (lift (x i)))
  let spec (i) := lift (T (x i))
  change spectralKernelRectangle e _ key (fun i ↦ D (f i)) geom ij +
      spectralKernelRectangle e _ key (fun i ↦ D ((f i).comp T)) (fun i ↦ lift (x i)) ij = _
  have hswap := spectralStripAmbientKernel_tendsto_swap (F := F) a hα hs₀(hs) e
    (fun z : Z(χ) ↦ N(χ, z)) key x f T lift hcomm ij
  have hadd := spectralStripAmbientKernel_tendsto_add e (fun z : Z(χ) ↦ N(χ, z)) key
    (fun i ↦ D (f i)) geom spec ij
  have hfinal := congrArg (fun outputs ↦ spectralKernelRectangle e (fun z : Z(χ) ↦ N(χ, z)) key
    (fun i ↦ D (f i)) outputs ij) (funext fun i ↦ hsplit (x i))
  exact (congrArg (spectralKernelRectangle e _ key (fun i ↦ D (f i)) geom ij + ·)
    hswap.symm).trans (hadd.symm.trans hfinal)

/-- On a lifted basis vector biorthogonality makes the rectangular net eventually constant.
The rectangle only uses the quotient of its input, so this determines the operator everywhere. -/
private theorem spectralStripAmbientKernel_operator_limit {Z J H V : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (q : V →L[ℂ] H) (S : H →L[ℂ] V) (hq : ∀ u, q (S u) = u) (A T : V →L[ℂ] V)
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (j : (z : Z) → Fin (N z) → J)
    (hj : Bijective (fun p : (z : Z) × Fin (N z) ↦ j p.1 p.2))
    (x : J → H) (f : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x f)
    (h : ∀ v, Tendsto (fun ij : ℕ × ℕ ↦
      ∑ z ∈ ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn,
        ∑ m : Fin (N z), f (j z m) (q v) • A (S (x (j z m)))) atTop (𝓝 (T v))) :
    ∀ v, T v = A (S (q v)) := by
  have hlift : T.comp S = A.comp S := by
    apply ContinuousLinearMap.ext_on hb.2.2.1
    rintro _ ⟨i, rfl⟩
    apply tendsto_nhds_unique (h (S (x i)))
    apply tendsto_const_nhds.congr'
    have hc := spectralLineAmbientKernel_operator_single e N j hj i
      (fun k ↦ f k (x i) • A (S (x k))) (fun k hk ↦ by rw [hb.2.1 i k hk.symm, zero_smul])
    filter_upwards [hc] with ij hij
    simpa only [hq, hb.1, one_smul, ContinuousLinearMap.comp_apply] using hij.symm
  intro v
  have hv := h (S (q v))
  simp only [hq] at hv
  exact (tendsto_nhds_unique (h v) hv).trans (DFunLike.congr_fun hlift (q v))

/-- Paper: Theorem 10.4.3.5(3), p. 473. The ambient limit represents
convolution after spectral projection.
Deviation: The limit is taken in the ambient space of (10.4.3.43), with
convolution on the output factor as required by this operator order.
Equation (10.4.3.42) gives a limit in the quotient tensor space. -/
theorem spectralStripAmbientKernel_operator (_ha : 0 < a)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (_hχ : IsSpectralBasepointChoice χ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (_horder : Order(χ, e)) (_hb : Bases(χ, x, f)) (K : Π(W'(α, s), W(α, s)))
    (_hK : Tendsto (rectangle(χ, e) (fun j ↦ D (f j))
      (fun j ↦ B (S(a, hα, hs₀(hs)) (x j)))) atTop (𝓝 K)) :
    sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K = Bpre := by
  let θ := Θ(a, hα, hs₀(hs))
  let lift := θ.orthogonal.subtypeL.comp θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hsection (u) : θ.mkQL (lift u) = u :=
    (θ.quotientEquivOrthogonal_symm_eq_mk _ (θ.quotientEquivOrthogonal u).property).symm.trans
      (θ.quotientEquivOrthogonal.symm_apply_apply u)
  let key (z : Z(χ)) (m : Fin N(χ, z)) : SpectralStripJetIndex χ a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let index : ((z : Z(χ)) × Fin N(χ, z)) ≃ SpectralStripJetIndex χ a α s :=
    ⟨fun p ↦ key p.1 p.2,
      fun j ↦ ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩,
        ⟨j.val.2.2.2, j.property⟩⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let T := sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K
  have h := spectralStripAmbientKernel_operator_limit θ.mkQL lift hsection B T e
    (fun z ↦ N(χ, z)) key index.bijective x f _hb.1 (fun v ↦ by
      let ev := (ContinuousLinearMap.apply ℂ (W(α, s)) v).comp
        (sobolevProjectiveKernelOperator (F := F) hα hs₀(hs))
      refine ((ev.continuous.tendsto K).comp _hK).congr fun ij ↦ ?_
      exact spectralLineAmbientKernel_operator_eval a hα hs₀(hs) e (fun z ↦ N(χ, z)) key f
        (fun j ↦ B (lift (x j))) ij v)
  apply ContinuousLinearMap.ext
  intro v
  exact (h v).trans (congrArg B (spectralStripKernel_orthogonalLift (F := F) a hα hs _ha _ v rfl))

end StripTensors

/-- Paper: Definition 10.4.3.7(1), p. 473. The global strip kernel comes
from the projective tensor of convolution after projection.
Deviation: Require existence of a tensor for this specific operator. This
permits any real twist and avoids assuming the missing geometric-block estimate. -/
def globalStripSpectralKernel
    (hK : ∃ K, sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K = Bpre) : L²mixed :=
  sobolevProjectiveKernelClass hα hs₀(hs) hK.choose

local notation "stripTensorExists" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K = Bpre)
local notation "kStrip(" h ")" => globalStripSpectralKernel (F := F) a hα hs φ h

/-- Paper: (10.4.3.45) and Definition 10.4.3.7, p. 473. Haar integration
against the strip kernel gives convolution after projection. -/
theorem spectralStripKernel_apply (hK : stripTensorExists) : kernelFor(kStrip(hK), Bpre) := by
  rw [← hK.choose_spec]
  exact (sobolevProjectiveKernelClass_spec hα hs₀(hs) hK.choose _).2 rfl

/-- Paper: Definition 10.4.3.7(2), pp. 473–474. Subtract the spectral kernel of
the given strip restriction from the Haar convolution kernel of the same test. -/
def globalStripGeometricKernel (hK : stripTensorExists) (p : C𝔽 × C𝔽) : ℂ :=
  φ.val (p.1 * p.2⁻¹) - kStrip(hK) p

local notation "geomStrip(" h ")" => globalStripGeometricKernel (F := F) a hα hs φ h

/-- Paper: Theorem 10.4.3.6(1), p. 473. On the strip theta subspace,
convolution agrees with geometric projection followed by convolution and
with the Haar integral against the global geometric kernel.
Deviation: Use the weight of the actual interval [−α, α]. -/
theorem geometricStripKernel_apply (_ha : 0 < a)
    (hK : stripTensorExists) (u : W(α, s)) (_hu : u ∈ Θ(a, hα, hs₀(hs))) :
    ∀ᵐ x ∂μ𝔽, Integrable (fun y ↦ geomStrip(hK) (x, y) * u y) μ𝔽 ∧
      B u x = ((B).comp Pg) u x ∧
      B u x = ∫ y, geomStrip(hK) (x, y) * u y ∂μ𝔽 := by
  have hgeom : Pg u = u := geometricProjection_apply_of_mem (F := F) a hα hs₀(hs) _hu
  have hspec : Ps u = 0 := Submodule.starProjection_orthogonal_apply_eq_zero _hu
  have hk := spectralStripKernel_apply (F := F) a hα hs φ hK u
  let row (v : W(α, s)) := ∀ᵐ x ∂μ𝔽, Integrable (fun y ↦ kStrip(hK) (x, y) * u y) μ𝔽 ∧
    v x = ∫ y, kStrip(hK) (x, y) * u y ∂μ𝔽
  have hB0 : Bpre u = 0 := by
    change B (Ps u) = 0
    rw [hspec, map_zero]
  have hk₀ : row 0 := Eq.mp (congrArg row hB0) hk
  let haarRows := geometricLineKernel_apply_rows (G := C𝔽) μ𝔽 m𝔽 (-α) α s
    (hStrip(hα)) hs₀(hs) φ
  have hrows := haarRows u (kStrip(hK) : C𝔽 × C𝔽 → ℂ) hk₀
  have heq : B u = ((B).comp Pg) u := by
    change B u = B (Pg u)
    rw [hgeom]
  exact hrows.mono fun x hx ↦ ⟨hx.1, congrArg (fun v : W(α, s) ↦ v x) heq, hx.2⟩

section MixedWeightKernel

open scoped ENNReal NNReal

/-- Normalize the mixed Sobolev kernel which realizes an operator by Haar integration. -/
private theorem spectralStripKernel_hilbertSchmidt_of_rows {α s : ℝ}
    (op : W(α, s) →L[ℂ] W(α, s))
    (k : Lp ℂ 2 ((ν(α, s)).prod (ν'(α, s))))
    (hrow : ∀ u : W(α, s), ∀ᵐ x ∂μ𝔽, op u x = ∫ y, k (x, y) * u y ∂μ𝔽) :
    IsSobolevHilbertSchmidtKernel (F := F) op
      (fun p : C𝔽 × C𝔽 ↦ ((w(α, s) p.2)⁻¹ : ℝ) • k p) := by
  let ν := ν(α, s)
  let wi (y : C𝔽) := w(α, s) y
  have hp (y : C𝔽) : 0 < wi y := intervalSobolevDensity_pos' _ _ _ _
  let wNN (y : C𝔽) : ℝ≥0 := ⟨wi y, (hp y).le⟩
  have hcont : Continuous wi :=
    (continuous_intervalSobolevDensity (-α) α s).comp (continuous_logModule' m𝔽)
  have hw : Continuous wNN := hcont.subtype_mk _
  have hν : ν = (μ𝔽).withDensity (fun y ↦ (wNN y : ENNReal)) :=
    congrArg (μ𝔽).withDensity (funext fun y ↦ ENNReal.ofReal_eq_coe_nnreal (hp y).le)
  have hν' : ν'(α, s) = (μ𝔽).withDensity (fun y ↦ (((wNN y)⁻¹ : ℝ≥0) : ENNReal)) := by
    apply congrArg (μ𝔽).withDensity
    funext y
    exact ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr (hp y).le)
  have hk : MemLp (k : C𝔽 × C𝔽 → ℂ) 2 (ν.prod ((μ𝔽).withDensity fun y ↦ ↑((wNN y)⁻¹))) :=
    (congrArg (fun η : Measure C𝔽 ↦ MemLp (k : C𝔽 × C𝔽 → ℂ) 2 (ν.prod η)) hν').mp (Lp.memLp k)
  exact spectralStripKernel_hilbertSchmidt_operator μ𝔽 ν wNN hw.measurable hp hν op k
    (Lp.stronglyMeasurable k) hk hrow

end MixedWeightKernel

/-- Paper: Theorem 10.4.3.6(2), p. 473, first formula. Dividing the global spectral
kernel by the input weight gives the Hilbert-Schmidt representative of convolution
after spectral projection.
Deviation: The exponent endpoints are −α and α, as in §9.2. -/
theorem spectralStripKernel_hilbertSchmidt (_ha : 0 < a)
    (hK : stripTensorExists) :
    IsSobolevHilbertSchmidtKernel (F := F) Bpre (weighted(kStrip(hK))) := by
  have hrow := spectralStripKernel_apply (F := F) a hα hs φ hK
  exact spectralStripKernel_hilbertSchmidt_of_rows (F := F) Bpre (kStrip(hK))
    (fun u ↦ (hrow u).mono fun _ hx ↦ hx.2)

/-- Paper: Theorem 10.4.3.6(2), p. 473, second formula. Output multiplication
gives the Hilbert-Schmidt representative of the strip spectral restriction.
Deviation: The target uses the spectral projector, in agreement with the
kernel in (10.4.3.47). The cutoff is real-valued as in §9.3. -/
theorem spectralStripRestrictionKernel_hilbertSchmidt (_ha : 0 < a)
    (hρ : hcut) (_hband : innerBand) (hK : stripTensorExists) :
    IsSobolevHilbertSchmidtKernel (F := F) (spectralRestriction (F := F) a hα hs₀(hs) hρ φ)
      (cut(weighted(kStrip(hK)))) := by
  have mulKernel {X : Type _} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
      [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
      (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν] [SFinite ν]
      (r : X → ℝ) (hm : Measurable r) (hr : ∀ x, |r x| ≤ 1)
      (M : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (hM : ∀ f : Lp ℂ 2 ν,
        (M f : X → ℂ) =ᵐ[ν] fun x ↦ (r x : ℂ) * f x)
      {k : X × X → ℂ} (hk : MemLp k 2 (ν.prod ν)) :
      ∃ ha : MemLp (fun p : X × X ↦ r p.1 • k p) 2 (ν.prod ν),
        (integralKernelOperator ν (ha.toLp _)).val = M.comp (integralKernelOperator ν (hk.toLp k)).val := by
    have hb : MemLp (fun p : X × X ↦ r p.1) ⊤ (ν.prod ν) :=
      memLp_top_of_bound (hm.comp measurable_fst).aestronglyMeasurable 1
        (.of_forall fun p ↦ hr p.1)
    have ha : MemLp (fun p : X × X ↦ r p.1 • k p) 2 (ν.prod ν) := hb.smul hk
    refine ⟨ha, ?_⟩
    ext1 f
    apply Lp.ext
    filter_upwards [integralKernelOperator_apply ν (ha.toLp _) f,
      integralKernelOperator_apply ν (hk.toLp _) f, Measure.ae_ae_of_ae_prod ha.coeFn_toLp,
      Measure.ae_ae_of_ae_prod hk.coeFn_toLp, hM ((integralKernelOperator ν (hk.toLp _)).val f)]
      with x hx hx' hax hkx hmx
    change (integralKernelOperator ν (ha.toLp _)).val f x =
      M ((integralKernelOperator ν (hk.toLp _)).val f) x
    rw [hx.2, hmx, hx'.2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hax, hkx] with y ha' hk'
    rw [ha', hk']
    exact mul_assoc (r x : ℂ) (k (x, y)) (f y)
  obtain ⟨hk, hB⟩ := spectralStripKernel_hilbertSchmidt (F := F) a hα hs φ _ha hK
  let ν := ν(α, s)
  let M := modulatedCutoffOperator m𝔽 ν hρ
  obtain ⟨hg, he⟩ := mulKernel ν ρ hρ.measurable hρ.abs_le_one M (modulatedCutoffOperator_apply m𝔽 ν hρ) hk
  exact ⟨hg, he.trans (congrArg (fun U : W(α, s) →L[ℂ] W(α, s) ↦ M.comp U) hB)⟩

/-- Paper: Theorem 10.4.3.6(3), p. 473. The cutoff geometric kernel,
divided by the input weight, is the Hilbert-Schmidt representative of
the geometric restriction on the strip. -/
theorem geometricStripRestrictionKernel_hilbertSchmidt (_ha : 0 < a)
    (hρ : hcut) (_hband : innerBand) (hK : stripTensorExists) :
    IsSobolevHilbertSchmidtKernel (F := F) (geometricRestriction (F := F) a hα hs₀(hs) hρ φ)
      (cut(weighted(geomStrip(hK)))) := by
  have subKernel {X : Type _} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
      [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
      (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν] [SFinite ν]
      {k q g : X × X → ℂ} (hk : MemLp k 2 (ν.prod ν)) (hq : MemLp q 2 (ν.prod ν))
      (he : ∀ p, k p - q p = g p) (T Q G : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
      (ht : ∀ u : Lp ℂ 2 ν, ∀ᵐ x ∂ν, Integrable (fun y ↦ k (x,y) * u y) ν ∧
        T u x = ∫ y, k (x,y) * u y ∂ν)
      (hQ : (integralKernelOperator ν (hq.toLp q)).val = Q) (hsum : T = G + Q) :
      ∃ hg : MemLp g 2 (ν.prod ν), (integralKernelOperator ν (hg.toLp g)).val = G := by
    have hg : MemLp g 2 (ν.prod ν) := (hk.sub hq).ae_eq (.of_forall he)
    refine ⟨hg, ?_⟩
    ext1 u
    apply Lp.ext
    have hqs := integralKernelOperator_apply ν (hq.toLp q) u
    rw [hQ] at hqs
    have hd : (G u : X → ℂ) =ᵐ[ν] fun x ↦ T u x - Q u x := by
      rw [eq_sub_of_add_eq hsum.symm]
      exact Lp.coeFn_sub _ _
    filter_upwards [integralKernelOperator_apply ν (hg.toLp g) u, ht u, hqs, hd,
      Measure.ae_ae_of_ae_prod hg.coeFn_toLp, Measure.ae_ae_of_ae_prod hq.coeFn_toLp]
      with x hx ht' hqs' hd' hGx hQx
    rw [hx.2, hd', ht'.2, hqs'.2, ← integral_sub ht'.1 hqs'.1]
    apply integral_congr_ae
    filter_upwards [hGx, hQx] with y hy hz
    rw [hy, hz, ← he, sub_mul]
  let ν := ν(α, s)
  let M := modulatedCutoffOperator m𝔽 ν hρ
  let k : C𝔽 × C𝔽 → ℂ := fun p ↦ (ρ p.1 : ℂ) * φ.val (p.1 * p.2⁻¹) / (w(α, s) p.2 : ℂ)
  let q := cut(weighted(kStrip(hK)))
  let g := cut(weighted(geomStrip(hK)))
  have hφs := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsur : Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hk, hrow⟩ := truncatedHardySobolevConvolution_hilbertSchmidt μ𝔽 m𝔽 (-α) α s
    (hStrip(hα)) hs₀(hs) φ.val hc.aemeasurable φ.property.2 hb hm hsur hρ _hband
  obtain ⟨hq, hQ⟩ := spectralStripRestrictionKernel_hilbertSchmidt (F := F) a hα hs φ _ha hρ _hband hK
  have he (p : C𝔽 × C𝔽) : k p - q p = g p := by
    have alg (r w : ℝ) (z t : ℂ) :
        (r : ℂ) * z / (w : ℂ) - r • (w⁻¹ • t) = r • (w⁻¹ • (z - t)) := by
      simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    exact alg (ρ p.1) (w(α, s) p.2) (φ.val (p.1 * p.2⁻¹)) (kStrip(hK) p)
  let A := A(hα, hs₀(hs), φ)
  let Q := spectralRestriction (F := F) a hα hs₀(hs) hρ φ
  let G := geometricRestriction (F := F) a hα hs₀(hs) hρ φ
  have hsum : M.comp A = G + Q := by
    ext1 u
    change M (A u) = M (A (Pg u)) + M (A (Ps u))
    rw [← map_add, ← map_add]
    exact congrArg (fun v ↦ M (A v)) ((Θ(a, hα, hs₀(hs))).starProjection_add_starProjection_orthogonal u).symm
  have hconv := hardySobolevConvolution_eq_testAction μ𝔽 m𝔽 (-α) α s (hStrip(hα))
    hs₀(hs) φ hc.aemeasurable hb
  have hOp := congrArg (fun U : W(α, s) →L[ℂ] W(α, s) ↦ M.comp U) hconv
  exact subKernel ν hk hq he _ Q G hrow hQ (hOp.trans hsum)

/-- Paper: Definition 10.4.3.7, pp. 473–474. The two strip representatives are measurable. -/
theorem globalStripKernels_measurable (hK : stripTensorExists) :
    Measurable (kStrip(hK) : C𝔽 × C𝔽 → ℂ) ∧ Measurable geomStrip(hK) := by
  have hk : Measurable (kStrip(hK) : C𝔽 × C𝔽 → ℂ) := (Lp.stronglyMeasurable _).measurable
  refine ⟨hk, ?_⟩
  have hc : Continuous φ.val :=
    continuous_schwartzBruhat
      (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  unfold globalStripGeometricKernel
  exact (hc.measurable.comp (measurable_fst.mul measurable_snd.inv)).sub hk

end MeasurableKernels

end RiemannMasullo
