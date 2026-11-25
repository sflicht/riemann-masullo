module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
public import RiemannMasullo.Ch09_HardySobolev.Sec3
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.External.FermatDixmierMalliavin.OneParameter

import all RiemannMasullo.Ch09_HardySobolev.Sec3

/-!
# Spectral nuclearity

Masullo, §10.3, pp. 447–455. Convolution acts on the spectral Sobolev quotients
from §10.2. The trace formulas use the strict boundary multiplicity from that
section and the integrated left-translation action from §9.3.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

section StrongNuclearity

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- Paper: §10.3, p. 447. A strongly nuclear operator is an operator-norm sum
of rank-one terms with unit-ball vectors and functionals and rapidly decreasing
coefficients.
Deviation: The name is kept apart from `IsStronglyNuclearOperator` of §7.4
(Theorem 7.4.1.1(2), pp. 366–367), which is stated for endomorphisms of a locally
convex space through a nuclear presentation. This one is for maps between normed spaces. -/
def IsStronglyNuclearBanachOperator (A : E →L[ℂ] G) : Prop :=
  ∃ (c : ℕ → ℂ) (Λ : ℕ → StrongDual ℂ E) (y : ℕ → G),
    (∀ n, ‖Λ n‖ ≤ 1 ∧ ‖y n‖ ≤ 1) ∧
    (∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℂ) ^ k * c n) atTop (𝓝 0)) ∧
    HasSum (fun n ↦ c n • (Λ n).smulRight (y n)) A

/-- Paper: §10.3, p. 447. A rank-one operator has a strongly nuclear expansion
using a single coefficient after normalizing the factors.
Deviation: Sanity check for the strongly nuclear condition. -/
theorem isStronglyNuclearBanachOperator_smulRight (Λ : StrongDual ℂ E) (y : G) :
    IsStronglyNuclearBanachOperator (Λ.smulRight y) := by
  classical
  refine ⟨fun n ↦ if n = 0 then ((‖Λ‖ * ‖y‖ : ℝ) : ℂ) else 0,
    fun n ↦ if n = 0 then ((‖Λ‖⁻¹ : ℝ) : ℂ) • Λ else 0,
    fun n ↦ if n = 0 then ((‖y‖⁻¹ : ℝ) : ℂ) • y else 0, ?_, ?_, ?_⟩
  · intro n
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true, norm_smul, Complex.norm_real, norm_inv, norm_norm]
      constructor
      · by_cases h : ‖Λ‖ = 0 <;> simp [h]
      · by_cases h : ‖y‖ = 0 <;> simp [h]
    · simp [hn]
  · intro k
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [hn]
  · convert hasSum_single (f := fun n : ℕ ↦ (if n = 0 then ((‖Λ‖ * ‖y‖ : ℝ) : ℂ) else 0) •
        (if n = 0 then ((‖Λ‖⁻¹ : ℝ) : ℂ) • Λ else 0).smulRight
          (if n = 0 then ((‖y‖⁻¹ : ℝ) : ℂ) • y else 0)) 0 (by intro n hn; simp [hn]) using 1
    simp only [ite_true]
    by_cases hΛ : ‖Λ‖ = 0
    · have : Λ = 0 := norm_eq_zero.mp hΛ
      subst this; ext; simp
    by_cases hy : ‖y‖ = 0
    · have : y = 0 := norm_eq_zero.mp hy
      subst this; ext; simp
    ext x
    simp [ContinuousLinearMap.smulRight_apply, smul_smul]
    field_simp [hΛ, hy]

/-- Paper: §10.3, p. 448. Strong nuclearity implies nuclearity. -/
theorem IsStronglyNuclearBanachOperator.isNuclearOperator [CompleteSpace E]
    {A : E →L[ℂ] G} (_hA : IsStronglyNuclearBanachOperator A) : IsNuclearOperator A := by
  obtain ⟨c, Λ, y, hb, hc, hs⟩ := _hA
  rw [isNuclearOperator_iff_isBanachNuclear]
  let d : ℕ → ℂ := fun n ↦ (n : ℂ) + 1
  have hd (n : ℕ) : ‖d n‖ = (n : ℝ) + 1 := by
    simp only [d]; exact_mod_cast Complex.norm_natCast (n + 1)
  have hd0 (n : ℕ) : d n ≠ 0 := by
    intro h; have := hd n; rw [h, norm_zero] at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine ⟨fun n ↦ c n * d n ^ 2, fun n ↦ (d n)⁻¹ • Λ n, fun n ↦ (d n)⁻¹ • y n, ?_, ?_, ?_, ?_⟩
  · have h4 := (tendsto_zero_iff_norm_tendsto_zero.mp (hc 4)).eventually (gt_mem_nhds one_pos)
    refine Summable.of_norm_bounded_eventually_nat
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 4) ?_
    filter_upwards [h4, eventually_ge_atTop 1] with n hn h1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
    rw [norm_mul, norm_pow, Complex.norm_natCast] at hn
    rw [norm_norm, norm_mul, norm_pow, hd]
    have hcn := norm_nonneg (c n)
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    have : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
    calc ‖c n‖ * ((n : ℝ) + 1) ^ 2 * (n : ℝ) ^ 2
        ≤ ‖c n‖ * (4 * (n : ℝ) ^ 2) * (n : ℝ) ^ 2 := by gcongr
      _ = 4 * ((n : ℝ) ^ 4 * ‖c n‖) := by ring
      _ ≤ 4 := by nlinarith
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hinv
    rw [norm_smul, norm_inv, hd]
    exact mul_le_of_le_one_right (by positivity) (hb n).1
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hinv
    rw [norm_smul, norm_inv, hd]
    exact mul_le_of_le_one_right (by positivity) (hb n).2
  · intro x
    refine (hs.mapL (ContinuousLinearMap.apply ℂ G x)).congr_fun fun n ↦ ?_
    simp only [ContinuousLinearMap.apply_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_smul, smul_eq_mul]
    congr 1
    field_simp [hd0 n]

end StrongNuclearity

private theorem liftQL_mkQ_aux {M N : Type*} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N] (S : Submodule ℂ M) (f : M →L[ℂ] N)
    (h : S ≤ f.ker) (v : M) : S.liftQL f h (S.mkQ v) = f v := by
  rw [Submodule.liftQL_apply]; rfl


variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "W(" l ", " r ", " s ")" =>
  CompactIntervalSobolev μ𝔽 (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) l r s
local notation "Θ(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs
local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs
local notation "Qω(" a ", " hI ", " hs ", " ω ")" =>
  spectralSobolevIsotypeQuotient F a hI hs ω
local notation "ρ(" l ", " r ", " s ", " hI ", " hs ")" =>
  (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).comp (ideleClassNorm F).ker.subtype
local notation "Wω(" hI ", " hs ", " ω ")" => actionIsotype (ρ(_, _, _, hI, hs)) ω
local notation "testAction(" l ", " r ", " s ", " hI ", " hs ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 l r s hI hs
local notation "h₀" => le_rfl (a := (0 : ℝ))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " χ ", " z ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽
    (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) χ z)

-- Select the norm topology directly when using the locally convex nuclear ideal.
local instance instSpectralQuotientPolynormableSec3 (a : ℝ) {l r s : ℝ}
    (hI : l ≤ r) (hs : 0 ≤ s) : PolynormableSpace ℂ Q(a, hI, hs) :=
  (norm_withSeminorms ℂ Q(a, hI, hs)).toPolynormableSpace

section Convolution

variable (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)

/-- A Pettis integral of translates of a vector in a closed invariant subspace of a
Hilbert space stays in that subspace, since every vector orthogonal to it kills the integrand. -/
private theorem hardySobolevTestAction_preserves_globalTheta_aux {X V : Type*}
    [Group X] [MeasurableSpace X] (μ : Measure X) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (K : Submodule ℂ V) (hK : IsClosed (K : Set V))
    (τ : X →* (V →L[ℂ] V)) (hτ : ∀ g, ∀ v ∈ K, τ g v ∈ K) {ψ : X → ℂ} {u b : V}
    (hu : u ∈ K) (hb : HasPettisIntegral (.positive μ) (fun g ↦ ψ g • τ g u) b) : b ∈ K := by
  have : CompleteSpace K := hK.completeSpace_coe
  rw [← K.orthogonal_orthogonal]
  intro w hw
  have hδ := congrArg
    (fun z : PettisWeakCompletion V ↦ (show Module.Dual ℂ (StrongDual ℂ V) from z)
      (innerSL ℂ w)) hb.2
  change innerSL ℂ w b = ∫ g, innerSL ℂ w (ψ g • τ g u) ∂μ at hδ
  rw [innerSL_apply_apply] at hδ
  rw [hδ]
  refine integral_eq_zero_of_ae (.of_forall fun g ↦ ?_)
  change innerSL ℂ w (ψ g • τ g u) = 0
  rw [innerSL_apply_apply]
  exact (K.mem_orthogonal' w).mp hw _ (K.smul_mem _ (hτ g u hu))

/-- Paper: (10.3.1.2), p. 448, and (10.3.2.2), p. 454. Convolution with a
test preserves the closed weighted theta subspace, so it descends to the quotient. -/
theorem hardySobolevTestAction_preserves_globalTheta (φ : BruhatCompactSupport C𝔽) :
    Θ(a, hI, hs) ≤ ((Θ(a, hI, hs)).mkQL.comp (testAction(l, r, s, hI, hs) φ)).ker := by
  intro v hv
  obtain ⟨ρ, hρ, -, -⟩ := exists_globalThetaSobolevAction (F := F) a hI hs
  have hinv : ∀ g, ∀ w ∈ Θ(a, hI, hs), hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs g w ∈
      Θ(a, hI, hs) := fun g w hw ↦ by
    rw [← hρ g ⟨w, hw⟩]
    exact (ρ g ⟨w, hw⟩).property
  have hmem := hardySobolevTestAction_preserves_globalTheta_aux μ𝔽 (Θ(a, hI, hs))
    (Submodule.isClosed_topologicalClosure _) (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs)
    hinv hv (bruhatRegularizedAction_apply μ𝔽 (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs)
      (exists_hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).choose_spec.2 φ v)
  exact (Submodule.Quotient.mk_eq_zero (Θ(a, hI, hs))).mpr hmem

/-- Paper: (10.3.1.2), p. 448, and (10.3.2.2), p. 454. The spectral convolution
operator is the descended Hardy–Sobolev test action. -/
def spectralConvolution (φ : BruhatCompactSupport C𝔽) : Q(a, hI, hs) →L[ℂ] Q(a, hI, hs) :=
  (Θ(a, hI, hs)).liftQL ((Θ(a, hI, hs)).mkQL.comp (testAction(l, r, s, hI, hs) φ))
    (hardySobolevTestAction_preserves_globalTheta (F := F) a hI hs φ)

/-- Paper: (10.3.1.2), p. 448, and (10.3.2.2), p. 454. On a representative,
spectral convolution takes the quotient class of its ambient convolution. -/
theorem spectralConvolution_mkQ (φ : BruhatCompactSupport C𝔽) (v : W(l, r, s)) :
    spectralConvolution (F := F) a hI hs φ ((Θ(a, hI, hs)).mkQ v) =
      (Θ(a, hI, hs)).mkQ (testAction(l, r, s, hI, hs) φ v) := by
  unfold spectralConvolution
  have h := (liftQL_mkQ_aux (Θ(a, hI, hs))
    ((Θ(a, hI, hs)).mkQL.comp (testAction(l, r, s, hI, hs) φ))
    (hardySobolevTestAction_preserves_globalTheta (F := F) a hI hs φ) v)
  with_reducible_and_instances exact h.trans (Submodule.mkQL_apply _ _)

open scoped UniformConvergenceCLM in
/-- Descending a linear family of operators through a fixed quotient is linear. -/
private theorem spectralConvolution_isLinear_aux {P M : Type*} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup M] [Module ℂ M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul ℂ M] {𝔖 : Set (Set M)} (S : Submodule ℂ M)
    (T : P →ₗ[ℂ] (M →Lᵤ[ℂ, 𝔖] M)) (h : ∀ p, S ≤ (S.mkQL.comp (T p)).ker) :
    IsLinearMap ℂ (fun p ↦ S.liftQL (S.mkQL.comp (T p)) (h p)) := by
  constructor
  · intro p q
    refine ContinuousLinearMap.coe_injective (Submodule.linearMap_qext S (LinearMap.ext fun x ↦ ?_))
    change S.mkQ (T (p + q) x) = S.mkQ (T p x) + S.mkQ (T q x)
    rw [← map_add, T.map_add]
    rfl
  · intro c p
    refine ContinuousLinearMap.coe_injective (Submodule.linearMap_qext S (LinearMap.ext fun x ↦ ?_))
    change S.mkQ (T (c • p) x) = c • S.mkQ (T p x)
    rw [← map_smul, T.map_smul]
    rfl

/-- Paper: (10.3.1.2), p. 448, and (10.3.2.2), p. 454. The descended action
is complex linear in the test. -/
theorem spectralConvolution_isLinear :
    IsLinearMap ℂ (spectralConvolution (F := F) a hI hs) :=
  spectralConvolution_isLinear_aux (Θ(a, hI, hs)) (testAction(l, r, s, hI, hs))
    (hardySobolevTestAction_preserves_globalTheta (F := F) a hI hs)

/-- A continuous endomorphism commuting with the translation action intertwines the
two regularized vectors obtained from Pettis integrals of the corresponding orbits. -/
private theorem hardySobolevTestAction_preserves_spectralIsotype_aux {X V : Type*}
    [CommGroup X] [MeasurableSpace X] (μ : Measure X) [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [SeparatingDual ℂ V]
    (τ : X →* (V →L[ℂ] V)) {ψ : X → ℂ} (k : X) (u w : V) (hk : τ k u = w) {a b : V}
    (ha : HasPettisIntegral (.positive μ) (fun g ↦ ψ g • τ g u) a)
    (hb : HasPettisIntegral (.positive μ) (fun g ↦ ψ g • τ g w) b) : τ k a = b := by
  have ev {f : X → V} {v : V} (h : HasPettisIntegral (.positive μ) f v) (δ : StrongDual ℂ V) :
      δ v = ∫ g, δ (f g) ∂μ :=
    congrArg (fun z : PettisWeakCompletion V ↦ (show Module.Dual ℂ (StrongDual ℂ V) from z) δ) h.2
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun δ ↦ ?_
  have hδ := ev ha (δ.comp (τ k))
  rw [ContinuousLinearMap.comp_apply] at hδ
  rw [hδ, ev hb]
  refine integral_congr_ae (.of_forall fun g ↦ ?_)
  change δ (τ k (ψ g • τ g u)) = δ (ψ g • τ g w)
  congr 1
  rw [(τ k).map_smul, ← hk]
  congr 1
  exact congrArg (fun T : V →L[ℂ] V ↦ T u)
    (show τ k * τ g = τ g * τ k by rw [← map_mul, ← map_mul, mul_comm])

/-- The regularized action of a commutative group commutes with its translations, so it
preserves every isotype of a restricted translation action. -/
private theorem hardySobolevTestAction_preserves_spectralIsotype_aux₂ {X V : Type*}
    [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [μ.IsHaarMeasure] [AddCommGroup V] [Module ℂ V] [UniformSpace V]
    [IsUniformAddGroup V] [PolynormableSpace ℂ V] [T2Space V] [CompleteSpace V]
    [SeparatingDual ℂ V] (τ : X →* (V →L[ℂ] V)) (hτ : Continuous (fun p : X × V ↦ τ p.1 p.2))
    (φ : BruhatCompactSupport X) (K : Subgroup X) (ω : PontryaginDual K) :
    ∀ v ∈ actionIsotype (τ.comp K.subtype) ω,
      bruhatRegularizedAction μ τ hτ φ v ∈ actionIsotype (τ.comp K.subtype) ω := by
  intro v hv
  rw [mem_actionIsotype] at hv ⊢
  intro k
  have h := hardySobolevTestAction_preserves_spectralIsotype_aux μ τ k.val v ((ω k : ℂ) • v)
    (hv k) (bruhatRegularizedAction_apply μ τ hτ φ v)
    (bruhatRegularizedAction_apply μ τ hτ φ ((ω k : ℂ) • v))
  change τ k.val (bruhatRegularizedAction μ τ hτ φ v) = _
  exact h.trans (map_smul (bruhatRegularizedAction μ τ hτ φ) _ _)

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
Convolution preserves the ambient norm-one isotype. -/
theorem hardySobolevTestAction_preserves_spectralIsotype (ω : PontryaginDual C₁)
    (φ : BruhatCompactSupport C𝔽) :
    ∀ v ∈ Wω(hI, hs, ω), testAction(l, r, s, hI, hs) φ v ∈ Wω(hI, hs, ω) :=
  hardySobolevTestAction_preserves_spectralIsotype_aux₂ μ𝔽
    (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs)
    (exists_hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).choose_spec.2 φ C₁ ω

local notation "Nω(" ω ")" => (Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype
local notation "Aω(" ω ", " φ ")" =>
  (ContinuousLinearMap.restrict (testAction(l, r, s, hI, hs) φ)
    (hardySobolevTestAction_preserves_spectralIsotype (F := F) hI hs ω φ))

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
Convolution preserves the theta intersection in each norm-one isotype. -/
theorem hardySobolevTestAction_preserves_spectralIsotypeTheta (ω : PontryaginDual C₁)
    (φ : BruhatCompactSupport C𝔽) :
    Nω(ω) ≤ ((Nω(ω)).mkQL.comp Aω(ω, φ)).ker := by
  intro v hv
  have hz := hardySobolevTestAction_preserves_globalTheta (F := F) a hI hs φ
    (show v.val ∈ Θ(a, hI, hs) from hv)
  have hout : testAction(l, r, s, hI, hs) φ v.val ∈ Θ(a, hI, hs) :=
    (Submodule.Quotient.mk_eq_zero (Θ(a, hI, hs))).mp hz
  apply (Submodule.Quotient.mk_eq_zero (Nω(ω))).mpr
  exact hout

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
The isotype operator descends ambient convolution restricted to that isotype. -/
def spectralIsotypeConvolution (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽) :
    Qω(a, hI, hs, ω) →L[ℂ] Qω(a, hI, hs, ω) :=
  (Nω(ω)).liftQL ((Nω(ω)).mkQL.comp Aω(ω, φ))
    (hardySobolevTestAction_preserves_spectralIsotypeTheta (F := F) a hI hs ω φ)

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
On an isotypic representative the restricted operator takes the class of its convolution. -/
theorem spectralIsotypeConvolution_mkQ (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (v : Wω(hI, hs, ω)) :
    spectralIsotypeConvolution (F := F) a hI hs ω φ ((Nω(ω)).mkQ v) =
      (Nω(ω)).mkQ (Aω(ω, φ) v) :=
  rfl

private theorem spectralConvolution_range_isotype_aux {X V : Type*}
    [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [μ.IsHaarMeasure]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℂ V] [SeparatingDual ℂ V]
    (τ : X →* (V →L[ℂ] V)) (ψ : X → ℂ) (k : X) (c : ℂ)
    (hψ : ∀ g, ψ (k⁻¹ * g) = c * ψ g) (u a : V)
    (ha : HasPettisIntegral (.positive μ) (fun g ↦ ψ g • τ g u) a) :
    τ k a = c • a := by
  have ev (δ : StrongDual ℂ V) : δ a = ∫ g, δ (ψ g • τ g u) ∂μ :=
    congrArg (fun z : PettisWeakCompletion V ↦
      (show Module.Dual ℂ (StrongDual ℂ V) from z) δ) ha.2
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro δ
  have hδ := ev (δ.comp (τ k))
  rw [ContinuousLinearMap.comp_apply] at hδ
  calc
    δ (τ k a) = ∫ g, δ (τ k (ψ g • τ g u)) ∂μ := hδ
    _ = ∫ g, δ (ψ g • τ (k * g) u) ∂μ := by
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      rw [(τ k).map_smul, map_mul]
      rfl
    _ = ∫ g, δ (ψ (k⁻¹ * g) • τ g u) ∂μ := by
      rw [← integral_mul_left_eq_self
        (fun g ↦ δ (ψ (k⁻¹ * g) • τ g u)) k]
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      simp
    _ = c * ∫ g, δ (ψ g • τ g u) ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      rw [hψ g, mul_smul, map_smul]
      simp
    _ = δ (c • a) := by rw [← ev δ, map_smul]; rfl

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
The full quotient action of an isotypic test has range in the corresponding quotient isotype.
Deviation: For left translation φ(x) ↦ φ(k⁻¹x), the weight is ω as an
eigencharacter. Equivalently the pointwise covariance is φ(kx) = ω⁻¹(k)φ(x). -/
theorem spectralConvolution_range_isotype (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    range (spectralConvolution (F := F) a hI hs φ) ⊆
      range (fun v : Wω(hI, hs, ω) ↦ (Θ(a, hI, hs)).mkQ v.val) := by
  have hW (v : W(l, r, s)) :
      testAction(l, r, s, hI, hs) φ v ∈ Wω(hI, hs, ω) := by
    rw [mem_actionIsotype]
    intro k
    exact spectralConvolution_range_isotype_aux μ𝔽
      (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs) φ.val k.val (ω k : ℂ)
      (_hφ k) v _ (bruhatRegularizedAction_apply μ𝔽
        (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs)
        (exists_hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).choose_spec.2 φ v)
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (Θ(a, hI, hs)) x
  exact ⟨⟨testAction(l, r, s, hI, hs) φ v, hW v⟩,
    spectralConvolution_mkQ (F := F) a hI hs φ v⟩

end Convolution

section FiniteSums

variable {ι Z E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Paper: (10.3.1.1), p. 448, and (10.3.2.1), p. 453. Form a finite section
by summing the rank-one contributions of all jets belonging to the selected zeros.
The functional in each term is the transpose of convolution applied to that jet. -/
def spectralConvolutionFiniteSum (A : E →L[ℂ] E) (x : ι → E) (Λ : ι → StrongDual ℂ E)
    (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → ι) : E →L[ℂ] E :=
  ∑ z ∈ K, ∑ m : Fin (N z), ((Λ (jet z m)).comp A).smulRight (x (jet z m))

/-- Paper: (10.3.1.21), p. 451. The finite section at one zero with one
surviving jet is exactly the transpose functional times its biorthogonal vector.
Deviation: Sanity check in multiplicity one. -/
theorem spectralConvolutionFiniteSum_single (A : E →L[ℂ] E) (x : ι → E) (Λ : ι → StrongDual ℂ E)
    (z : Z) (jet : Z → Fin 1 → ι) :
    spectralConvolutionFiniteSum A x Λ {z} (fun _ ↦ 1) jet =
      ((Λ (jet z 0)).comp A).smulRight (x (jet z 0)) := by
  simp [spectralConvolutionFiniteSum]

end FiniteSums

section TraceNormLimits

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Paper: (10.3.1.23), p. 452. Trace-norm Cauchy tails for a rectangular
family of finite-rank operators. A trace-class witness gives the difference
its actual trace norm. -/
def SpectralRectanglesTraceCauchy (B : ℕ × ℕ → H →L[ℂ] H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ i : ℕ × ℕ, ∀ j k, i ≤ j → i ≤ k →
    ∃ T : nuclearEndomorphisms H, T.val = B j - B k ∧ traceNorm T < ε

/-- Paper: (10.3.1.23), p. 452. Constant rectangles have zero differences.
Deviation: Sanity check for the trace-norm Cauchy condition. -/
theorem spectralRectanglesTraceCauchy_const (A : H →L[ℂ] H) :
    SpectralRectanglesTraceCauchy (fun _ ↦ A) := by
  intro ε hε
  refine ⟨(0, 0), fun _ _ _ _ ↦ ⟨0, by simp, ?_⟩⟩
  letI : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hz := ((traceNorm_normedSpaceCore (H := H)).norm_eq_zero_iff
    (0 : nuclearEndomorphisms H)).mpr rfl
  exact lt_of_eq_of_lt hz hε

private theorem spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg
    (T : H →L[ℂ] H) (n : ℕ) : 0 ≤ approximationNumber T n :=
  Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _

/-- Every finite sum of approximation numbers is bounded by the trace norm. -/
private theorem spectralConvolutionFiniteSum_limit_of_traceCauchy_bound
    (T : nuclearEndomorphisms H) (s : Finset ℕ) :
    ∑ n ∈ s, approximationNumber T.val n ≤ traceNorm T := by
  have hmem := (mem_traceClassOperators_iff_isNuclearOperator T.val).2 T.property
  have hsum : Summable (approximationNumber T.val) := by simpa using hmem.2
  have ht := schattenNorm_one_eq_traceNorm T
  simp only [schattenNorm, Real.rpow_one, div_one] at ht
  rw [← ht]
  exact hsum.sum_le_tsum s (fun n _ ↦ spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg T.val n)

/-- Once the rectangle includes a zero, its jets reproduce the corresponding
coordinates of the image of the original operator. -/
private theorem spectralConvolutionFiniteSum_limit_of_traceCauchy_coordinate {ι Z : Type*}
    (A : H →L[ℂ] H) (x : ι → H) (Λ : ι → StrongDual ℂ H) (K : Finset Z)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → ι) (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : Injective (fun j : (z : Z) × Fin (N z) ↦ jet j.1 j.2))
    (z : Z) (hz : z ∈ K) (m : Fin (N z)) (v : H) :
    Λ (jet z m) (spectralConvolutionFiniteSum A x Λ K N jet v) = Λ (jet z m) (A v) := by
  classical
  simp only [spectralConvolutionFiniteSum, sum_apply, map_sum, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single_of_mem z hz]
  · rw [Finset.sum_eq_single m]
    · rw [hb.1, mul_one]
    · intro k _ hk
      have hne : jet z k ≠ jet z m :=
        fun h ↦ hk (eq_of_heq (Sigma.mk.inj_iff.mp (hj (a₁ := ⟨z, k⟩) (a₂ := ⟨z, m⟩) h)).2)
      rw [hb.2.1 _ _ hne, mul_zero]
    · simp
  · intro w _ hw
    apply Finset.sum_eq_zero
    intro k _
    have hne : jet w k ≠ jet z m :=
      fun h ↦ hw (congrArg Sigma.fst (hj (a₁ := ⟨w, k⟩) (a₂ := ⟨z, m⟩) h))
    rw [hb.2.1 _ _ hne, mul_zero]

/-- Trace-norm Cauchy bounds pass to each finite sum of powers of approximation
numbers at an operator-norm limit. Taking their supremum controls the Schatten tail. -/
private theorem spectralConvolutionFiniteSum_limit_of_traceCauchy_tail
    (B : ℕ × ℕ → H →L[ℂ] H) (C : H →L[ℂ] H) (hlim : Tendsto B atTop (𝓝 C))
    (hc : SpectralRectanglesTraceCauchy B) (p : ℝ) (hp : 1 ≤ p) (ε : ℝ)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∀ᶠ j in atTop, Summable (fun n ↦ approximationNumber (B j - C) n ^ p) ∧
      ∑' n, approximationNumber (B j - C) n ^ p ≤ ε := by
  have nn := spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg (H := H)
  have hcont (n : ℕ) : Continuous (fun D : H →L[ℂ] H ↦ approximationNumber D n) :=
    (LipschitzWith.of_dist_le' (K := 1) (fun D E ↦ by
      simpa only [dist_eq_norm, Real.norm_eq_abs, one_mul] using abs_approximationNumber_sub_le D E n)).continuous
  obtain ⟨i, hi⟩ := hc ε hε
  filter_upwards [eventually_ge_atTop i] with j hj
  have hbound (s : Finset ℕ) : ∑ n ∈ s, approximationNumber (B j - C) n ^ p ≤ ε := by
    apply le_of_tendsto (tendsto_finsetSum s fun n _ ↦
      ((hcont n).continuousAt.tendsto.comp (tendsto_const_nhds.sub hlim)).rpow_const
        (Or.inr (zero_le_one.trans hp)))
    filter_upwards [eventually_ge_atTop i] with k hk
    obtain ⟨T, hT, ht⟩ := hi j k hj hk
    change ∑ n ∈ s, approximationNumber (B j - B k) n ^ p ≤ ε
    rw [← hT]
    refine (Finset.sum_le_sum fun n _ ↦ Real.rpow_le_self_of_le_one (nn _ n) ?_ hp).trans
      ((spectralConvolutionFiniteSum_limit_of_traceCauchy_bound T s).trans ht.le)
    have h := spectralConvolutionFiniteSum_limit_of_traceCauchy_bound T {n}
    exact (by simpa using h : approximationNumber T.val n ≤ traceNorm T).trans (ht.le.trans hε₁)
  have hnonneg : 0 ≤ fun n ↦ approximationNumber (B j - C) n ^ p :=
    fun n ↦ Real.rpow_nonneg (nn _ n) _
  exact ⟨summable_of_sum_le hnonneg hbound, Real.tsum_le_of_sum_le hnonneg hbound⟩

/-- Paper: (10.3.1.23), p. 452. A trace-norm Cauchy family of biorthogonal
finite sections converges to the given operator in every Schatten norm.
Each coordinate of the image eventually agrees with the corresponding
coordinate of the operator. Totality of the functionals identifies the limit. -/
theorem spectralConvolutionFiniteSum_limit_of_traceCauchy {ι Z : Type*}
    (A : H →L[ℂ] H) (x : ι → H) (Λ : ι → StrongDual ℂ H)
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → ι)
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : Bijective (fun j : (z : Z) × Fin (N z) ↦ jet j.1 j.2))
    (p : ℝ) (hp : 1 ≤ p) :
    let B (ij : ℕ × ℕ) := spectralConvolutionFiniteSum A x Λ
      (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn) N jet
    let S := schattenClass H H p hp
    SpectralRectanglesTraceCauchy B →
      ∃ (hA : A ∈ S) (hB : ∀ ij, B ij ∈ S),
        Tendsto (fun ij ↦ schattenNorm (E := H) (F := H) (p := p) (hp := hp)
          (⟨B ij, hB ij⟩ - ⟨A, hA⟩ : S)) atTop (𝓝 0) := by
  classical
  intro B S hc
  have hB (j) : B j ∈ S := by
    exact S.sum_mem fun z _ ↦ S.sum_mem fun m _ ↦ smulRight_mem_schattenClass hp _ _
  have hCauchy : CauchySeq B := by
    refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
    obtain ⟨i, hi⟩ := hc ε hε
    refine ⟨i, fun j hj k hk ↦ ?_⟩
    obtain ⟨T, hT, ht⟩ := hi j k hj hk
    rw [dist_eq_norm, ← hT, ← approximationNumber_zero_eq_opNorm T.val
      (isCompactOperator_of_isNuclearOperator T.property)]
    have h := spectralConvolutionFiniteSum_limit_of_traceCauchy_bound T {0}
    exact lt_of_le_of_lt (by simpa using h) ht
  obtain ⟨C, hlim⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hCA : C = A := by
    ext v
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    have hev : ContinuousLinearMap.apply ℂ ℂ (C v) = ContinuousLinearMap.apply ℂ ℂ (A v) := by
      apply ContinuousLinearMap.ext_on _hb.2.2.2
      rintro _ ⟨i, rfl⟩
      obtain ⟨⟨z, m⟩, rfl⟩ := _hj.2 i
      change Λ (jet z m) (C v) = Λ (jet z m) (A v)
      apply tendsto_nhds_unique ((Λ (jet z m)).continuous.continuousAt.tendsto.comp
        (((ContinuousLinearMap.apply ℂ H v).continuous.continuousAt.tendsto).comp hlim))
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (e z)] with j hj
      exact (spectralConvolutionFiniteSum_limit_of_traceCauchy_coordinate A x Λ _ N jet _hb _hj.1
        z (Finset.mem_preimage.mpr (Finset.mem_product.mpr
          ⟨Finset.mem_Iic.mpr hj.1, Finset.mem_Iic.mpr hj.2⟩)) m v).symm
    exact fun ℓ ↦ DFunLike.congr_fun hev ℓ
  subst C
  have hcompact := isCompactOperator_of_tendsto hlim (.of_forall fun j ↦ (hB j).1)
  have tail := spectralConvolutionFiniteSum_limit_of_traceCauchy_tail B A hlim hc p hp
  obtain ⟨j, hj, _⟩ := (tail 1 zero_lt_one le_rfl).exists
  have hdiff : B j - A ∈ S := ⟨(hB j).1.sub hcompact, hj⟩
  have hA : A ∈ S := by simpa only [sub_sub_cancel] using S.sub_mem (hB j) hdiff
  refine ⟨hA, hB, ?_⟩
  have hzero : Tendsto (fun j ↦ ∑' n, approximationNumber (B j - A) n ^ p) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [tail _ (lt_min (half_pos hε) zero_lt_one) (min_le_right (ε / 2) 1)] with j hj
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun n ↦ Real.rpow_nonneg
      (spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg (B j - A) n) p)]
    exact hj.2.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hε))
  exact hzero.rpow_const_nhds_zero (one_div_pos.mpr (zero_lt_one.trans_le hp))

/-- An operator whose range lies in a subspace of dimension at most `r` is a sum of
`r` rank-one operators whose functionals have norm at most that of the operator and
whose vectors have norm at most one. -/
private theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_rankOne
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] (D : H →L[ℂ] H) (hD : ∀ x, D x ∈ V)
    (r : ℕ) (hr : Module.finrank ℂ V ≤ r) :
    ∃ (Λ : ℕ → StrongDual ℂ H) (y : ℕ → H), (∀ i, ‖Λ i‖ ≤ ‖D‖ ∧ ‖y i‖ ≤ 1) ∧
      ∑ i ∈ Finset.range r, (Λ i).smulRight (y i) = D := by
  classical
  let b := stdOrthonormalBasis ℂ V
  let d := Module.finrank ℂ V
  let y : ℕ → H := fun i ↦ if h : i < d then (b ⟨i, h⟩ : H) else 0
  have hy (i : ℕ) : ‖y i‖ ≤ 1 := by
    by_cases h : i < d
    · simp only [y, h, ↓reduceDIte, Submodule.norm_coe]
      exact (b.orthonormal.1 _).le
    · simp [y, h]
  refine ⟨fun i ↦ (innerSL ℂ (y i)).comp D, y, fun i ↦ ⟨?_, hy i⟩, ?_⟩
  · calc ‖(innerSL ℂ (y i)).comp D‖ ≤ ‖innerSL ℂ (y i)‖ * ‖D‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖D‖ := by
          rw [innerSL_apply_norm]
          exact mul_le_mul_of_nonneg_right (hy i) (norm_nonneg _)
      _ = ‖D‖ := one_mul _
  · ext x
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply]
    rw [← Finset.sum_subset (Finset.range_mono hr) (fun i _ hi ↦ by
      have hi' : ¬ i < d := fun h ↦ hi (Finset.mem_range.mpr h)
      simp only [y, hi', ↓reduceDIte, smul_zero]), Finset.sum_range]
    have h := congrArg Subtype.val (b.sum_repr' ⟨D x, hD x⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, Submodule.coe_inner] at h
    refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans h
    simp only [y, dif_pos (show (j : ℕ) < d from j.is_lt), Fin.eta]

/-- Rapid decay against `n ^ k` for every `k` gives rapid decay against `(n + 1) ^ k`. -/
private theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_succ
    (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hf : ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * f n) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ k * f n) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n : ℕ ↦ 2 ^ k * ((n : ℝ) ^ k * f n)) atTop (𝓝 0) := by
    simpa using (hf k).const_mul (2 ^ k)
  refine squeeze_zero' (.of_forall fun n ↦ mul_nonneg (by positivity) (hf0 n)) ?_ h2
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) k) (hf0 n)

/-- If `c n ≤ e (n + 1) + e n` and `e` decays rapidly, then `c (⌊√m⌋)` decays rapidly in `m`. -/
private theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_sqrt
    (e : ℕ → ℝ) (he0 : ∀ n, 0 ≤ e n)
    (he : ∀ j : ℕ, Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ j * e n) atTop (𝓝 0))
    (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hc : ∀ n, c n ≤ e (n + 1) + e n) (k : ℕ) :
    Tendsto (fun m : ℕ ↦ (m : ℝ) ^ k * c (Nat.sqrt m)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (2 * k) * e (n + 1)) atTop (𝓝 0) := by
    have h := (tendsto_add_atTop_iff_nat 1).mpr (he (2 * k))
    refine squeeze_zero (fun n ↦ mul_nonneg (by positivity) (he0 _)) (fun n ↦ ?_) h
    push_cast
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith) _) (he0 _)
  have hg : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (2 * k) * c n) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ mul_nonneg (by positivity) (hc0 n)) (fun n ↦ ?_)
      (by simpa using hshift.add (he (2 * k)))
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hc n) (by positivity)
  have hsqrt : Tendsto Nat.sqrt atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b * b, fun m hm ↦ Nat.le_sqrt.mpr hm⟩
  refine squeeze_zero (fun m ↦ mul_nonneg (by positivity) (hc0 _)) (fun m ↦ ?_) (hg.comp hsqrt)
  simp only [Function.comp_apply]
  refine mul_le_mul_of_nonneg_right ?_ (hc0 _)
  rw [pow_mul]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  have h := Nat.lt_succ_sqrt' m
  have h' : (m : ℝ) < ((Nat.sqrt m : ℝ) + 1) ^ 2 := by exact_mod_cast h
  exact h'.le

/-- Rescaling a rank-one term by the norm bound of its functional. -/
private theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_smul
    (c : ℝ) (Λ : StrongDual ℂ H) (hΛ : ‖Λ‖ ≤ c) (v : H) :
    (c : ℂ) • (((c : ℂ)⁻¹ • Λ).smulRight v) = Λ.smulRight v ∧ ‖(c : ℂ)⁻¹ • Λ‖ ≤ 1 := by
  by_cases hc : c = 0
  · subst hc
    have : Λ = 0 := norm_le_zero_iff.mp hΛ
    subst this
    simp
  constructor
  · ext x
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_smul,
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc), one_mul]
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    have hc' : 0 < c := lt_of_le_of_ne ((norm_nonneg _).trans hΛ) (Ne.symm hc)
    rw [abs_of_pos hc', inv_mul_le_iff₀ hc', mul_one]
    exact hΛ

/-- An approximant of rank at most `n` within `2⁻ⁿ` of the `n`-th approximation number;
the zeroth one is zero. -/
private theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_approx
    (A : H →L[ℂ] H) (n : ℕ) :
    ∃ S : H →L[ℂ] H, FiniteDimensional ℂ (LinearMap.range S.toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range S.toLinearMap) ≤ n ∧
      ‖S - A‖ ≤ approximationNumber A n + (1 / 2) ^ n ∧ (n = 0 → S = 0) := by
  let X : Set ℝ := {r | ∃ S : H →L[ℂ] H,
    Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) ∧ r = ‖S - A‖}
  have hX : X.Nonempty := ⟨_, 0, by simp, rfl⟩
  have hlt : sInf X < sInf X + (1 / 2) ^ n := lt_add_of_pos_right _ (by positivity)
  obtain ⟨r, ⟨S, hS, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hX hlt
  have hfin : FiniteDimensional ℂ (LinearMap.range S.toLinearMap) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hS Cardinal.natCast_lt_aleph0)
  have hrank : Module.finrank ℂ (LinearMap.range S.toLinearMap) ≤ n :=
    Module.finrank_le_of_rank_le hS
  refine ⟨S, hfin, hrank, hr.le, fun hn ↦ ?_⟩
  subst hn
  have h0 : LinearMap.range S.toLinearMap = ⊥ :=
    Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hrank)
  ext x
  have hx : S x ∈ LinearMap.range S.toLinearMap := ⟨x, rfl⟩
  rw [h0, Submodule.mem_bot] at hx
  simpa using hx

/-- Paper: Theorem 10.3.1.1(3), p. 449. Rapid decay of the approximation
numbers gives a strongly nuclear expansion by the singular-value decomposition. -/
theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers (A : H →L[ℂ] H)
    (_hA : ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n)
      atTop (𝓝 0)) : IsStronglyNuclearBanachOperator A := by
  classical
  choose S hSfin hSrank hSA hS0 using
    isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_approx A
  have hdec (n : ℕ) : ∃ (Λ : ℕ → StrongDual ℂ H) (y : ℕ → H),
      (∀ i, ‖Λ i‖ ≤ ‖S (n + 1) - S n‖ ∧ ‖y i‖ ≤ 1) ∧
      ∑ i ∈ Finset.range (2 * n + 1), (Λ i).smulRight (y i) = S (n + 1) - S n := by
    have := hSfin n
    have := hSfin (n + 1)
    refine isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_rankOne
      (LinearMap.range (S (n + 1)).toLinearMap ⊔ LinearMap.range (S n).toLinearMap)
      (S (n + 1) - S n) (fun x ↦ ?_) (2 * n + 1) ?_
    · exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩)
        (Submodule.mem_sup_right ⟨x, rfl⟩)
    · refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
      have := hSrank n
      have := hSrank (n + 1)
      omega
  choose Λ y hΛy hsum using hdec
  let e : ℕ → ℝ := fun n ↦ ‖S n - A‖
  let a : ℕ → ℝ := fun n ↦ approximationNumber A n
  have ha0 (n : ℕ) : 0 ≤ a n :=
    Real.sInf_nonneg (by rintro _ ⟨T, -, rfl⟩; exact norm_nonneg _)
  have he (j : ℕ) : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ j * e n) atTop (𝓝 0) := by
    have h1 := isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_succ a ha0 _hA j
    have h2 := isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_succ
      (fun n ↦ (1 / 2 : ℝ) ^ n) (fun n ↦ by positivity)
      (fun k ↦ tendsto_pow_const_mul_const_pow_of_abs_lt_one k (by norm_num)) j
    refine squeeze_zero (fun n ↦ mul_nonneg (by positivity) (norm_nonneg _)) (fun n ↦ ?_)
      (by simpa using h1.add h2)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left ((hSA n).trans_eq (by rw [one_div, inv_pow])) (by positivity)
  let c : ℕ → ℝ := fun n ↦ ‖S (n + 1) - S n‖
  have hc (n : ℕ) : c n ≤ e (n + 1) + e n := by
    have : S (n + 1) - S n = (S (n + 1) - A) - (S n - A) := by abel
    simp only [c, e, this]
    exact norm_sub_le _ _
  have hdecay := isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_sqrt e
    (fun n ↦ norm_nonneg _) he c (fun n ↦ norm_nonneg _) hc
  let idx : ℕ → ℕ := fun m ↦ m - Nat.sqrt m * Nat.sqrt m
  let term : ℕ → H →L[ℂ] H := fun m ↦ (c (Nat.sqrt m) : ℂ) •
    (((c (Nat.sqrt m) : ℂ)⁻¹ • Λ (Nat.sqrt m) (idx m)).smulRight (y (Nat.sqrt m) (idx m)))
  have hterm (m : ℕ) : term m = (Λ (Nat.sqrt m) (idx m)).smulRight (y (Nat.sqrt m) (idx m)) :=
    (isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_smul _ _
      (hΛy _ _).1 _).1
  have hblock (N : ℕ) : ∑ m ∈ Finset.range (N * N), term m = S N := by
    induction N with
    | zero => simp [hS0 0 rfl]
    | succ N ih =>
      rw [show (N + 1) * (N + 1) = N * N + (2 * N + 1) by ring, Finset.sum_range_add, ih,
        show S (N + 1) = S N + (S (N + 1) - S N) by abel, ← hsum N]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' : i ≤ N + N := by rw [Finset.mem_range] at hi; omega
      rw [hterm]
      simp only [idx, Nat.sqrt_add_eq N hi', Nat.add_sub_cancel_left]
  have hS : Tendsto S atTop (𝓝 A) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [e] using he 0)
  have hnorm (m : ℕ) : ‖term m‖ ≤ c (Nat.sqrt m) := by
    rw [hterm, ContinuousLinearMap.norm_smulRight_apply]
    exact (mul_le_mul (hΛy _ _).1 (hΛy _ _).2 (norm_nonneg _) (norm_nonneg _)).trans_eq
      (mul_one _)
  have hsumm : Summable term := by
    refine Summable.of_norm_bounded_eventually_nat (g := fun m : ℕ ↦ 1 / (m : ℝ) ^ 2)
      (Real.summable_one_div_nat_pow.mpr one_lt_two) ?_
    filter_upwards [(hdecay 2).eventually (gt_mem_nhds zero_lt_one), eventually_ge_atTop 1]
      with m h1 hm
    have hm' : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    refine (hnorm m).trans ?_
    rw [le_div_iff₀ hm', mul_comm]
    exact h1.le
  have hsq : Tendsto (fun N : ℕ ↦ N * N) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b, fun N hN ↦ hN.trans (Nat.le_mul_self N)⟩
  have hlim : ∑' m, term m = A := by
    refine tendsto_nhds_unique ((hsumm.hasSum.tendsto_sum_nat).comp hsq) ?_
    refine hS.congr fun N ↦ ?_
    exact (hblock N).symm
  refine ⟨fun m ↦ (c (Nat.sqrt m) : ℂ), fun m ↦ (c (Nat.sqrt m) : ℂ)⁻¹ • Λ (Nat.sqrt m) (idx m),
    fun m ↦ y (Nat.sqrt m) (idx m), fun m ↦ ⟨?_, (hΛy _ _).2⟩, fun k ↦ ?_, ?_⟩
  · exact (isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_smul _ _
      (hΛy _ _).1 (0 : H)).2
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (hdecay k).congr fun m ↦ ?_
    rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  · exact hlim ▸ hsumm.hasSum


end TraceNormLimits

-- TODO(paper-gap): On p. 450 an interval cannot select an arbitrary K with
-- omitted zeros between selected ordinates. The sums below use the actual
-- biorthogonal finite sections of (10.3.1.1) and (10.3.2.1).
-- TODO(paper-gap): (10.3.1.18) uses a uniform bound on paired norms, which fails
-- for close simple zeta zeros (ERRATA R5). The finite sections need another estimate.
-- The same display evaluates the entire Mellin transform at t. Its block matrix
-- in (10.3.1.17) uses i*t. A transform (t-z)H(z) separates the two points.

/-- Paper: (10.3.1.18)–(10.3.1.22), p. 451. Each individual finite section
has a singular-value bound in terms of its actual rank-one factors.
Deviation: The bound depends on the selected vectors and functionals. For a
single zero it is a local block bound, with no uniform biorthogonal constant. -/
theorem spectralConvolutionFiniteSum_approximationNumber_le {ι Z E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (x : ι → E) (Λ : ι → StrongDual ℂ E)
    (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → ι) (n : ℕ) :
    approximationNumber (spectralConvolutionFiniteSum A x Λ K N jet) n ≤
      ∑ z ∈ K, ∑ m : Fin (N z), ‖(Λ (jet z m)).comp A‖ * ‖x (jet z m)‖ := by
  classical
  let T := spectralConvolutionFiniteSum A x Λ K N jet
  have h : approximationNumber T n ≤ ‖T‖ := by
    unfold approximationNumber
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro _ ⟨S, _, rfl⟩
      exact norm_nonneg _
    · exact ⟨0, by simp, by simp⟩
  apply h.trans
  unfold T spectralConvolutionFiniteSum
  apply (norm_sum_le _ _).trans
  refine Finset.sum_le_sum fun z _ ↦ ?_
  simpa only [ContinuousLinearMap.norm_smulRight_apply] using
    (norm_sum_le Finset.univ (fun m : Fin (N z) ↦ ((Λ (jet z m)).comp A).smulRight (x (jet z m))))

/-- Paper: (10.3.1.17), p. 450. Compactly supported Bruhat tests have
an integrable Fourier–Mellin pairing at every norm twist. The pairing is
the unweighted integral against the twisted base character. -/
theorem spectralConvolution_mellin_integrable (φ : BruhatCompactSupport C𝔽)
    (χ : PontryaginDual C𝔽) (z : ℂ) :
    Integrable (fun g ↦ φ.val g * ideleClassNormTwist (F := F) χ z g) μ𝔽 ∧
      M(φ, χ, z) = ∫ g, φ.val g * ideleClassNormTwist (F := F) χ z g ∂μ𝔽 := by
  have hc : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  constructor
  · exact (hc.mul (ideleClassNormTwist χ z).continuous).integrable_of_hasCompactSupport
      (show HasCompactSupport φ.val from φ.property.2).mul_right
  · exact Set.indicator_of_mem (Set.mem_univ _) _

section ApproximationDecay

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem spectralApprox_antitone (A : H →L[ℂ] H) : Antitone (approximationNumber A) := by
  intro m n hmn
  unfold approximationNumber
  refine le_csInf ⟨_, 0, by simp, rfl⟩ ?_
  rintro _ ⟨S, hS, rfl⟩
  exact csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩
    ⟨S, hS.trans (Nat.cast_le.mpr hmn), rfl⟩

omit [CompleteSpace H] in
/-- Adding two rank-n approximants gives a rank-at-most-2n approximant. -/
private theorem spectralApprox_add (A B : H →L[ℂ] H) (n : ℕ) :
    approximationNumber (A + B) (2 * n + 1) ≤ approximationNumber A n + approximationNumber B n := by
  refine le_add_of_forall_lt fun a ha b hb ↦ ?_
  have nonempty (T : H →L[ℂ] H) :
      {r : ℝ | ∃ S : H →L[ℂ] H, S.toLinearMap.rank ≤ (n : Cardinal) ∧ r = ‖S - T‖}.Nonempty :=
    ⟨_, 0, by simp, rfl⟩
  obtain ⟨_, ⟨S, hS, rfl⟩, hSa⟩ := exists_lt_of_csInf_lt (nonempty A) ha
  obtain ⟨_, ⟨T, hT, rfl⟩, hTb⟩ := exists_lt_of_csInf_lt (nonempty B) hb
  have hrank : (S + T).toLinearMap.rank ≤ ((2 * n + 1 : ℕ) : Cardinal) := by
    refine (LinearMap.rank_add_le _ _).trans ((add_le_add hS hT).trans ?_)
    exact_mod_cast (show n + n ≤ 2 * n + 1 by omega)
  calc
    approximationNumber (A + B) (2 * n + 1) ≤ ‖S + T - (A + B)‖ :=
      csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩ ⟨S + T, hrank, rfl⟩
    _ = ‖(S - A) + (T - B)‖ := by congr 1; abel
    _ ≤ a + b := (norm_add_le _ _).trans (add_le_add hSa.le hTb.le)

private abbrev SpectralApproxBound (A : H →L[ℂ] H) (k : ℕ) :=
  ∃ C : ℝ, ∀ n : ℕ, ((n : ℝ) + 1) ^ k * approximationNumber A n ≤ C

/-- A polynomial bound on odd approximation numbers extends to all indices by monotonicity. -/
private theorem spectralApprox_bound_of_odd (A : H →L[ℂ] H) (k : ℕ) (C : ℝ)
    (h : ∀ m : ℕ, ((m : ℝ) + 1) ^ k * approximationNumber A (2 * m + 1) ≤ C) :
    SpectralApproxBound A k := by
  refine ⟨max (approximationNumber A 0) (3 ^ k * C), fun n ↦ ?_⟩
  cases n with
  | zero => simp
  | succ n =>
    let m := n / 2
    have hi : 2 * m + 1 ≤ n + 1 := by dsimp [m]; omega
    have hc : ((n + 1 : ℕ) : ℝ) + 1 ≤ 3 * ((m : ℝ) + 1) := by
      exact_mod_cast (show n + 1 + 1 ≤ 3 * (m + 1) by dsimp [m]; omega)
    apply le_trans _ (le_max_right _ _)
    calc
      _ ≤ (3 * ((m : ℝ) + 1)) ^ k * approximationNumber A (2 * m + 1) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hc k) (spectralApprox_antitone A hi)
          (spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg _ _) (by positivity)
      _ = 3 ^ k * (((m : ℝ) + 1) ^ k * approximationNumber A (2 * m + 1)) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (h m) (by positivity)

/-- Trace-class operators have a uniform, one-power approximation-number bound. -/
private theorem spectralApprox_trace (T : nuclearEndomorphisms H) : SpectralApproxBound T.val 1 := by
  refine ⟨traceNorm T, fun n ↦ ?_⟩
  have h := Finset.sum_le_sum (s := Finset.range (n + 1))
    (fun i hi ↦ spectralApprox_antitone T.val (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  calc
    _ = ∑ _i ∈ Finset.range (n + 1), approximationNumber T.val n := by simp
    _ ≤ _ := h.trans (spectralConvolutionFiniteSum_limit_of_traceCauchy_bound T _)

private theorem spectralApprox_bound_add (A B : H →L[ℂ] H) (k : ℕ)
    (hA : SpectralApproxBound A k) (hB : SpectralApproxBound B k) : SpectralApproxBound (A + B) k := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨D, hD⟩ := hB
  apply spectralApprox_bound_of_odd _ _ (C + D)
  intro n
  calc
    _ ≤ ((n : ℝ) + 1) ^ k * (approximationNumber A n + approximationNumber B n) :=
      mul_le_mul_of_nonneg_left (spectralApprox_add A B n) (by positivity)
    _ ≤ _ := by rw [mul_add]; exact add_le_add (hC n) (hD n)

private theorem spectralApprox_bound_comp (A B : H →L[ℂ] H) (k : ℕ)
    (hA : SpectralApproxBound A k) (hB : SpectralApproxBound B 1) :
    SpectralApproxBound (A.comp B) (k + 1) := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨D, hD⟩ := hB
  apply spectralApprox_bound_of_odd _ _ (C * D)
  intro n
  have ha := spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg A n
  have hb := spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg B n
  have hC0 : 0 ≤ C := le_trans (mul_nonneg (by positivity) ha) (hC n)
  calc
    _ ≤ ((n : ℝ) + 1) ^ (k + 1) * (approximationNumber A n * approximationNumber B n) :=
      mul_le_mul_of_nonneg_left (by simpa [two_mul] using approximationNumber_comp_le A B n n)
        (by positivity)
    _ = (((n : ℝ) + 1) ^ k * approximationNumber A n) *
          (((n : ℝ) + 1) ^ 1 * approximationNumber B n) := by ring
    _ ≤ _ := mul_le_mul (hC n) (hD n) (mul_nonneg (by positivity) hb) hC0

/-- A family of trace-class operators in which every member is a finite sum of
two-fold products of family members has rapidly decreasing approximation numbers. -/
private theorem spectralApprox_rapid_of_factorization {ι : Type*} (A : ι → H →L[ℂ] H)
    (htrace : ∀ i, IsNuclearOperator (A i))
    (hfactor : ∀ i, A i ∈ AddSubmonoid.closure {T | ∃ j l, T = (A j).comp (A l)}) (i : ι) (k : ℕ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber (A i) n) atTop (𝓝 0) := by
  have bounds (p : ℕ) : ∀ j, SpectralApproxBound (A j) p := by
    induction p with
    | zero => exact fun j ↦ ⟨approximationNumber (A j) 0, fun n ↦ by
        simpa using spectralApprox_antitone (A j) (Nat.zero_le n)⟩
    | succ p ih =>
      intro j
      apply AddSubmonoid.closure_induction (motive := fun T _ ↦ SpectralApproxBound T (p + 1))
        _ _ _ (hfactor j)
      · rintro T ⟨u, v, rfl⟩
        exact spectralApprox_bound_comp _ _ _ (ih u) (spectralApprox_trace ⟨A v, htrace v⟩)
      · refine ⟨0, fun n ↦ ?_⟩
        have hz : approximationNumber (0 : H →L[ℂ] H) n ≤ ‖(0 : H →L[ℂ] H) - 0‖ :=
          csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩ ⟨0, by simp, rfl⟩
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by simpa using hz)
      · exact fun X Y _ _ ↦ spectralApprox_bound_add X Y _
  obtain ⟨C, hC⟩ := bounds (k + 1) i
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine squeeze_zero (fun n : ℕ ↦ mul_nonneg (by positivity)
    (spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg (A i) n)) ?_
    (show Tendsto (fun n : ℕ ↦ C * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) by simpa using hinv.const_mul C)
  intro n
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    _ ≤ ((n : ℝ) + 1) ^ k * approximationNumber (A i) n * ((n : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ n.cast_nonneg (by linarith) k)
        (spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg (A i) n)) (by positivity)
    _ = ((n : ℝ) + 1) ^ (k + 1) * approximationNumber (A i) n := by ring
    _ ≤ C := hC n

end ApproximationDecay

section TestFactorization

private local instance spectralApprox_isotype_polynormable (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : PolynormableSpace ℂ Qω(a, hI, hs, ω) :=
  (norm_withSeminorms ℂ Qω(a, hI, hs, ω)).toPolynormableSpace

/-- Bounded restriction and projection preserve a Banach nuclear presentation. -/
private theorem spectralApprox_nuclear_compression {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A) (J : K →L[ℂ] H) (P : H →L[ℂ] K) :
    IsNuclearOperator (P.comp (A.comp J)) := by
  obtain ⟨c, f, y, hc, hf, hy, hs⟩ := (isNuclearOperator_iff_isBanachNuclear _).mp hA
  apply (isNuclearOperator_iff_isBanachNuclear _).mpr
  refine ⟨c, fun n ↦ (f n).comp J, P ∘ y, hc, ?_,
    (P.continuous.tendsto' 0 0 (map_zero P)).comp hy, fun x ↦ ?_⟩
  · exact ((J.precomp ℂ).continuous.tendsto' 0 0 (map_zero _)).comp hf
  · simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_smul] using
      P.hasSum (hs (J x))

/-- The quotient representative formulas identify the compression with the restricted action. -/
private theorem spectralApprox_nuclear_representatives {H K V W : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [PolynormableSpace ℂ H] [PolynormableSpace ℂ K]
    (A : H →L[ℂ] H) (D : K →L[ℂ] K) (hn : IsNuclearOperator A)
    (S : Submodule ℂ H) [CompleteSpace S] (U : K ≃ₗᵢ[ℂ] S)
    (q : V → K) (π : W → H) (i : V → W) (B : V → V) (C : W → W)
    (hq : Surjective q) (hU : ∀ v, (U (q v) : H) = π (i v))
    (hD : ∀ v, D (q v) = q (B v))
    (hA : ∀ w, A (π w) = π (C w)) (hB : ∀ v, C (i v) = i (B v)) :
    IsNuclearOperator D := by
  let J := S.subtypeL.comp U.toContinuousLinearEquiv.toContinuousLinearMap
  let P := U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp S.orthogonalProjectionOnto
  have hPJ : LeftInverse P J := fun x ↦ by
    change U.symm (S.orthogonalProjectionOnto (U x : H)) = x
    rw [S.orthogonalProjectionOnto_mem_subspace_eq_self, U.symm_apply_apply]
  have hcomp : P.comp (A.comp J) = D := by
    ext x
    obtain ⟨v, rfl⟩ := hq x
    apply Eq.trans _ (hPJ (D (q v)))
    apply congrArg P
    change A (U (q v) : H) = (U (D (q v)) : H)
    rw [hU, hA, hB, hD, hU]
  rw [← hcomp]
  exact spectralApprox_nuclear_compression A hn J P

set_option maxHeartbeats 800000 in
/-- Compress ambient convolution to the isotype using the quotient isometry and
its orthogonal projection. -/
private theorem spectralApprox_isotype_nuclear (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (hn : IsNuclearOperator (spectralConvolution (F := F) a hI hs φ)) :
    let H := Qω(a, hI, hs, ω)
    let D : H →L[ℂ] H := spectralIsotypeConvolution (F := F) a hI hs ω φ
    IsNuclearOperator (E := H) (F := H) D := by
  have hiso := spectralSobolevIsotypeQuotient_isometry (F := F) a hI hs ω
  with_reducible obtain ⟨ρ, _, _, U, hU⟩ := hiso
  let S := actionIsotype (ρ.comp (ideleClassNorm F).ker.subtype) ω
  let _ : CompleteSpace S := (isClosed_actionIsotype _ _).completeSpace_coe
  let N := Θ(a, hI, hs)
  let B := (testAction(l, r, s, hI, hs) φ).restrict
    (hardySobolevTestAction_preserves_spectralIsotype (F := F) hI hs ω φ)
  exact spectralApprox_nuclear_representatives _ _ hn S U
    (spectralSobolevIsotypeQuotient_mk a hI hs ω) N.mkQ Subtype.val B
    (testAction(l, r, s, hI, hs) φ) (spectralSobolevIsotypeQuotient_mk_surjective a hI hs ω) hU
    (spectralIsotypeConvolution_mkQ (F := F) a hI hs ω φ)
    (spectralConvolution_mkQ (F := F) a hI hs φ) (fun _ ↦ rfl)

/-- Equality of descended convolutions can be checked on representatives. -/
private theorem spectralApprox_descend {H K V W : Type*}
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    (q : V →ₗ[ℂ] H) (hq : Surjective q) (i : V →ₗ[ℂ] W) (hi : Injective i)
    (f : K → H →L[ℂ] H) (g : K → W →L[ℂ] W) (b : K → V → V)
    (hf : ∀ k v, f k (q v) = q (b k v)) (hg : ∀ k v, i (b k v) = g k (i v)) :
    (∀ t, g t = 0 → f t = 0) ∧
    (∀ t u v, g t = g u + g v → f t = f u + f v) ∧
    (∀ t u v, (∀ x, g t x = g u (g v x)) → f t = (f u).comp (f v)) := by
  refine ⟨fun t ht ↦ ?_, fun t u v ht ↦ ?_, fun t u v ht ↦ ?_⟩
  · ext x
    obtain ⟨y, rfl⟩ := hq x
    change f t (q y) = 0
    rw [hf, ← q.map_zero]
    apply congrArg q
    apply hi
    rw [hg, ht, map_zero]
    rfl
  · ext x
    obtain ⟨y, rfl⟩ := hq x
    rw [add_apply, hf, hf, hf, ← q.map_add]
    apply congrArg q
    apply hi
    rw [map_add, hg, hg, hg, ht, add_apply]
  · ext x
    obtain ⟨y, rfl⟩ := hq x
    rw [ContinuousLinearMap.comp_apply, hf, hf, hf]
    apply congrArg q
    apply hi
    rw [hg, hg, hg, ht]

set_option maxHeartbeats 600000 in
private theorem spectralApprox_isotype_laws (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    let D := spectralIsotypeConvolution (F := F) a hI hs ω
    D 0 = 0 ∧ (∀ u v, D (u + v) = D u + D v) ∧
      ∀ t u v : BruhatCompactSupport C𝔽,
        t.val = lcaConvolution μ𝔽 u.val v.val → D t = (D u).comp (D v) := by
  let E := Wω(hI, hs, ω)
  let q := spectralSobolevIsotypeQuotient_mk (F := F) a hI hs ω
  let b (φ : BruhatCompactSupport C𝔽) := (testAction(l, r, s, hI, hs) φ).restrict
    (hardySobolevTestAction_preserves_spectralIsotype (F := F) hI hs ω φ)
  have laws := spectralApprox_descend q.toLinearMap
    (spectralSobolevIsotypeQuotient_mk_surjective a hI hs ω) E.subtype Subtype.val_injective
    (spectralIsotypeConvolution (F := F) a hI hs ω) (fun φ ↦ testAction(l, r, s, hI, hs) φ)
    (fun φ v ↦ b φ v) (spectralIsotypeConvolution_mkQ (F := F) a hI hs ω) (fun _ _ ↦ rfl)
  refine ⟨laws.1 0 (map_zero _), fun u v ↦ laws.2.1 _ u v (map_add _ _ _), ?_⟩
  intro t u v ht
  apply laws.2.2
  let ρ := hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs
  have hρ := (exists_hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).choose_spec.2
  have hconv := bruhatRegularizedAction_convolution μ𝔽 ρ hρ u v
  with_reducible obtain ⟨t', ht', hact⟩ := hconv
  have heq : t' = t := Subtype.ext (ht'.trans ht.symm)
  exact heq ▸ hact

private def spectralApprox_isotype_addHom (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    BruhatCompactSupport C𝔽 →+ (Qω(a, hI, hs, ω) →L[ℂ] Qω(a, hI, hs, ω)) where
  toFun := spectralIsotypeConvolution (F := F) a hI hs ω
  map_zero' := (spectralApprox_isotype_laws (F := F) a hI hs ω).1
  map_add' := (spectralApprox_isotype_laws (F := F) a hI hs ω).2.1

local notation "homTest(" ω ", " φ ")" =>
  ∀ (k : C₁) (x : C𝔽), (φ : BruhatCompactSupport C𝔽).val (k.val⁻¹ * x) =
    (ω k : ℂ) * (φ : BruhatCompactSupport C𝔽).val x

/-- Extend a real test to the positive half-line through the logarithm. Its support lies
in the exponential image of the original support, so the zero extension is smooth at zero. -/
private theorem spectralHomogeneousTest_real_factorization_log (f : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ Φ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧ tsupport Φ ⊆ Real.exp '' tsupport f ∧
      ∀ s, Φ (Real.exp s) = f s := by
  let Φ (y : ℝ) := if 0 < y then f (Real.log y) else 0
  have hK := hc.isCompact.image Real.continuous_exp
  have hs : tsupport Φ ⊆ Real.exp '' tsupport f := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_cases h : 0 < y
    · exact ⟨Real.log y, subset_tsupport f (by simpa [Φ, h, mem_support] using hy), Real.exp_log h⟩
    · exact ((mem_support.mp hy) (ite_eq_right h)).elim
  refine ⟨Φ, contDiff_iff_contDiffAt.mpr fun y ↦ ?_, hs, fun s ↦ by simp [Φ, Real.exp_pos]⟩
  by_cases h : 0 < y
  · apply (hf.contDiffAt.comp y (Real.contDiffAt_log.mpr h.ne')).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds h] with z hz using ite_eq_left hz
  · have hy : y ∉ tsupport Φ := fun hy ↦ by
      obtain ⟨s, _, rfl⟩ := hs hy
      exact h (Real.exp_pos s)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)

/-- Reflect the kernel of a translation integral and put the Haar normalization into it.
The resulting convolution is itself a smooth compactly supported test. -/
private theorem spectralHomogeneousTest_real_factorization_term
    (ν : Measure (Multiplicative ℝ)) [ν.IsHaarMeasure] (φ g : ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcg : HasCompactSupport g) :
    ∃ h : BruhatCompactSupport (Multiplicative ℝ),
      h ∈ AddSubmonoid.closure {h | ∃ u v : BruhatCompactSupport (Multiplicative ℝ),
        h.val = lcaConvolution ν u.val v.val} ∧
      ∀ s : ℝ, h.val (Multiplicative.ofAdd s) = ∫ t, φ t * g (s + t) := by
  let μ : Measure (Multiplicative ℝ) := (volume : Measure ℝ)
  let : IsFiniteMeasureOnCompacts μ :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
  let : μ.IsMulLeftInvariant :=
    ⟨fun y ↦ (measurePreserving_add_left (volume : Measure ℝ) y.toAdd).map_eq⟩
  let c := μ.haarScalarFactor ν
  have hμ : μ = c • ν := Measure.isMulLeftInvariant_eq_smul μ ν
  let k (t : ℝ) := φ (-t)
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := hφ.comp contDiff_neg
  have hck : HasCompactSupport k := hcφ.comp_homeomorph (Homeomorph.neg ℝ)
  let L := ContinuousLinearMap.mul ℝ ℂ
  let w := MeasureTheory.convolution k g L volume
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := hcg.contDiff_convolution_right L hk.continuous.locallyIntegrable hg
  have hcw : HasCompactSupport w := hck.convolution L hcg
  let h : BruhatCompactSupport (Multiplicative ℝ) :=
    ⟨w ∘ Multiplicative.toAdd, (mem_bruhatCompactSupportSubmodule_real_iff _).mpr ⟨hw, hcw⟩⟩
  let u : BruhatCompactSupport (Multiplicative ℝ) :=
    ⟨fun y ↦ (c : ℂ) * k y.toAdd, (mem_bruhatCompactSupportSubmodule_real_iff _).mpr
      ⟨contDiff_const.mul hk, hck.mul_left⟩⟩
  let v : BruhatCompactSupport (Multiplicative ℝ) :=
    ⟨g ∘ Multiplicative.toAdd, (mem_bruhatCompactSupportSubmodule_real_iff _).mpr ⟨hg, hcg⟩⟩
  refine ⟨h, AddSubmonoid.subset_closure ⟨u, v, funext fun s ↦ ?_⟩, fun s ↦ ?_⟩
  · let b (t : Multiplicative ℝ) := k t.toAdd * g (s.toAdd - t.toAdd)
    change (∫ t, b t ∂μ) = ∫ t, (c : ℂ) * k t.toAdd * g (-t.toAdd + s.toAdd) ∂ν
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, ← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun t ↦ by simp only [b, sub_eq_neg_add, mul_assoc]
  · change (∫ t : ℝ, φ (-t) * g (s - t)) = _
    simpa only [sub_eq_add_neg] using
      integral_neg_eq_self (fun t : ℝ ↦ φ t * g (s + t)) volume

/-- Classical input: the Dixmier–Malliavin factorization theorem on the additive real line,
from J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. 102 (1978), 307–330. Every smooth compactly supported
function is a finite sum of convolutions of such functions for the chosen Haar measure.
`mem_bruhatCompactSupportSubmodule_real_iff` identifies the tests here with those functions. -/
private theorem spectralHomogeneousTest_real_factorization
    (ν : Measure (Multiplicative ℝ)) [ν.IsHaarMeasure]
    (f : BruhatCompactSupport (Multiplicative ℝ)) :
    f ∈ AddSubmonoid.closure {h | ∃ u v : BruhatCompactSupport (Multiplicative ℝ),
      h.val = lcaConvolution ν u.val v.val} := by
  let g := f.val ∘ Multiplicative.ofAdd
  obtain ⟨hg, hc⟩ := (mem_bruhatCompactSupportSubmodule_real_iff _).mp f.property
  obtain ⟨Φ, hΦ, hΦs, hΦexp⟩ := spectralHomogeneousTest_real_factorization_log g hg hc
  have hΦc : HasCompactSupport Φ :=
    (hc.isCompact.image Real.continuous_exp).of_isClosed_subset (isClosed_tsupport _) hΦs
  obtain ⟨Φ₁, φ, ψ, h₁, hs₁, hφ, hψ, hsφ, hsψ, heq⟩ :=
    DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add (1 : ℝ) 1 zero_lt_one Φ hΦ hΦc
  have hc₁ : HasCompactSupport (Φ₁ ∘ Real.exp) := by
    apply HasCompactSupport.intro hc
    intro s hs
    change Φ₁ (Real.exp s) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro h
    obtain ⟨r, hr, he⟩ := hΦs (hs₁ h)
    exact hs (Real.exp_injective he ▸ hr)
  obtain ⟨u, hu, heu⟩ := spectralHomogeneousTest_real_factorization_term ν φ (Φ₁ ∘ Real.exp)
    hφ (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsφ) (h₁.comp Real.contDiff_exp) hc₁
  obtain ⟨v, hv, hev⟩ := spectralHomogeneousTest_real_factorization_term ν ψ g
    hψ (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsψ) hg hc
  have hf : f = u + v := by
    apply Subtype.ext
    funext s
    change g s.toAdd = u.val (Multiplicative.ofAdd s.toAdd) + v.val (Multiplicative.ofAdd s.toAdd)
    rw [heu, hev]
    simpa only [smul_eq_mul, mul_one, ← Real.exp_eq_exp_ℝ, ← Real.exp_add, hΦexp, comp_apply]
      using heq (Real.exp s.toAdd)
  exact hf ▸ AddSubmonoid.add_mem _ hu hv

/-- Restriction to a one-parameter subgroup is smooth in the real parameter. -/
private theorem spectralHomogeneousTest_section_smooth (σ : Multiplicative ℝ →ₜ* C𝔽)
    (f : bruhatSmoothSubmodule (G := C𝔽)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ f.val (σ (Multiplicative.ofAdd t))) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing f with
  | zero =>
    exact contDiff_zero.mpr ((continuous_of_bruhatSmooth
      ((mem_bruhatSmoothSubmodule_iff _).mp f.property)).comp σ.continuous)
  | succ n ih =>
    let d : bruhatSmoothSubmodule (G := C𝔽) :=
      ⟨bruhatDirectionalDeriv σ f.val, bruhatDirectionalDeriv_mem_smooth σ f⟩
    have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ f.val (σ (Multiplicative.ofAdd s)))
        (d.val (σ (Multiplicative.ofAdd t))) t := by
      have h := hasDerivAt_bruhatDirectionalDeriv σ
        ((mem_bruhatSmoothSubmodule_iff _).mp f.property 1) (σ (Multiplicative.ofAdd t))
      have hs := HasDerivAt.comp_sub_const t t (by simpa only [sub_self] using h)
      apply hs.congr_of_eventuallyEq (.of_forall fun s ↦ ?_)
      change f.val (σ (Multiplicative.ofAdd s)) =
        f.val (σ (Multiplicative.ofAdd t) * σ (Multiplicative.ofAdd (s - t)))
      rw [← map_mul, ← ofAdd_add, add_sub_cancel]
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun t ↦ (hd t).differentiableAt, fun h ↦ absurd h (by simp), ?_⟩
    rw [show deriv (fun t : ℝ ↦ f.val (σ (Multiplicative.ofAdd t))) =
      fun t ↦ d.val (σ (Multiplicative.ofAdd t)) from funext fun t ↦ (hd t).deriv]
    exact ih d

/-- A character times the pullback of a real-line test by the log norm is a Bruhat test. -/
private theorem spectralHomogeneousTest_lift_mem (hsur : Surjective m𝔽)
    (χ : PontryaginDual C𝔽) (f : BruhatCompactSupport (Multiplicative ℝ)) :
    (fun x : C𝔽 ↦ (χ x : ℂ) * f.val (positiveRealLogEquiv (m𝔽 x))) ∈
      bruhatCompactSupportSubmodule C𝔽 := by
  let L := (positiveRealLogEquiv : ℝ≥0ˣ →ₜ* Multiplicative ℝ).comp m𝔽
  have hp : IsProperMap L :=
    positiveRealLogEquiv.toHomeomorph.isProperMap.comp (isProperMap_ideleClassNorm F)
  have hc : HasCompactSupport (fun x : C𝔽 ↦ f.val (L x)) :=
    HasCompactSupport.intro (hp.isCompact_preimage f.property.2) fun _ hx ↦
      image_eq_zero_of_notMem_tsupport hx
  have hs := isBruhatSmooth_logProfile m𝔽
    ((mem_bruhatCompactSupportSubmodule_real_iff _).mp f.property).1
  have hval (x : C𝔽) : L x = Multiplicative.ofAdd (Real.log ((m𝔽 x).val : ℝ)) :=
    congrArg Multiplicative.ofAdd (positiveRealLogEquiv_apply _)
  let r : BruhatCompactSupport C𝔽 := ⟨fun x ↦ f.val (L x),
    (mem_bruhatSmoothSubmodule_iff _).mpr (by simpa only [hval, Function.comp_apply] using hs), hc⟩
  -- At weight zero the radial test is Schwartz, so it can be multiplied by the character.
  have hr := modulationWeight_mem_schwartzBruhat m𝔽 univ ⟨0, mem_univ _⟩
    ⟨r.val, bruhatCompactSupport_le_modulatedExponentialDecay m𝔽 univ hm𝔽 hsur r.property⟩
  rw [modulationWeight_zero] at hr
  obtain ⟨M, hM⟩ := schwartzBruhat_mul_unitaryCharacter χ
  let w := M (⟨r.val, hr⟩ : SchwartzBruhat C𝔽)
  have hw : w.val = fun x ↦ (χ x : ℂ) * f.val (L x) := funext (hM _)
  exact ⟨hw ▸ (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth w), hc.mul_left⟩

/-- The two character factors in the convolution integral multiply to `χ x`. The remaining
integrand factors through the log norm, so it integrates against the pushforward Haar measure. -/
private theorem spectralHomogeneousTest_lift_convolution (χ : PontryaginDual C𝔽)
    (u v : BruhatCompactSupport (Multiplicative ℝ)) (x : C𝔽) :
    let L := (positiveRealLogEquiv : ℝ≥0ˣ →ₜ* Multiplicative ℝ).comp m𝔽
    (χ x : ℂ) * lcaConvolution ((μ𝔽).map L) u.val v.val (L x) =
      lcaConvolution μ𝔽 (fun y ↦ (χ y : ℂ) * u.val (L y))
        (fun y ↦ (χ y : ℂ) * v.val (L y)) x := by
  intro L
  let b (t : Multiplicative ℝ) := u.val t * v.val (t⁻¹ * L x)
  have continuous_test (f : BruhatCompactSupport (Multiplicative ℝ)) : Continuous f.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp f.property.1)
  have hb : Continuous b := (continuous_test u).mul
    ((continuous_test v).comp (continuous_inv.mul continuous_const))
  change (χ x : ℂ) * (∫ t, b t ∂(μ𝔽).map L) = _
  rw [integral_map (φ := (L : C𝔽 → Multiplicative ℝ)) L.continuous.measurable.aemeasurable
    hb.aestronglyMeasurable, ← integral_const_mul]
  apply integral_congr_ae (.of_forall fun y ↦ ?_)
  change (χ x : ℂ) * (u.val (L y) * v.val ((L y)⁻¹ * L x)) =
    ((χ y : ℂ) * u.val (L y)) * ((χ (y⁻¹ * x) : ℂ) * v.val (L (y⁻¹ * x)))
  have hχ : (χ y : ℂ) * (χ (y⁻¹ * x) : ℂ) = (χ x : ℂ) := by
    rw [← Circle.coe_mul, ← map_mul, mul_inv_cancel_left]
  rw [map_mul L, map_inv, ← hχ]
  ring

/-- Paper: Theorems 10.3.1.1(3) and 10.3.2.1(3), pp. 449 and 454. A homogeneous
compactly supported Bruhat test is a finite sum of convolutions of pairs of tests
of the same character. Deviation: Isolate the radial Dixmier–Malliavin
factorization and its transport along the idelic norm. -/
private theorem spectralHomogeneousTest_convolution_factorization (ω : PontryaginDual C₁)
    (φ : BruhatCompactSupport C𝔽)
    (hφ : homTest(ω, φ)) :
    φ ∈ AddSubmonoid.closure {θ : BruhatCompactSupport C𝔽 |
      ∃ ψ η : BruhatCompactSupport C𝔽,
        homTest(ω, ψ) ∧ homTest(ω, η) ∧ θ.val = lcaConvolution μ𝔽 ψ.val η.val} := by
  let L := (positiveRealLogEquiv : ℝ≥0ˣ →ₜ* Multiplicative ℝ).comp m𝔽
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ := q.comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let σ := τ.comp (positiveRealLogEquiv.symm : Multiplicative ℝ →ₜ* ℝ≥0ˣ)
  have hσ (t : Multiplicative ℝ) : L (σ t) = t :=
    (congrArg positiveRealLogEquiv (hτ _)).trans (positiveRealLogEquiv.apply_symm_apply t)
  -- The inverse compact component gives the eigencharacter for left translation.
  let P : C𝔽 →ₜ* C𝔽 := (τ.comp m𝔽) / ContinuousMonoidHom.id C𝔽
  have hP (x : C𝔽) : P x ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (τ (ideleClassNorm F x) / x) = 1
    rw [map_div, hτ, div_self']
  let r : C𝔽 →ₜ* C₁ := ⟨P.toMonoidHom.codRestrict _ hP, P.continuous.subtype_mk _⟩
  let χ := ω.comp r
  have hk (k : C₁) : χ k.val⁻¹ = ω k := by
    apply congrArg ω
    apply Subtype.ext
    change τ (ideleClassNorm F k.val⁻¹) / k.val⁻¹ = k.val
    rw [map_inv, show ideleClassNorm F k.val = 1 from k.property, inv_one, map_one,
      one_div, inv_inv]
  let T : BruhatCompactSupport (Multiplicative ℝ) →+ BruhatCompactSupport C𝔽 :=
    { toFun := fun f ↦ ⟨fun x ↦ (χ x : ℂ) * f.val (L x),
        spectralHomogeneousTest_lift_mem hτ.surjective χ f⟩
      map_zero' := Subtype.ext (funext fun _ ↦ mul_zero _)
      map_add' := fun _ _ ↦ Subtype.ext (funext fun _ ↦ mul_add _ _ _) }
  have hT (f : BruhatCompactSupport (Multiplicative ℝ)) : homTest(ω, T f) := by
    intro k x
    have hL : L k.val = 1 :=
      (congrArg positiveRealLogEquiv k.property).trans (map_one _)
    change (χ (k.val⁻¹ * x) : ℂ) * f.val (L (k.val⁻¹ * x)) = _
    rw [map_mul, hk, Circle.coe_mul, map_mul, map_inv, hL, inv_one, one_mul, mul_assoc]
    rfl
  -- Homogeneity recovers the whole test from its restriction to the section.
  let f : BruhatCompactSupport (Multiplicative ℝ) := ⟨φ.val ∘ σ, (mem_bruhatCompactSupportSubmodule_real_iff _).mpr
    ⟨spectralHomogeneousTest_section_smooth σ ⟨φ.val, φ.property.1⟩,
      HasCompactSupport.intro (φ.property.2.image L.continuous) (fun t ht ↦
        show φ.val (σ (Multiplicative.ofAdd t)) = 0 from
          image_eq_zero_of_notMem_tsupport fun h ↦ ht ⟨_, h, hσ t⟩)⟩⟩
  have hφT : φ = T f := by
    apply Subtype.ext
    funext x
    have he : (r x).val⁻¹ * τ (m𝔽 x) = x := by
      change (τ (m𝔽 x) / x)⁻¹ * τ (m𝔽 x) = x
      rw [inv_div, div_mul_cancel]
    have h := hφ (r x) (τ (m𝔽 x))
    rw [he] at h
    change φ.val x = (ω (r x) : ℂ) *
      φ.val (τ (positiveRealLogEquiv.symm (positiveRealLogEquiv (m𝔽 x))))
    rwa [positiveRealLogEquiv.symm_apply_apply]
  let ν : Measure (Multiplicative ℝ) := (μ𝔽).map L
  have hp : IsProperMap L :=
    positiveRealLogEquiv.toHomeomorph.isProperMap.comp (isProperMap_ideleClassNorm F)
  have : ν.IsHaarMeasure := Measure.isHaarMeasure_map μ𝔽 L.toMonoidHom L.continuous
    (RightInverse.surjective hσ) (isProperMap_iff_tendsto_cocompact.mp hp).2
  rw [hφT, ← AddSubmonoid.mem_comap (f := T)]
  refine AddSubmonoid.closure_le.mpr ?_ (spectralHomogeneousTest_real_factorization ν f)
  rintro a ⟨u, v, huv⟩
  apply AddSubmonoid.mem_comap.mpr
  refine AddSubmonoid.subset_closure ⟨T u, T v, hT u, hT v, ?_⟩
  exact funext fun x ↦ (congrArg ((χ x : ℂ) * ·) (congrFun huv (L x))).trans
    (spectralHomogeneousTest_lift_convolution χ u v x)

/-- An additive convolution action transports finite factorizations to compositions. -/
private theorem spectralApprox_map_factorization {V O : Type*}
    [AddCommMonoid V] [AddCommMonoid O] (f : V →+ O) (p : V → Prop) (R : V → V → V → Prop)
    (m : O → O → O) (hm : ∀ t u v, R t u v → f t = m (f u) (f v))
    (t : V) (ht : t ∈ AddSubmonoid.closure {t | ∃ u v, p u ∧ p v ∧ R t u v}) :
    f t ∈ AddSubmonoid.closure {z | ∃ i j : Subtype p, z = m (f i.val) (f j.val)} := by
  induction ht using AddSubmonoid.closure_induction with
  | mem t h =>
    obtain ⟨u, v, hu, hv, h⟩ := h
    exact AddSubmonoid.subset_closure ⟨⟨u, hu⟩, ⟨v, hv⟩, hm _ _ _ h⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ hu hv => rw [map_add]; exact add_mem hu hv

set_option maxHeartbeats 800000 in
private theorem spectralApprox_isotype_rapid (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (hφ : homTest(ω, φ))
    (htrace : ∀ ψ : BruhatCompactSupport C𝔽, IsNuclearOperator (spectralConvolution (F := F) a hI hs ψ)) :
    let H := Qω(a, hI, hs, ω)
    let A : H →L[ℂ] H := spectralIsotypeConvolution (F := F) a hI hs ω φ
    ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n) atTop (𝓝 0) := by
  dsimp only
  let p := fun ψ : BruhatCompactSupport C𝔽 ↦ homTest(ω, ψ)
  let M := spectralApprox_isotype_addHom (F := F) a hI hs ω
  let A := fun i : Subtype p ↦ M i.val
  intro k
  refine spectralApprox_rapid_of_factorization (H := Qω(a, hI, hs, ω)) A ?_ ?_ ⟨φ, hφ⟩ k
  · intro i
    exact spectralApprox_isotype_nuclear (F := F) a hI hs ω i.val (htrace i.val)
  · intro i
    exact spectralApprox_map_factorization M p (fun θ ψ η ↦ θ.val = lcaConvolution μ𝔽 ψ.val η.val)
      ContinuousLinearMap.comp (spectralApprox_isotype_laws (F := F) a hI hs ω).2.2 i.val
      (spectralHomogeneousTest_convolution_factorization (F := F) ω i.val i.property)

end TestFactorization

section StripTraceCauchy

variable (a : ℝ)

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

/-- For included jets the finite section has exactly the convolution coordinate.
Consequently the difference of two sufficiently large sections lies in the orthogonal
complement of any fixed finite span of Riesz vectors. Finite diagonal sums for a
single section after this orthogonal projection bound its trace norm. -/
private theorem spectralStripConvolution_traceCauchy_of_compressed_diagonal
    {H J κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (B : ℕ × ℕ → H →L[ℂ] H) (Λ : J → StrongDual ℂ H)
    (b : HilbertBasis κ ℂ H) (hnuc : ∀ j, B j ∈ nuclearEndomorphisms H)
    (hcoord : ∀ k, ∀ᶠ j in atTop, ∀ v, Λ k (B j v) = Λ k (A v))
    (ht : ∀ ε > (0 : ℝ), ∃ S : Finset J, ∀ᶠ j in atTop, ∀ t : Finset κ,
      let V := Submodule.span ℂ ((fun k ↦ (InnerProductSpace.toDual ℂ H).symm (Λ k)) '' (S : Set J))
      ∑ n ∈ t, (inner ℂ (b n) (CFC.sqrt ((B j).adjoint * Vᗮ.starProjection * B j) (b n))).re ≤ ε) :
    SpectralRectanglesTraceCauchy B := by
  classical
  intro ε hε
  obtain ⟨S, hS⟩ := ht (ε / 3) (by positivity)
  let V := Submodule.span ℂ ((fun k ↦ (InnerProductSpace.toDual ℂ H).symm (Λ k)) '' (S : Set J))
  let P := Vᗮ.starProjection
  let D (j : ℕ × ℕ) : nuclearEndomorphisms H :=
    ⟨P * B j, mul_mem_nuclearEndomorphisms_left P ⟨B j, hnuc j⟩⟩
  have hgram (j : ℕ × ℕ) : (D j).val.adjoint * (D j).val = (B j).adjoint * P * B j := by
    change star (P * B j) * (P * B j) = star (B j) * P * B j
    have hP : IsStarProjection P := isStarProjection_starProjection
    rw [star_mul, hP.isSelfAdjoint.star_eq, ← mul_assoc, mul_assoc (star (B j)), hP.isIdempotentElem.eq]
  have hnorm : ∀ᶠ j in atTop, traceNorm (D j) ≤ ε / 3 := by
    filter_upwards [hS] with j hj
    apply le_of_tendsto' (hasSum_traceNorm_diagonal b (D j))
    intro t
    simpa only [hgram] using hj t
  have hScoord : ∀ᶠ j in atTop, ∀ k ∈ S, ∀ v, Λ k (B j v) = Λ k (A v) :=
    S.eventually_all.mpr fun k _ ↦ hcoord k
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (hnorm.and hScoord)
  refine ⟨j₀, fun j k hj hk ↦ ⟨D j - D k, ?_, ?_⟩⟩
  · ext v
    change P (B j v) - P (B k v) = B j v - B k v
    rw [← map_sub]
    apply Submodule.starProjection_eq_self_iff.mpr
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      rw [InnerProductSpace.toDual_symm_apply, map_sub, (hj₀ j hj).2 r hr v, (hj₀ k hk).2 r hr v,
        sub_self]
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  · let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
    have hc := traceNorm_normedSpaceCore (H := H)
    have hneg : traceNorm (-(D k)) = traceNorm (D k) := by
      rw [← neg_one_smul ℂ (D k)]
      simpa only [norm_neg, norm_one, one_mul] using hc.norm_smul (-1 : ℂ) (D k)
    have htr := hc.norm_triangle (D j) (-(D k))
    change traceNorm (D j + -(D k)) ≤ traceNorm (D j) + traceNorm (-(D k)) at htr
    rw [← sub_eq_add_neg, hneg] at htr
    linarith [(hj₀ j hj).1, (hj₀ k hk).1]

/-- Pointwise square-root identity from AppC_LCTVS/Sec3a, used for compression
and for the contraction which attains the trace norm. -/
private theorem spectralStripConvolution_traceCauchy_abs_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (X : H →L[ℂ] H) (v : H) : ‖CFC.sqrt (X.adjoint * X) v‖ = ‖X v‖ := by
  let S := CFC.sqrt (X.adjoint * X)
  have hpos : 0 ≤ S := CFC.sqrt_nonneg _
  have ha := (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).isSelfAdjoint.adjoint_eq
  have hsq : S * S = X.adjoint * X :=
    CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr X.isPositive_adjoint_comp_self)
  change ‖S v‖ = ‖X v‖
  rw [S.apply_norm_eq_sqrt_inner_adjoint_right, X.apply_norm_eq_sqrt_inner_adjoint_right, ha,
    ← ContinuousLinearMap.mul_def, hsq, ContinuousLinearMap.mul_def]

/-- The two orthogonal output compressions satisfy a weighted trace-norm bound.
This follows from the Pythagorean identity on each input vector and operator
monotonicity of the positive square root. -/
private theorem spectralStripConvolution_traceCauchy_compression_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) [V.HasOrthogonalProjection] (T : nuclearEndomorphisms H)
    {d : ℝ} (hd : 0 ≤ d) :
    let left (P : H →L[ℂ] H) := (⟨P * T.val, mul_mem_nuclearEndomorphisms_left P T⟩ :
      nuclearEndomorphisms H)
    traceNorm (left V.starProjection) + d * traceNorm (left Vᗮ.starProjection) ≤
      (1 + d ^ 2) * traceNorm T := by
  intro left
  let absOp (X : H →L[ℂ] H) := CFC.sqrt (X.adjoint * X)
  let A := left V.starProjection
  let B := left Vᗮ.starProjection
  let Y := absOp A.val + d • absOp B.val
  let c := 1 + d ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have bound (v : H) : ‖Y v‖ ≤ ‖(c • T.val) v‖ := by
    have hp := V.norm_sq_eq_add_norm_sq_starProjection (T.val v)
    change ‖T.val v‖ ^ 2 = ‖A.val v‖ ^ 2 + ‖B.val v‖ ^ 2 at hp
    calc
      ‖Y v‖ ≤ ‖absOp A.val v‖ + ‖d • absOp B.val v‖ := norm_add_le _ _
      _ = ‖A.val v‖ + d * ‖B.val v‖ := by
        simp only [absOp, norm_smul, Real.norm_of_nonneg hd, spectralStripConvolution_traceCauchy_abs_norm]
      _ ≤ c * ‖T.val v‖ := by
        apply le_of_sq_le_sq _ (mul_nonneg hc (norm_nonneg _))
        calc
          _ ≤ (1 + d ^ 2) * (‖A.val v‖ ^ 2 + ‖B.val v‖ ^ 2) := by
            nlinarith [sq_nonneg (d * ‖A.val v‖ - ‖B.val v‖)]
          _ ≤ (c * ‖T.val v‖) ^ 2 := by
            rw [← hp, mul_pow]
            exact mul_le_mul_of_nonneg_right (by dsimp [c]; nlinarith [sq_nonneg d, sq_nonneg (d^2)])
              (sq_nonneg _)
      _ = ‖(c • T.val) v‖ := by simp [norm_smul, Real.norm_of_nonneg hc]
  have hY : 0 ≤ Y := add_nonneg (CFC.sqrt_nonneg (A.val.adjoint * A.val))
    (smul_nonneg hd (CFC.sqrt_nonneg (B.val.adjoint * B.val)))
  have hle := CFC.sqrt_le_sqrt _ _ ((ContinuousLinearMap.norm_map_le_norm_map_iff_le _ _).mp bound)
  change CFC.abs Y ≤ CFC.abs ((c : ℂ) • T.val) at hle
  rw [CFC.abs_of_nonneg Y hY, CFC.abs_smul, Complex.norm_real, Real.norm_of_nonneg hc] at hle
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  refine hasSum_le (fun i ↦ ?_)
    ((hasSum_traceNorm_diagonal b A).add ((hasSum_traceNorm_diagonal b B).mul_left d))
    ((hasSum_traceNorm_diagonal b T).mul_left c)
  have h := (ContinuousLinearMap.le_def.mp hle).re_inner_nonneg_right (b i)
  simpa [Y, absOp, CFC.abs, ContinuousLinearMap.star_eq_adjoint, inner_sub_right,
    inner_add_right, inner_smul_right_eq_smul, sub_nonneg] using h

/-- A finite block sum nearly attaining the common bound leaves little trace norm
for disjoint sums. A finite span of moments detects the almost maximal sum and is
orthogonal to every block outside a fixed finite set. -/
private theorem spectralStripConvolution_traceCauchy_bounded_tails
    {H J Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : Z → nuclearEndomorphisms H) (V : Finset J → Submodule ℂ H)
    [∀ S, (V S).HasOrthogonalProjection]
    (hcap : ∀ K : Finset Z, ∀ η > (0 : ℝ), ∃ S : Finset J,
      traceNorm ⟨(V S)ᗮ.starProjection * (∑ z ∈ K, R z).val,
        mul_mem_nuclearEndomorphisms_left _ _⟩ < η)
    (hoff : ∀ S, ∃ F : Finset Z, ∀ K : Finset Z, Disjoint K F →
      (V S)ᗮ.starProjection * (∑ z ∈ K, R z).val = (∑ z ∈ K, R z).val)
    (hbound : BddAbove (range fun K : Finset Z ↦ traceNorm (∑ z ∈ K, R z))) :
    ∀ ε > (0 : ℝ), ∃ F : Finset Z, ∀ K : Finset Z, Disjoint K F →
      traceNorm (∑ z ∈ K, R z) < ε := by
  classical
  intro ε hε
  let n (K : Finset Z) := traceNorm (∑ z ∈ K, R z)
  let M := ⨆ K, n K
  have upper (K : Finset Z) : n K ≤ M := le_ciSup hbound K
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let core := (traceNorm_normedSpaceCore (H := H)).toCore
  have hM : 0 ≤ M := (core.norm_nonneg (∑ z ∈ (∅ : Finset Z), R z)).trans (upper ∅)
  let d := min 1 (ε / (4 * (M + 1)))
  have hd : 0 < d := lt_min one_pos (div_pos hε (by positivity))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdM : d * M ≤ ε / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (M + 1))).mp (min_le_right 1 (ε / (4 * (M + 1))))
    change d * (4 * (M + 1)) ≤ ε at h
    linarith
  let η := d * ε / 8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK⟩ : ∃ K, M - η < n K := exists_lt_of_lt_ciSup (show M - η < M by linarith)
  obtain ⟨S, hS⟩ := hcap K η hη
  obtain ⟨F, hF⟩ := hoff S
  refine ⟨K ∪ F, ?_⟩
  intro L hL
  let X := ∑ z ∈ K, R z
  let Y := ∑ z ∈ L, R z
  let P := (V S).starProjection
  let Q := (V S)ᗮ.starProjection
  let left (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) : nuclearEndomorphisms H :=
    ⟨A * T.val, mul_mem_nuclearEndomorphisms_left _ _⟩
  have hQ : Q = 1 - P := (V S).starProjection_orthogonal'
  have hQY : Q * Y.val = Y.val := hF L (Finset.disjoint_union_right.mp hL).2
  have hPY : P * Y.val = 0 := by rwa [hQ, sub_mul, one_mul, sub_eq_self] at hQY
  have hX : left P (X + Y) + left Q X = X := by
    apply Subtype.ext
    change P * (X.val + Y.val) + Q * X.val = X.val
    rw [mul_add, hPY, add_zero, hQ, sub_mul, one_mul]
    abel
  have hY : left Q (X + Y) - left Q X = Y := by
    apply Subtype.ext
    change Q * (X.val + Y.val) - Q * X.val = Y.val
    rw [mul_add, hQY, add_sub_cancel_left]
  -- The head of X + Y still sees almost M. The common bound on X + Y then limits its tail.
  have bound := spectralStripConvolution_traceCauchy_compression_bound (V S) (X + Y) hd.le
  change traceNorm (left P (X + Y)) + d * traceNorm (left Q (X + Y)) ≤ _ at bound
  have hXY : traceNorm (X + Y) ≤ M := by
    simpa only [n, Finset.sum_union (Finset.disjoint_union_right.mp hL).1.symm] using upper (K ∪ L)
  have hnX : n K ≤ traceNorm (left P (X + Y)) + traceNorm (left Q X) := by
    change ‖X‖ ≤ _
    calc
      ‖X‖ = ‖left P (X + Y) + left Q X‖ := congrArg norm hX.symm
      _ ≤ _ := core.norm_triangle _ _
  have hnY : traceNorm Y ≤ traceNorm (left Q (X + Y)) + traceNorm (left Q X) :=
    calc
      ‖Y‖ = ‖left Q (X + Y) - left Q X‖ := congrArg norm hY.symm
      _ ≤ _ := by
        have hneg : traceNorm (-(left Q X)) = traceNorm (left Q X) := by
          rw [← neg_one_smul ℂ (left Q X)]
          simpa only [norm_neg, norm_one, one_mul] using core.norm_smul (-1 : ℂ) (left Q X)
        change traceNorm (_ - _) ≤ _
        rw [sub_eq_add_neg, ← hneg]
        exact core.norm_triangle _ _
  change traceNorm (left Q X) < η at hS
  change traceNorm Y < ε
  by_contra! hbad
  have small := mul_le_mul_of_nonneg_left hdM hd.le
  have cost := mul_le_mul_of_nonneg_left hXY (by positivity : 0 ≤ 1 + d ^ 2)
  have hscaled := mul_le_mul_of_nonneg_left (hbad.trans hnY) hd.le
  have herror := mul_le_mul_of_nonneg_right hd1 (core.norm_nonneg (left Q X))
  change d * traceNorm (left Q X) ≤ 1 * traceNorm (left Q X) at herror
  dsimp only [η] at hK hS
  nlinarith only [bound, cost, small, hscaled, herror, hnX, hK, hS, mul_pos hd hε]

/-- Every selected block takes values in the span of its finitely many jet vectors. -/
private theorem spectralStripConvolution_traceCauchy_finiteRank
    {H J Z : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (L : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) :
    FiniteDimensional ℂ (spectralConvolutionFiniteSum A x Λ L N jet).toLinearMap.range := by
  classical
  let Y := (L.sigma fun z ↦ (Finset.univ : Finset (Fin (N z)))).image (fun p ↦ x (jet p.1 p.2))
  let W := Submodule.span ℂ (Y : Set H)
  let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ Y.finite_toSet
  apply Submodule.finiteDimensional_of_le (S₂ := W)
  rintro _ ⟨v, rfl⟩
  change spectralConvolutionFiniteSum A x Λ L N jet v ∈ W
  simp only [spectralConvolutionFiniteSum, sum_apply, ContinuousLinearMap.smulRight_apply]
  refine W.sum_mem fun z hz ↦ W.sum_mem fun m _ ↦ W.smul_mem _ (Submodule.subset_span ?_)
  exact Finset.mem_image.mpr ⟨⟨z, m⟩, Finset.mem_sigma.mpr ⟨hz, Finset.mem_univ _⟩, rfl⟩

/-- Biorthogonality identifies the blocks missed by any finite set of moments.
Totality makes the complementary projections strongly null, hence small in
trace norm on any fixed finite section. -/
private theorem spectralStripConvolution_traceCauchy_of_bounded_blocks
    {H J Z κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) (row : J → Z) (hr : ∀ z m, row (jet z m) = z)
    (K : ℕ × ℕ → Finset Z) (hK : ∀ z, ∀ᶠ j in atTop, z ∈ K j) (b : HilbertBasis κ ℂ H)
    (R : Z → nuclearEndomorphisms H)
    (hR : ∀ L : Finset Z, (∑ z ∈ L, R z).val = spectralConvolutionFiniteSum A x Λ L N jet)
    (hbound : BddAbove (range fun L : Finset Z ↦ traceNorm (∑ z ∈ L, R z))) :
    ∀ ε > (0 : ℝ), ∃ S : Finset J, ∀ᶠ j in atTop, ∀ t : Finset κ,
      let V := Submodule.span ℂ ((fun k ↦ (InnerProductSpace.toDual ℂ H).symm (Λ k)) '' (S : Set J))
      let B := spectralConvolutionFiniteSum A x Λ (K j) N jet
      ∑ i ∈ t, (inner ℂ (b i) (CFC.sqrt (B.adjoint * Vᗮ.starProjection * B) (b i))).re ≤ ε := by
  classical
  let u (k : J) := (InnerProductSpace.toDual ℂ H).symm (Λ k)
  let V (S : Finset J) := Submodule.span ℂ (u '' (S : Set J))
  let dim (S : Finset J) : FiniteDimensional ℂ (V S) :=
    FiniteDimensional.span_of_finite ℂ (S.finite_toSet.image u)
  let Q (S : Finset J) := (V S)ᗮ.starProjection
  have hQ (v : H) : Tendsto (fun S ↦ Q S v) atTop (𝓝 0) := by
    have hd : ⊤ ≤ (⨆ S, V S).topologicalClosure := by
      apply (Submodule.topologicalClosure_eq_top_iff.mpr ?_).ge
      rw [Submodule.eq_bot_iff]
      intro w hw
      have he : ContinuousLinearMap.apply ℂ ℂ w = 0 := by
        apply ContinuousLinearMap.ext_on hb.2.2.2
        rintro _ ⟨k, rfl⟩
        have hm : u k ∈ V {k} := Submodule.subset_span ⟨k, Finset.mem_singleton_self k, rfl⟩
        have h := (Submodule.mem_orthogonal _ _).mp hw _ (le_iSup V {k} hm)
        change Λ k w = 0
        simpa only [u, InnerProductSpace.toDual_symm_apply] using h
      have hz := congrArg (fun f : StrongDual ℂ H →L[ℂ] ℂ ↦ f (InnerProductSpace.toDual ℂ H w)) he
      exact inner_self_eq_zero.mp hz
    have hm : Monotone V := fun _ _ h ↦ Submodule.span_mono (image_mono h)
    have h := tendsto_const_nhds (x := v) |>.sub (Submodule.starProjection_tendsto_self V hm v hd)
    simpa only [Q, Submodule.starProjection_orthogonal_val, sub_self] using h
  let B (L : Finset Z) := ∑ z ∈ L, R z
  let left (S : Finset J) (T : nuclearEndomorphisms H) : nuclearEndomorphisms H :=
    ⟨Q S * T.val, mul_mem_nuclearEndomorphisms_left _ _⟩
  have capture (L : Finset Z) (η : ℝ) (hη : 0 < η) : ∃ S, traceNorm (left S (B L)) < η := by
    have hdim : FiniteDimensional ℂ (B L).val.toLinearMap.range := by
      change FiniteDimensional ℂ (∑ z ∈ L, R z).val.toLinearMap.range
      rw [hR]
      exact spectralStripConvolution_traceCauchy_finiteRank A x Λ L N jet
    obtain ⟨_, hlim⟩ := tendsto_traceNorm_mul_finiteRank Q hQ (B L).val
      hdim
    exact (hlim.eventually_lt_const hη).exists
  have off (S : Finset J) : ∃ F : Finset Z, ∀ L : Finset Z, Disjoint L F →
      Q S * (B L).val = (B L).val := by
    refine ⟨S.image row, ?_⟩
    intro L hL
    ext v
    apply Submodule.starProjection_eq_self_iff.mpr
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      change inner ℂ (u k) ((B L).val v) = 0
      rw [show inner ℂ (u k) ((B L).val v) = Λ k ((B L).val v) from InnerProductSpace.toDual_symm_apply]
      change Λ k ((∑ z ∈ L, R z).val v) = 0
      rw [hR]
      simp only [spectralConvolutionFiniteSum, sum_apply, map_sum, ContinuousLinearMap.smulRight_apply, map_smul]
      refine Finset.sum_eq_zero fun z hz ↦ Finset.sum_eq_zero fun m _ ↦ ?_
      have hne : jet z m ≠ k := by
        intro h
        exact (Finset.disjoint_left.mp hL hz)
          (Finset.mem_image.mpr ⟨k, hk, (congrArg row h).symm.trans (hr z m)⟩)
      rw [hb.2.1 _ _ hne, smul_zero]
    | zero => exact inner_zero_left _
    | add y w _ _ hy hw => rw [inner_add_left, hy, hw, add_zero]
    | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]
  intro ε hε
  obtain ⟨F, hF⟩ := spectralStripConvolution_traceCauchy_bounded_tails R V capture off hbound _ (half_pos hε)
  obtain ⟨S, hS⟩ := capture F _ (half_pos hε)
  refine ⟨S, ?_⟩
  filter_upwards [F.eventually_all.mpr (fun z _ ↦ hK z)] with j hj
  let T := B (K j \ F)
  have heq : left S (B (K j)) = left S T + left S (B F) := by
    have hadd : B (K j) = T + B F := (Finset.sum_sdiff (f := R) (show F ⊆ K j from hj)).symm
    rw [hadd]
    exact Subtype.ext (mul_add _ _ _)
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let core := (traceNorm_normedSpaceCore (H := H)).toCore
  have hsmall : traceNorm (left S (B (K j))) ≤ ε := by
    have hc := (traceNorm_mul_left_le (Q S) T).trans
      (mul_le_of_le_one_left (core.norm_nonneg T) (V S)ᗮ.starProjection_norm_le)
    rw [heq]
    exact (core.norm_triangle _ _).trans ((add_le_add (hc.trans (hF _ Finset.sdiff_disjoint).le)
      hS.le).trans_eq (add_halves ε))
  intro t
  let D := left S (B (K j))
  have hs := hasSum_traceNorm_diagonal b D
  have hpos (i : κ) : 0 ≤ (inner ℂ (b i) (CFC.sqrt (D.val.adjoint * D.val) (b i))).re :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg (D.val.adjoint * D.val))).re_inner_nonneg_right _
  have hsum := hs.summable.sum_le_tsum t fun i _ ↦ hpos i
  rw [hs.tsum_eq] at hsum
  have gram : D.val.adjoint * D.val = (B (K j)).val.adjoint * Q S * (B (K j)).val := by
    change star (Q S * _) * (Q S * _) = star _ * Q S * _
    have hp : IsStarProjection (Q S) := isStarProjection_starProjection
    rw [star_mul, hp.isSelfAdjoint.star_eq, ← mul_assoc, mul_assoc (star _), hp.isIdempotentElem.eq]
  simpa only [gram, B, hR] using hsum.trans hsmall

/-- A finite-rank operator attains its trace norm against a compact contraction.
Use the contraction taking the operator to its absolute value and restrict it
to the finite-dimensional range. -/
private theorem spectralStripConvolution_traceCauchy_norming
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (hdim : FiniteDimensional ℂ T.val.toLinearMap.range) :
    ∃ U : compactOperator (RingHom.id ℂ) H H, ‖U‖ ≤ 1 ∧
      traceNorm T = (hilbertTrace ⟨U.val * T.val, mul_mem_nuclearEndomorphisms_left _ T⟩).re := by
  let W := T.val.toLinearMap.range
  let B := CFC.sqrt (T.val.adjoint * T.val)
  obtain ⟨C, hC, hCB⟩ := exists_contraction_comp_eq_of_norm_le T.val B
    fun v ↦ (spectralStripConvolution_traceCauchy_abs_norm T.val v).le
  let U : compactOperator (RingHom.id ℂ) H H := ⟨C * W.starProjection,
    (isCompactOperator_of_locallyCompactSpace_rng (C.comp W.subtypeL)).comp_clm W.orthogonalProjectionOnto⟩
  refine ⟨U, (norm_mul_le C W.starProjection).trans
    ((mul_le_of_le_one_right (norm_nonneg _) W.starProjection_norm_le).trans hC), ?_⟩
  have hUB : U.val * T.val = B := by
    ext v
    change C (W.starProjection (T.val v)) = B v
    rw [Submodule.starProjection_eq_self_iff.mpr (show T.val v ∈ W from ⟨v, rfl⟩)]
    exact congrArg (fun L : H →L[ℂ] H ↦ L v) hCB
  let D : nuclearEndomorphisms H := ⟨U.val * T.val, mul_mem_nuclearEndomorphisms_left _ T⟩
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  have h := Complex.reCLM.hasSum (summable_norm_hilbertDiagonal b D.val D.property).of_norm.hasSum
  change HasSum (fun i ↦ (inner ℂ (b i) ((U.val * T.val) (b i))).re) (hilbertTrace D).re at h
  rw [hUB] at h
  exact (hasSum_traceNorm_diagonal b T).unique h

/-- Pointwise summability of the block traces against compact operators gives
one trace-norm bound for all finite selections, by uniform boundedness on the
Banach space of compact operators. -/
private theorem spectralStripConvolution_traceCauchy_scalar_bound
    {H J Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (h : ∀ U : compactOperator (RingHom.id ℂ) H H,
      Summable (fun z ↦ ∑ m : Fin (N z), Λ (jet z m) (A (U.val (x (jet z m)))))) :
    ∃ R : Z → nuclearEndomorphisms H,
      (∀ K : Finset Z, (∑ z ∈ K, R z).val = spectralConvolutionFiniteSum A x Λ K N jet) ∧
      BddAbove (range fun K : Finset Z ↦ traceNorm (∑ z ∈ K, R z)) := by
  classical
  let f (j : J) := (Λ j).comp A
  let term (j : J) (y : H) : nuclearEndomorphisms H :=
    ⟨(f j).smulRight y, smulRight_mem_nuclearEndomorphisms _ _⟩
  let R (z : Z) := ∑ m, term (jet z m) (x (jet z m))
  have hR (K : Finset Z) : (∑ z ∈ K, R z).val = spectralConvolutionFiniteSum A x Λ K N jet := by
    simp only [R, Submodule.coe_sum, term, f, spectralConvolutionFiniteSum]
  refine ⟨R, hR, ?_⟩
  let C := compactOperator (RingHom.id ℂ) H H
  let : CompleteSpace C := (show IsClosed (C : Set (H →L[ℂ] H)) from
    isClosed_setOfPred_isCompactOperator).completeSpace_coe
  let eval (j : J) := (f j).comp ((ContinuousLinearMap.apply ℂ H (x j)).comp C.subtypeL)
  let test (K : Finset Z) := ∑ z ∈ K, ∑ m, eval (jet z m)
  obtain ⟨c, hc⟩ := banach_steinhaus (g := test) (fun U ↦ by
    refine ⟨∑' z, ‖∑ m, Λ (jet z m) (A (U.val (x (jet z m))))‖, fun K ↦ ?_⟩
    simp only [test, sum_apply]
    exact (norm_sum_le _ _).trans ((h U).norm.sum_le_tsum K fun _ _ ↦ norm_nonneg _))
  refine ⟨c, ?_⟩
  rintro _ ⟨K, rfl⟩
  let T := ∑ z ∈ K, R z
  have hd : FiniteDimensional ℂ T.val.toLinearMap.range := by
    dsimp only [T]
    rw [hR]
    exact spectralStripConvolution_traceCauchy_finiteRank A x Λ K N jet
  obtain ⟨U, hU, hnorm⟩ := spectralStripConvolution_traceCauchy_norming T hd
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  let D : nuclearEndomorphisms H := ⟨U.val * T.val, mul_mem_nuclearEndomorphisms_left _ T⟩
  have heq : D = ∑ z ∈ K, ∑ m, term (jet z m) (U.val (x (jet z m))) := by
    apply Subtype.ext
    ext v
    change U.val (T.val v) = _
    simp only [T, R, term, Submodule.coe_sum, sum_apply, ContinuousLinearMap.smulRight_apply,
      map_sum, map_smul]
  have ht : hilbertTrace D = test K U := by
    rw [← htr, heq]
    simp only [map_sum]
    simp only [htr, term, hilbertTrace_smulRight, test, sum_apply]
    rfl
  change traceNorm T ≤ c
  rw [hnorm, show hilbertTrace ⟨U.val * T.val, _⟩ = test K U from ht]
  exact (Complex.re_le_norm _).trans (((test K).le_opNorm U).trans
    ((mul_le_of_le_one_right (norm_nonneg _) hU).trans (hc K)))

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. After inserting any fixed compact
operator on the biorthogonal vectors, the scalar traces of the individual zero
blocks are summable. The jets at each zero are summed before testing summability.
The estimates for (10.3.2.7) involve only Mellin derivatives and give no bound for these
pairings with a compact operator. A summable majorant for the absolute block
traces, allowed to depend on the operator and test, would suffice.
Reconstruction: The paper does not state this. It is the project's formulation of what the
trace-norm estimates of Theorems 10.3.1.1(1) and 10.3.2.1(1) need, and it is not known whether
it is what the author intends.
Gap: The estimates on pp. 454–455 bound Mellin derivatives only. No bound for the block traces
against an arbitrary compact operator, allowing clusters of zeros, is supplied or known to us. -/
private theorem spectralStripConvolution_traceCauchy_compact_block_series (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
    let jet (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))) :
        SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
      ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
    ∀ U : compactOperator (RingHom.id ℂ) H H,
      Summable (fun z : Z(χ, α) ↦ ∑ m, Λ (jet z m) (A (U.val (x (jet z m))))) := by
  sorry

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455, after (10.3.2.7). For a fixed test,
discard the output directions of finitely many jets. The positive square root of
the remaining Gram operator should have uniformly small finite diagonal sums.
By `_hb` the Riesz vectors span densely, so the complementary projections tend strongly to
zero and compress any fixed finite-rank rectangle to zero in trace norm. In a trace-norm
Cauchy tail, contractivity bounds each later compressed trace norm, and hence each finite
diagonal sum, by the fixed rectangle's compressed trace norm plus the tail error.
Gap: The scalar Mellin estimates on p. 455 do not control this sum for an
individual rectangle, in particular when its boundary separates nearby zeros. -/
private theorem spectralStripConvolution_traceCauchy_compressed_diagonal (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ, α) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    {κ : Type*} (b : HilbertBasis κ ℂ Q(a, hStrip(hα), hs₀(hs))) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, α, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)
    let diagonal {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
        {J : Type _} (forms : J → StrongDual ℂ E) (S : Finset J) (D : E →L[ℂ] E) (v : E) :=
      let V := Submodule.span ℂ ((fun k ↦ (InnerProductSpace.toDual ℂ E).symm (forms k)) '' (S : Set J))
      (inner ℂ v (CFC.sqrt (D.adjoint * Vᗮ.starProjection * D) v)).re
    ∀ ε > (0 : ℝ), ∃ S : Finset (SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s),
      ∀ᶠ j in atTop, ∀ t : Finset κ, ∑ n ∈ t, diagonal Λ S (B j) (b n) ≤ ε := by
  classical
  intro H A B diagonal
  let count (z : Z(χ, α)) := N(χ, α, s, z)
  let jet (z : Z(χ, α)) (m : Fin (count z)) :
      SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let row (j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s) : Z(χ, α) :=
    ⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩
  obtain ⟨R, hR, hbound⟩ := spectralStripConvolution_traceCauchy_scalar_bound A x Λ count jet
    (spectralStripConvolution_traceCauchy_compact_block_series a χ _hχ hα hs φ x Λ _hb _hj)
  apply spectralStripConvolution_traceCauchy_of_bounded_blocks A x Λ _hb count jet row
    (fun _ _ ↦ rfl) (fun ij : ℕ × ℕ ↦
      ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn) _ b R hR hbound
  intro z
  filter_upwards [eventually_ge_atTop (e z)] with ij hij
  simpa using (show (e z).1 ≤ ij.1 ∧ (e z).2 ≤ ij.2 from hij)

/-- Paper: Theorem 10.3.2.1(1), p. 453. The rectangular sums have Cauchy tails in trace norm.
Gap: Trace-norm tails must control close zeros and high jet orders in the strip norm.
A strip component with bounded central-line frequency support vanishes by holomorphy. -/
theorem spectralStripConvolution_traceCauchy (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ, α) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, α, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)
    SpectralRectanglesTraceCauchy B := by
  classical
  intro H A B
  let count (z : Z(χ, α)) := N(χ, α, s, z)
  let jet (z : Z(χ, α)) (m : Fin (count z)) : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let index (j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s) : (z : Z(χ, α)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩, ⟨j.val.2.2.2, j.property⟩⟩
  let eqv : ((z : Z(χ, α)) × Fin (count z)) ≃ SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  apply spectralStripConvolution_traceCauchy_of_compressed_diagonal A B Λ b
  · intro j
    exact (nuclearEndomorphisms H).sum_mem fun z _ ↦
      (nuclearEndomorphisms H).sum_mem fun m _ ↦ smulRight_mem_nuclearEndomorphisms _ _
  · intro r
    obtain ⟨⟨z, m⟩, rfl⟩ := eqv.surjective r
    filter_upwards [eventually_ge_atTop (e z)] with j hj
    exact spectralConvolutionFiniteSum_limit_of_traceCauchy_coordinate A x Λ _ count jet _hb eqv.injective
      z (by simpa using (show (e z).1 ≤ j.1 ∧ (e z).2 ≤ j.2 from hj)) m
  · exact spectralStripConvolution_traceCauchy_compressed_diagonal (F := F) a χ _hχ hα hs φ
      eχ e _he x Λ _hb _hj b

end StripTraceCauchy

section Line

variable (a : ℝ)

local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ // 0 < order(χ z.1, shift(a, z.2))}
local notation "N(" χ ", " s ", " z ")" => spectralBoundaryMultiplicity s (mult(χ (z).val.1,
  shift(a, (z).val.2)))

/-- Relabeling a biorthogonal system by a bijection preserves its two dense spans. -/
private theorem spectralLineConvolution_traceCauchy_reindexBasis
    {I J E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (r : J ≃ I)
    (x : I → E) (f : I → StrongDual ℂ E) (h : IsSpectralMarkushevichBasis x f) :
    IsSpectralMarkushevichBasis (x ∘ r) (f ∘ r) := by
  refine ⟨fun j ↦ h.1 (r j), fun i j hij ↦ h.2.1 _ _ (r.injective.ne hij), ?_, ?_⟩
  · simpa only [r.surjective.range_comp] using h.2.2.1
  · simpa only [r.surjective.range_comp] using h.2.2.2

/-- Relabeling both zeros and their derivative indices leaves each finite rectangle unchanged. -/
private theorem spectralLineConvolution_traceCauchy_reindexSum
    {I J Z W E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (r : J ≃ I) (u : W ≃ Z) (e : Z ↪ ℕ × ℕ) (A : E →L[ℂ] E)
    (x : I → E) (f : I → StrongDual ℂ E) (N : Z → ℕ) (M : W → ℕ)
    (i : (z : Z) → Fin (N z) → I) (j : (w : W) → Fin (M w) → J)
    (hN : ∀ w, M w = N (u w)) (hj : ∀ w m, r (j w m) = i (u w) (Fin.cast (hN w) m))
    (k : Finset (ℕ × ℕ)) :
    spectralConvolutionFiniteSum A (x ∘ r) (f ∘ r)
      (k.preimage (u.toEmbedding.trans e) (u.toEmbedding.trans e).injective.injOn) M j =
    spectralConvolutionFiniteSum A x f (k.preimage e e.injective.injOn) N i := by
  unfold spectralConvolutionFiniteSum
  apply Finset.sum_equiv u (fun _ ↦ Finset.mem_preimage.trans Finset.mem_preimage.symm)
  intro w _
  apply Fintype.sum_equiv (finCongr (hN w))
  intro m
  simp only [Function.comp_apply, hj, finCongr_apply]

/-- Paper: Theorem 10.3.1.1(1), p. 448. The rectangular sums have Cauchy tails in trace norm.
At width zero every strip zero lies on the line and has the same boundary multiplicity. -/
theorem spectralLineConvolution_traceCauchy (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → Q(a, h₀, hs₀(hs)))
    (Λ : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) (fun ω ↦ χ ω) hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2)) :
    let H := Q(a, h₀, hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a h₀ hs₀(hs) φ
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2, m.val), m.isLt⟩)
    SpectralRectanglesTraceCauchy B := by
  let Z₀ := {z : PontryaginDual C₁ × ℝ × ℝ //
    z.2.1 ∈ Icc (-(0 : ℝ)) 0 ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
  have hz (z : Z₀) : z.val.2.1 = 0 := by simpa using z.property.1
  let zeros : Z₀ ≃ Z(χ) :=
    { toFun := fun z ↦ ⟨(z.val.1, z.val.2.2), by simpa only [hz z, add_zero] using z.property.2⟩
      invFun := fun z ↦ ⟨(z.val.1, 0, z.val.2), by simp, by simpa only [add_zero] using z.property⟩
      left_inv := fun z ↦ Subtype.ext (Prod.ext rfl (Prod.ext (hz z).symm rfl))
      right_inv := fun _ ↦ Subtype.ext rfl }
  let J := SpectralStripJetIndex (F := F) χ a 0 s
  have hzero (j : J) : j.val.2.1 = 0 := by
    simpa using (SpectralStripJetIndex.mem_strip_order_pos h₀ j).1
  have hbound (k : ℕ) : spectralStripMultiplicity 0 s 0 k = spectralBoundaryMultiplicity s k :=
    spectralStripMultiplicity_boundary le_rfl (Or.inr rfl) s k
  let jets : J ≃ SpectralLineJetIndex (F := F) χ a s :=
    { toFun := fun j ↦ ⟨(j.val.1, j.val.2.2.1, j.val.2.2.2), by
        simpa only [hzero j, add_zero, hbound] using j.property⟩
      invFun := fun i ↦ ⟨(i.val.1, 0, i.val.2.1, i.val.2.2), by
        simpa only [add_zero, hbound] using i.property⟩
      left_inv := fun j ↦ Subtype.ext (Prod.ext rfl (Prod.ext (hzero j).symm rfl))
      right_inv := fun _ ↦ Subtype.ext rfl }
  let lineCount (z : Z(χ)) := N(χ, s, z)
  let stripCount (w : Z₀) := spectralStripMultiplicity 0 s w.val.2.1 (mult(χ w.val.1,
    shift(a + w.val.2.1, w.val.2.2)))
  have hm (w : Z₀) : stripCount w = lineCount (zeros w) := by
    simp only [stripCount, lineCount, zeros, Equiv.coe_fn_mk, hz w, add_zero, hbound]
  let lineJet (z : Z(χ)) (m : Fin (lineCount z)) : SpectralLineJetIndex (F := F) χ a s :=
    ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
  let stripJet (w : Z₀) (m : Fin (stripCount w)) : J :=
    ⟨(w.val.1, w.val.2.1, w.val.2.2, m.val), m.isLt⟩
  let rect (q : ℕ × ℕ) := (Finset.Iic q.1).product (Finset.Iic q.2)
  let raw (k : SpectralLineJetIndex (F := F) χ a s) :=
    spectralZeroJet (F := F) (χ k.val.1) 0 k.val.2.1 k.val.2.2
  -- Vary the lower endpoint to transport the quotient and its dual embedding together.
  let claim (l : ℝ) (hl : l ≤ 0) :=
    ∀ (X : SpectralLineJetIndex (F := F) χ a s → Q(a, hl, hs₀(hs)))
      (L : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, hl, hs₀(hs))),
      IsSpectralMarkushevichBasis X L →
      ∀ (hv : ∀ k, MemLp (raw k) 2 _),
      (∀ k, spectralSobolevDualEmbedding F a hl hs₀(hs) (L k) = (hv k).toLp (raw k)) →
      SpectralRectanglesTraceCauchy (fun q ↦ spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a hl hs₀(hs) φ) X L
        ((rect q).preimage e e.injective.injOn) lineCount lineJet)
  suffices claim 0 h₀ from this x Λ _hb (spectralLineJet_memLp (F := F) χ hs) _hj
  suffices claim (-0) hStrip(h₀) by simpa only [neg_zero] using this
  intro X L hb hv hj
  have strip := spectralStripConvolution_traceCauchy (F := F) a χ _hχ h₀ hs φ
    eχ (zeros.toEmbedding.trans e) (fun w ↦ _he (zeros w)) (X ∘ jets) (L ∘ jets)
    (spectralLineConvolution_traceCauchy_reindexBasis jets X L hb) (by
      rintro ⟨⟨ω, b, t, k⟩, hk⟩
      obtain rfl : b = 0 := hzero ⟨(ω, b, t, k), hk⟩
      exact hj (jets ⟨(ω, 0, t, k), hk⟩))
  let A := spectralConvolution (F := F) a hStrip(h₀) hs₀(hs) φ
  have rectangle_eq (q : ℕ × ℕ) := spectralLineConvolution_traceCauchy_reindexSum
    jets zeros e A X L lineCount stripCount lineJet stripJet hm (fun _ _ ↦ Subtype.ext rfl) (rect q)
  exact (congrArg SpectralRectanglesTraceCauchy (funext rectangle_eq)).mp strip

/-- Paper: Theorem 10.3.1.1(1) and (10.3.1.1), p. 448. The rectangular
finite-rank sums over any enumeration converge to convolution in each Schatten class.
Deviation: The injections permit finite or empty character and zero sets. Use
the strict multiplicity cutoff and the jet realization of Theorem 10.2.1.1. -/
theorem spectralLineConvolution_schatten_tendsto (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → Q(a, h₀, hs₀(hs)))
    (Λ : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) (fun ω ↦ χ ω) hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))
    (p : ℝ) (hp : 1 ≤ p) :
    let H := Q(a, h₀, hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a h₀ hs₀(hs) φ
    let S := schattenClass H H p hp
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2, m.val), m.isLt⟩)
    ∃ (hA : A ∈ S) (hB : ∀ ij, B ij ∈ S),
      Tendsto (fun ij ↦ schattenNorm (E := H) (F := H) (p := p) (hp := hp)
        (⟨B ij, hB ij⟩ - ⟨A, hA⟩ : S)) atTop (𝓝 0) := by
  let count (z : Z(χ)) := N(χ, s, z)
  let jet (z : Z(χ)) (m : Fin (count z)) : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s :=
    ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
  let index (j : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s) : (z : Z(χ)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1), SpectralLineJetIndex.order_pos j⟩, ⟨j.val.2.2, j.property⟩⟩
  let equiv : ((z : Z(χ)) × Fin (count z)) ≃ SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact spectralConvolutionFiniteSum_limit_of_traceCauchy
    (spectralConvolution (F := F) a h₀ hs₀(hs) φ) x Λ e count jet
    _hb equiv.bijective p hp
    (spectralLineConvolution_traceCauchy (F := F) a χ _hχ hs φ eχ e _he x Λ _hb _hj)

/-- Number the norm-one characters and, within each row, the selected zeros. -/
private theorem spectralLineConvolution_nuclear_indices {Z : Type*}
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (row : Z → PontryaginDual C₁) (point : Z → ℂ)
    (hinj : Injective (fun z ↦ (row z, point z))) (hz : ∀ z, 0 < order(χ (row z), point z)) :
    ∃ (r : PontryaginDual C₁ ↪ ℕ) (e : Z ↪ ℕ × ℕ), ∀ z, (e z).1 = r (row z) := by
  have hK := IsModulation.isCompact_ker (m := m𝔽) hm𝔽
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp hK
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : SecondCountableTopology C₁ := Topology.IsInducing.subtypeVal.secondCountableTopology
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual C₁) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap C₁ Circle).secondCountableTopology
  let : Countable (PontryaginDual C₁) := countable_of_Lindelof_of_discrete
  let zeros (ω : PontryaginDual C₁) := {z : ℂ | 0 < order(χ ω, z)}
  have hc (ω) : (zeros ω).Countable := by
    obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec (χ ω)
    have hfinite : order(χ ω, (2 : ℂ)) ≠ ⊤ := by
      intro h
      have hp : 0 < order(χ ω, (2 : ℂ)) := by rw [h]; exact WithTop.coe_lt_top (0 : ℤ)
      have := completedHeckeL_continuation_zeros (χ ω) _ hL heq (by norm_num : 0 < (2 : ℂ).re) hp
      norm_num at this
    have hd : (zeros ω)ᶜ ∈ codiscrete ℂ := by
      filter_upwards [hL.meromorphicOn.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top] with z hz'
      rcases hz'.2 with h | h
      · simp [zeros, h]
      · exact (hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
          isPreconnected_univ (mem_univ _) (mem_univ z) hfinite h).elim
    let : DiscreteTopology (zeros ω) := isDiscrete_iff_discreteTopology.mp
      (compl_mem_codiscrete_iff.mp hd).2
    exact Set.countable_coe_iff.mp countable_of_Lindelof_of_discrete
  let : Countable (⋃ ω, zeros ω) := (Set.countable_iUnion hc).to_subtype
  obtain ⟨r⟩ := nonempty_embedding_nat (PontryaginDual C₁)
  obtain ⟨c⟩ := nonempty_embedding_nat (⋃ ω, zeros ω)
  let pt (z : Z) : ⋃ ω, zeros ω := ⟨point z, mem_iUnion.mpr ⟨row z, hz z⟩⟩
  refine ⟨r, ⟨fun z ↦ (r (row z), c (pt z)), ?_⟩, fun _ ↦ rfl⟩
  intro i j hij
  exact hinj (Prod.ext (r.injective (congrArg Prod.fst hij))
    (congrArg Subtype.val (c.injective (congrArg Prod.snd hij))))

/-- Paper: Theorem 10.3.1.1(2), p. 448. Convolution on the a-line spectral
quotient is trace class for each test. -/
theorem spectralLineConvolution_nuclear {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, h₀, hs₀(hs))
    IsNuclearOperator (E := H) (F := H) (spectralConvolution (F := F) a h₀ hs₀(hs) φ) := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  obtain ⟨_, x, Λ, hb, hj⟩ := spectralLineMarkushevichBasis (a := a) χ hχ hs
  obtain ⟨r, e, he⟩ := spectralLineConvolution_nuclear_indices χ
    (fun z : Z(χ) ↦ z.val.1) (fun z ↦ shift(a, z.val.2)) (by
      intro i j h
      have hrow := congrArg Prod.fst h
      exact Subtype.ext (Prod.ext hrow
        (by simpa using congrArg (fun p ↦ (p.2 : ℂ).im) h))) (fun z ↦ z.property)
  obtain ⟨hA, _⟩ := spectralLineConvolution_schatten_tendsto (F := F) a χ hχ hs φ
    r e he x Λ hb hj 1 le_rfl
  exact (mem_traceClassOperators_iff_isNuclearOperator _).mp hA

/-- A descended endomorphism has operator norm bounded by the ambient operator norm. -/
private theorem spectralConvolution_norm_le_of_quotient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (S : Submodule ℂ E) (A : E →L[ℂ] E) (B : (E ⧸ S) →L[ℂ] (E ⧸ S))
    (h : ∀ x, B (S.mkQ x) = S.mkQ (A x)) : ‖B‖ ≤ ‖A‖ := by
  refine B.opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨u, hu, hnorm⟩ := Submodule.Quotient.norm_mk_lt (S := S) x
    (div_pos hε (show 0 < ‖A‖ + 1 by positivity))
  calc
    ‖B x‖ = ‖S.mkQ (A u)‖ := by rw [← hu]; exact congrArg norm (h u)
    _ ≤ ‖A u‖ := Submodule.Quotient.norm_mk_le S _
    _ ≤ ‖A‖ * (‖x‖ + ε / (‖A‖ + 1)) :=
      (A.le_opNorm u).trans (mul_le_mul_of_nonneg_left hnorm.le (norm_nonneg A))
    _ = ‖A‖ * ‖x‖ + ε * (‖A‖ / (‖A‖ + 1)) := by ring
    _ ≤ ‖A‖ * ‖x‖ + ε := by
      have hscale : ‖A‖ / (‖A‖ + 1) ≤ 1 :=
        (div_le_one (by positivity)).mpr (le_add_of_nonneg_right zero_le_one)
      exact add_le_add_right (mul_le_of_le_one_right hε.le hscale) _

/-- The Hardy–Sobolev action is continuous in operator norm, and passing to
the quotient can only decrease the norm. -/
private theorem spectralConvolution_opNorm_continuous {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    Continuous (spectralConvolution (F := F) a hI hs) := by
  let A := (spectralConvolution_isLinear (F := F) a hI hs).mk' (spectralConvolution (F := F) a hI hs)
  let B (φ : BruhatCompactSupport C𝔽) : W(l, r, s) →L[ℂ] W(l, r, s) :=
    (testAction(l, r, s, hI, hs) φ : W(l, r, s) →L[ℂ] W(l, r, s))
  have htest : Continuous B := continuous_hardySobolevTestAction μ𝔽 m𝔽 l r s hI hs
  have hn (φ : BruhatCompactSupport C𝔽) : ‖A φ‖ ≤ ‖B φ‖ :=
    spectralConvolution_norm_le_of_quotient (Θ(a, hI, hs)) _ _
      (spectralConvolution_mkQ (F := F) a hI hs φ)
  have hB0 : B 0 = 0 := map_zero (testAction(l, r, s, hI, hs))
  change Continuous A
  apply continuous_of_tendsto_nhds_zero A
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ ↦ norm_nonneg _) hn ?_
  have hc : Tendsto (fun φ ↦ ‖B φ‖) (𝓝 0) (𝓝 ‖B 0‖) := htest.norm.continuousAt
  rwa [hB0, norm_zero] at hc

/-- The trace norm is a supremum of continuous finite sums of approximation numbers
on any operator-norm continuous family of trace-class operators. -/
private theorem spectralConvolution_traceNorm_lowerSemicontinuous {X H : Type*}
    [TopologicalSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : X → nuclearEndomorphisms H) (hT : Continuous (fun x ↦ (T x).val)) :
    LowerSemicontinuous (fun x ↦ traceNorm (T x)) := by
  let p (I : Finset ℕ) (x : X) := ∑ n ∈ I, approximationNumber (T x).val n
  have hbound (x : X) : BddAbove (range (fun I ↦ p I x)) :=
    ⟨traceNorm (T x), fun _ ⟨I, h⟩ ↦ h ▸
      spectralConvolutionFiniteSum_limit_of_traceCauchy_bound (T x) I⟩
  have hsum (x : X) : traceNorm (T x) = ⨆ I, p I x := by
    apply le_antisymm ?_ (ciSup_le fun I ↦ spectralConvolutionFiniteSum_limit_of_traceCauchy_bound (T x) I)
    have he := schattenNorm_one_eq_traceNorm (T x)
    simp only [schattenNorm, Real.rpow_one, div_one] at he
    rw [← he]
    exact Real.tsum_le_of_sum_le (spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg _)
      (fun I ↦ le_ciSup (hbound x) I)
  simp_rw [hsum]
  refine lowerSemicontinuous_ciSup hbound fun I ↦ Continuous.lowerSemicontinuous ?_
  apply continuous_finsetSum _ fun n _ ↦ ?_
  have hcont : Continuous (fun D : H →L[ℂ] H ↦ approximationNumber D n) :=
    (LipschitzWith.of_dist_le' (K := 1) (fun D E ↦ by
      simpa only [dist_eq_norm, Real.norm_eq_abs, one_mul] using abs_approximationNumber_sub_le D E n)).continuous
  exact hcont.comp hT

/-- A lower semicontinuous seminorm restricts continuously to each Fréchet stage of a
strict LF-space, whose topology is final locally convex. This is the Fréchet-stage
argument of `IsLFSpace.barrelled` from Appendix C. -/
private theorem spectralConvolution_continuous_of_lsc_seminorm {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (hE : IsStrictLFSpace E) (p : Seminorm ℂ E)
    (hp : LowerSemicontinuous p) : Continuous p := by
  obtain ⟨_, S, _, hS, _, htop⟩ := hE
  have hP : WithSeminorms
      (Subtype.val : {q : Seminorm ℂ E // ∀ k, Continuous (q ∘ (S k).subtype)} → Seminorm ℂ E) :=
    ⟨htop⟩
  apply hP.continuous_seminorm (i := ⟨p, ?_⟩)
  intro k
  obtain ⟨hadd, hpoly, hmetric, hcomplete⟩ := hS k
  let : UniformSpace (S k) := IsTopologicalAddGroup.rightUniformSpace (S k)
  let : IsUniformAddGroup (S k) := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace (S k) := hcomplete
  let : ContinuousSMul ℂ (S k) := PolynormableSpace.continuousSMul ℂ (S k)
  have : (uniformity (S k)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero (S k)]
    infer_instance
  have : BaireSpace (S k) := by
    let := UniformSpace.metricSpace (S k)
    infer_instance
  exact (p.comp (S k).subtype).continuous_of_lowerSemicontinuous (hp.comp continuous_subtype_val)

/-- A linear operator-norm continuous family of nuclear endomorphisms has a
trace-norm continuous lift when its domain is a strict LF-space. -/
private theorem spectralConvolution_traceNorm_lift {E H : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hE : IsStrictLFSpace E) (A : E →ₗ[ℂ] (H →L[ℂ] H)) (hA : Continuous A)
    (hn : ∀ x, IsNuclearOperator (A x)) :
    ∃ T : E →ₗ[ℂ] nuclearEndomorphisms H,
      (∀ x, (T x).val = A x) ∧ Tendsto (fun x ↦ traceNorm (T x)) (𝓝 0) (𝓝 0) := by
  let T := A.codRestrict (nuclearEndomorphisms H) hn
  refine ⟨T, fun _ ↦ rfl, ?_⟩
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let hcore := traceNorm_normedSpaceCore (H := H)
  let p : Seminorm ℂ E :=
    { toFun := fun x ↦ traceNorm (T x)
      map_zero' := by rw [map_zero]; exact (hcore.norm_eq_zero_iff _).mpr rfl
      add_le' := fun x y ↦ by rw [map_add]; exact hcore.norm_triangle _ _
      neg' := fun x ↦ by
        rw [map_neg, ← neg_one_smul ℂ (T x)]
        have h := hcore.norm_smul (-1 : ℂ) (T x)
        simpa only [norm_neg, norm_one, one_mul] using h
      smul' := fun c x ↦ by rw [map_smul]; exact hcore.norm_smul _ _ }
  have hp : LowerSemicontinuous p := spectralConvolution_traceNorm_lowerSemicontinuous T hA
  have hc := spectralConvolution_continuous_of_lsc_seminorm hE p hp
  change Tendsto p (𝓝 0) (𝓝 0)
  exact hc.tendsto' 0 0 p.map_zero'

/-- Paper: Theorem 10.3.1.1(2) and (10.3.1.2), p. 448. The convolution
action lifts to a linear map into the trace class, continuous at zero in trace norm. -/
theorem spectralLineConvolution_traceNorm_continuous {s : ℝ} (hs : 1 < s) :
    let H := Q(a, h₀, hs₀(hs))
    ∃ T : BruhatCompactSupport C𝔽 →ₗ[ℂ] nuclearEndomorphisms H,
      (∀ φ, (T φ).val = spectralConvolution (F := F) a h₀ hs₀(hs) φ) ∧
      Tendsto (fun φ : BruhatCompactSupport C𝔽 ↦ traceNorm (H := H) (T φ)) (𝓝 0) (𝓝 0) := by
  intro H
  let A : BruhatCompactSupport C𝔽 →ₗ[ℂ] (H →L[ℂ] H) :=
    (spectralConvolution_isLinear (F := F) a h₀ hs₀(hs)).mk'
      (spectralConvolution (F := F) a h₀ hs₀(hs))
  exact spectralConvolution_traceNorm_lift bruhatCompactSupport_strictLF A
    (spectralConvolution_opNorm_continuous (F := F) a h₀ hs₀(hs))
    (spectralLineConvolution_nuclear (F := F) a hs)

/-- Paper: Theorem 10.3.1.1(2), p. 448. Taking the trace of convolution gives
a distribution on the Bruhat compactly supported test space. -/
theorem spectralLineConvolution_trace_distribution {s : ℝ} (hs : 1 < s) :
    let H := Q(a, h₀, hs₀(hs))
    ∃ D : StrongDual ℂ (BruhatCompactSupport C𝔽),
      ∀ (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms H),
        T.val = spectralConvolution (F := F) a h₀ hs₀(hs) φ →
        D φ = hilbertTrace (H := H) T := by
  have traceDistribution {X : Type _} {H : Type _} [AddCommGroup X] [Module ℂ X]
      [TopologicalSpace X] [IsTopologicalAddGroup X] [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (A : X → H →L[ℂ] H)
      (h : ∃ T : X →ₗ[ℂ] nuclearEndomorphisms H, (∀ x, (T x).val = A x) ∧
        Tendsto (fun x : X ↦ traceNorm (H := H) (T x)) (𝓝 0) (𝓝 0)) :
      ∃ D : StrongDual ℂ X, ∀ (x : X) (U : nuclearEndomorphisms H),
        U.val = A x → D x = hilbertTrace U := by
    obtain ⟨T, hT, ht⟩ := h
    obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
    let D : X →ₗ[ℂ] ℂ := L.comp T
    have hb (x : X) : ‖D x‖ ≤ traceNorm (T x) :=
      (congrArg (fun c : ℂ ↦ ‖c‖) (hL (T x))).le.trans (norm_hilbertTrace_le (T x))
    have hd : Continuous D := continuous_of_continuousAt_zero D <| by
      change Tendsto D (𝓝 0) (𝓝 (D 0))
      rw [D.map_zero]
      exact squeeze_zero_norm hb ht
    refine ⟨⟨D, hd⟩, fun x U hU ↦ ?_⟩
    have heq : T x = U := Subtype.ext ((hT x).trans hU.symm)
    exact (hL (T x)).trans (congrArg (hilbertTrace (H := H)) heq)
  exact traceDistribution (X := BruhatCompactSupport C𝔽) (H := Q(a, h₀, hs₀(hs)))
    (spectralConvolution (F := F) a h₀ hs₀(hs))
    (spectralLineConvolution_traceNorm_continuous (F := F) a hs)

-- TODO(paper-gap): The L¹ comparison after (10.3.1.26) supplies no
-- sampling estimate at zero ordinates, and the rapid-decay claim uses arbitrary numbering.

section StripTraceFormula

open InnerProductSpace
open scoped InnerProductSpace

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

section InvariantBlockTrace

/-- Along a countably generated filter, strong convergence to the identity suffices for
convergence of the traces of left products with a fixed nuclear operator. -/
private theorem stripTrace_tendsto_strong {H I : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {l : Filter I} [l.IsCountablyGenerated]
    (P : I → H →L[ℂ] H) (hP : ∀ y, Tendsto (fun i ↦ P i y) l (𝓝 y))
    (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ hilbertTrace ⟨P i * T.val, mul_mem_nuclearEndomorphisms_left (P i) T⟩)
      l (𝓝 (hilbertTrace T)) := by
  apply tendsto_iff_seq_tendsto.2
  intro u hu
  let A : traceClassOperators H H := ⟨T.val, (mem_traceClassOperators_iff_isNuclearOperator _).2 T.property⟩
  let B (n : ℕ) : nuclearEndomorphisms H :=
    ⟨P (u n) * T.val, mul_mem_nuclearEndomorphisms_left _ T⟩
  obtain ⟨hm, hI, hlim⟩ := tendsto_schattenNorm_comp_left A (P ∘ u) (ContinuousLinearMap.id ℂ H)
    (fun y ↦ (hP y).comp hu)
  have hn : Tendsto (fun n ↦ traceNorm (B n - T)) atTop (𝓝 0) := by
    refine hlim.congr fun n ↦ ?_
    rw [← schattenNorm_one_eq_traceNorm]
    congr 1
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun n ↦ ‖hilbertTrace (B n) - hilbertTrace T‖) atTop (𝓝 0)
  have hdiff (n : ℕ) : hilbertTrace (B n) - hilbertTrace T = hilbertTrace (B n - T) :=
    ((congrArg₂ (· - ·) (htr (B n)).symm (htr T).symm).trans (tr.map_sub _ _).symm).trans (htr _)
  simp only [hdiff]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ norm_hilbertTrace_le (B n - T)) hn

/-- Finite independent moment functionals have biorthogonal vectors in their Riesz span. -/
private theorem stripDualTrace_finiteCoordinates {H I : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I] [DecidableEq I]
    (u : I → H) (hu : LinearIndependent ℂ u) :
    let V := Submodule.span ℂ (range u)
    let _ : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (finite_range u)
    ∃ y : I → H, (∀ i j, ⟪u j, y i⟫_ℂ = if i = j then 1 else 0) ∧
      ∀ v, V.starProjection v = ∑ i, ⟪u i, v⟫_ℂ • y i := by
  classical
  intro V hdim
  let ev : V →ₗ[ℂ] I → ℂ := LinearMap.pi fun i ↦ (innerSL ℂ (u i)).toLinearMap.comp V.subtype
  have hi : Injective ev := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro v hv
    have vanish (i : I) : ⟪u i, (v : H)⟫_ℂ = 0 := congrFun (LinearMap.mem_ker.mp hv) i
    have hV : V ≤ (innerSL ℂ (v : H)).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact inner_eq_zero_symm.mp (vanish i)
    exact Subtype.ext (inner_self_eq_zero.mp (hV v.property))
  have hs : Surjective ev := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank ℂ V = Module.finrank ℂ (I → ℂ) from
      (finrank_span_eq_card hu).trans (Module.finrank_fintype_fun_eq_card ℂ).symm)).mp hi
  let e := LinearEquiv.ofBijective ev ⟨hi, hs⟩
  let b := (Pi.basisFun ℂ I).map e.symm
  refine ⟨fun i ↦ (b i : H), fun i j ↦ ?_, fun v ↦ ?_⟩
  · change e (b i) j = _
    simp [b, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  · let w : V := ⟨V.starProjection v, V.starProjection_apply_mem v⟩
    have hc (i : I) : b.repr w i = ⟪u i, v⟫_ℂ := by
      change (Pi.basisFun ℂ I).repr (e w) i = _
      rw [Pi.basisFun_repr]
      change ⟪u i, V.starProjection v⟫_ℂ = _
      rw [← V.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr
        (show u i ∈ V from Submodule.subset_span (mem_range_self i))]
    have he := congrArg (fun z : V ↦ (z : H)) (b.sum_repr w).symm
    simpa only [Submodule.coe_sum, Submodule.coe_smul, hc] using he

/-- A total family of independent moment functionals computes a nuclear trace if the
operator acts diagonally modulo the earlier moments of each finite block. -/
private theorem stripDualTrace_hasSum {H Z : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Countable Z] (N : Z → ℕ)
    (u : (z : Z) → Fin (N z) → H)
    (hu : LinearIndependent ℂ (fun i : (z : Z) × Fin (N z) ↦ u i.1 i.2))
    (hsep : ∀ v : H, (∀ z m, ⟪u z m, v⟫_ℂ = 0) → v = 0)
    (T : nuclearEndomorphisms H) (t : Z → ℂ)
    (hflag : ∀ z m v, (∀ k : Fin (N z), k < m → ⟪u z k, v⟫_ℂ = 0) →
      ⟪u z m, T.val v⟫_ℂ = t z * ⟪u z m, v⟫_ℂ) :
    HasSum (fun z ↦ (N z : ℂ) * t z) (hilbertTrace T) := by
  classical
  let I (K : Finset Z) := (z : ↥K) × Fin (N z.val)
  let b (K : Finset Z) (i : I K) := u i.1.val i.2
  let V (K : Finset Z) := Submodule.span ℂ (range (b K))
  let fi (K : Finset Z) : Fintype (I K) := inferInstanceAs (Fintype ((z : ↥K) × Fin (N z.val)))
  let dim (K : Finset Z) : FiniteDimensional ℂ (V K) := FiniteDimensional.span_of_finite ℂ (finite_range (b K))
  let P (K : Finset Z) := (V K).starProjection
  have mono : Monotone V := by
    intro K L h
    apply Submodule.span_mono
    rintro _ ⟨⟨z, m⟩, rfl⟩
    exact ⟨⟨⟨z.val, h z.property⟩, m⟩, rfl⟩
  have hd : ⊤ ≤ (⨆ K, V K).topologicalClosure := by
    apply (Submodule.topologicalClosure_eq_top_iff.mpr ?_).ge
    rw [Submodule.eq_bot_iff]
    intro v hv
    apply hsep
    intro z m
    have hmem : u z m ∈ V {z} :=
      Submodule.subset_span (show b {z} ⟨⟨z, Finset.mem_singleton_self z⟩, m⟩ ∈ range (b {z}) from mem_range_self _)
    exact (Submodule.mem_orthogonal _ _).mp hv _ ((le_iSup V {z}) hmem)
  have hsot (v : H) := Submodule.starProjection_tendsto_self V mono v hd
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  have hfin (K : Finset Z) :
      hilbertTrace ⟨P K * T.val, mul_mem_nuclearEndomorphisms_left _ T⟩ =
        ∑ z ∈ K, (N z : ℂ) * t z := by
    have hi : Injective (fun i : I K ↦ (⟨i.1.val, i.2⟩ : (z : Z) × Fin (N z))) := by
      rintro ⟨⟨z, hz⟩, m⟩ ⟨⟨w, hw⟩, n⟩ h
      obtain ⟨rfl, h⟩ := Sigma.mk.inj h
      cases eq_of_heq h
      rfl
    obtain ⟨y, hy, hP⟩ := stripDualTrace_finiteCoordinates (b K) (hu.comp _ hi)
    let r (i : I K) : nuclearEndomorphisms H :=
      ⟨((innerSL ℂ (b K i)).comp T.val).smulRight (y i), smulRight_mem_nuclearEndomorphisms _ _⟩
    have heq : (⟨P K * T.val, mul_mem_nuclearEndomorphisms_left _ T⟩ : nuclearEndomorphisms H) =
        ∑ i, r i := by
      apply Subtype.ext
      ext v
      simpa [P, V, r, ContinuousLinearMap.mul_def, Submodule.coe_sum] using hP (T.val v)
    rw [heq, ← htr, map_sum]
    calc
      _ = ∑ i : I K, t i.1.val := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [htr, hilbertTrace_smulRight]
        change ⟪u i.1.val i.2, T.val (y i)⟫_ℂ = _
        have hlower (k : Fin (N i.1.val)) (hk : k < i.2) : ⟪u i.1.val k, y i⟫_ℂ = 0 := by
          have hne : i ≠ (⟨i.1, k⟩ : I K) := by
            intro h
            exact hk.ne (eq_of_heq (Sigma.mk.inj h.symm).2)
          exact (hy i ⟨i.1, k⟩).trans (ite_eq_right hne)
        rw [hflag i.1.val i.2 _ hlower]
        have hone : ⟪u i.1.val i.2, y i⟫_ℂ = 1 := (hy i i).trans (ite_eq_left rfl)
        rw [hone, mul_one]
      _ = _ := by
        change (∑ i : (z : ↥K) × Fin (N z.val), t i.1.val) = _
        rw [Fintype.sum_sigma]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact Finset.sum_attach K (fun z ↦ (N z : ℂ) * t z)
  exact (stripTrace_tendsto_strong P hsot T).congr hfin

end InvariantBlockTrace

section StripConvolutionCoefficients

variable {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)

local notation "logNorm" => (logIdeleClassNorm F)
local notation "D" => spectralSobolevDualEmbedding F a (hStrip(hα)) hs₀(hs)
local notation "raw(" χ ", " j ")" =>
  spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "jet(" z ", " m ")" => ⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩
local notation "J(" χ ")" => SpectralStripJetIndex (F := F) χ a α s

/-- A quotient jet functional evaluates on a representative by its explicit Haar moment. -/
private theorem spectralStripConvolution_jet_eval
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (j : SpectralStripJetIndex χ a α s) (f : StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hf : D f = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))) (v : W(-α, α, s)) :
    Integrable (fun y ↦ v y * raw(χ, j) y) μ𝔽 ∧
      f ((Θ(a, hStrip(hα), hs₀(hs))).mkQL v) = ∫ y, v y * raw(χ, j) y ∂μ𝔽 := by
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
  have he := spectralSobolevPairing_dual (hStrip(hα)) hs₀(hs) (f.comp ((Θ(a, hStrip(hα), hs₀(hs))).mkQL)) v
  change Integrable (fun y ↦ v y * D f y) μ𝔽 ∧
      f ((Θ(a, hStrip(hα), hs₀(hs))).mkQL v) = ∫ y, v y * D f y ∂μ𝔽 at he
  have hEq := hae.mono fun y hy ↦ congrArg (v y * ·) hy
  exact ⟨he.1.congr hEq, he.2.trans (integral_congr_ae hEq)⟩

/-- If the lower moments vanish, translation multiplies the top moment by the norm twist. -/
private theorem spectralStripConvolution_jet_translate (η : PontryaginDual C𝔽) (b t : ℝ)
    (m : ℕ) (v : W(-α, α, s))
    (hint : ∀ i ≤ m, Integrable (fun x ↦ v x * spectralZeroJet η b t i x) μ𝔽)
    (hzero : ∀ i < m, ∫ x, v x * spectralZeroJet η b t i x ∂μ𝔽 = 0) (g : C𝔽) :
    let τ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs)
    ∫ y, τ g v y * spectralZeroJet η b t m y ∂μ𝔽 =
      ideleClassNormTwist η (shift(b, t)) g * ∫ y, v y * spectralZeroJet η b t m y ∂μ𝔽 := by
  intro τ
  let T := ideleClassNormTwist η ((b : ℂ) + (t : ℂ) * Complex.I)
  let L (y : C𝔽) : ℂ := logNorm y
  let c (i : ℕ) := T g * L g ^ (m - i) * (m.choose i : ℂ)
  have hlog (y : C𝔽) : L (g * y) = L y + L g := by
    dsimp only [L, logIdeleClassNorm]
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
      (NNReal.coe_ne_zero.2 (ideleClassNorm F y).ne_zero), Complex.ofReal_add, add_comm]
  have hsum (y : C𝔽) : v y * spectralZeroJet η b t m (g * y) =
      ∑ i ∈ Finset.range (m + 1), c i * (v y * spectralZeroJet η b t i y) := by
    change v y * (T (g * y) * L (g * y) ^ m) = _
    rw [map_mul, hlog, add_pow]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change v y * (T g * T y * (L y ^ i * L g ^ (m - i) * (m.choose i : ℂ))) =
      (T g * L g ^ (m - i) * (m.choose i : ℂ)) * (v y * (T y * L y ^ i))
    ring
  let J := spectralZeroJet η b t m
  let H (y : C𝔽) := v (g⁻¹ * y) * J y
  calc
    _ = ∫ y, H y ∂μ𝔽 := integral_congr_ae
      ((hardySobolevTranslation_apply μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs) g v).mono
        fun y hy ↦ congrArg (· * J y) hy)
    _ = ∫ y, H (g * y) ∂μ𝔽 := (integral_mul_left_eq_self H g).symm
    _ = ∫ y, v y * J (g * y) ∂μ𝔽 := by simp only [H, inv_mul_cancel_left]
    _ = _ := by
      simp_rw [show ∀ y, v y * J (g * y) = _ from hsum]
      rw [integral_finsetSum _ fun i hi ↦ (hint i (Finset.mem_range_succ_iff.mp hi)).const_mul (c i)]
      simp_rw [integral_const_mul]
      rw [Finset.sum_eq_single_of_mem m (Finset.mem_range_succ_iff.mpr le_rfl)]
      · simp [c, T]
      · intro i hi hne
        rw [hzero i (lt_of_le_of_ne (Finset.mem_range_succ_iff.mp hi) hne), mul_zero]

/-- On the common kernel of all lower moments at this zero, the selected jet coordinate
of the convolution is the Mellin value times the same coordinate of the input. -/
private theorem spectralStripConvolution_jet_top
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (f : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽) (z : Z(χ, α)) (m : Fin (N(χ, α, s, z)))
    (u : Q(a, hStrip(hα), hs₀(hs)))
    (hlower : ∀ k : Fin (N(χ, α, s, z)), k < m → f (jet(z, k)) u = 0) :
    f (jet(z, m)) (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ u) =
      M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2)) * f (jet(z, m)) u := by
  let θ := globalThetaSobolev F a (hStrip(hα)) hs₀(hs)
  obtain ⟨v, hv⟩ := θ.mkQ_surjective u
  let J (i : ℕ) := spectralZeroJet (χ z.val.1) z.val.2.1 z.val.2.2 i
  let j : J(χ) := jet(z, m)
  let τ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs)
  let ℓ := (f j).comp θ.mkQL
  let η := ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2))
  have heval (j : J(χ)) (w : W(-α, α, s)) :=
    spectralStripConvolution_jet_eval (a := a) hα hs χ j (f j) (hj j) w
  have hint (i : ℕ) (hi : i ≤ m.val) : Integrable (fun y ↦ v y * J i y) μ𝔽 := by
    let k : Fin (N(χ, α, s, z)) := ⟨i, hi.trans_lt m.isLt⟩
    exact (heval (jet(z, k)) v).1
  have hzero (i : ℕ) (hi : i < m.val) : ∫ y, v y * J i y ∂μ𝔽 = 0 := by
    let k : Fin (N(χ, α, s, z)) := ⟨i, hi.trans m.isLt⟩
    refine (heval (jet(z, k)) v).2.symm.trans ?_
    change f (jet(z, k)) (θ.mkQ v) = 0
    exact (congrArg (f (jet(z, k))) hv).trans (hlower k hi)
  have htop : ∫ y, v y * J m.val y ∂μ𝔽 = f j u :=
    (heval j v).2.symm.trans (congrArg (f j) hv)
  have hτ (g : C𝔽) : ℓ (τ g v) = η g * f j u :=
    (heval j (τ g v)).2.trans ((spectralStripConvolution_jet_translate hα hs
      (χ z.val.1) z.val.2.1 z.val.2.2 m.val v hint hzero g).trans (congrArg (η g * ·) htop))
  have hP := bruhatRegularizedAction_apply μ𝔽 τ
    (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs)).choose_spec.2 φ v
  have he := congrArg (fun p : PettisWeakCompletion W(-α, α, s) ↦
    (show Module.Dual ℂ (StrongDual ℂ W(-α, α, s)) from p) ℓ) hP.2
  change ℓ (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs) φ v) =
    ∫ g, ℓ (φ.val g • τ g v) ∂μ𝔽 at he
  have hM := (spectralConvolution_mellin_integrable φ (χ z.val.1) (shift(z.val.2.1, z.val.2.2))).2
  calc
    _ = ℓ (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs) φ v) :=
      (congrArg (fun w ↦ f j (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ w)) hv.symm).trans
        (congrArg (f j) (spectralConvolution_mkQ a (hStrip(hα)) hs₀(hs) φ v))
    _ = ∫ g, ℓ (φ.val g • τ g v) ∂μ𝔽 := he
    _ = ∫ g, (φ.val g * η g) * f j u ∂μ𝔽 := integral_congr_ae (.of_forall fun g ↦ by
      exact (map_smul ℓ _ _).trans ((congrArg (φ.val g * ·) (hτ g)).trans (mul_assoc _ _ _).symm))
    _ = _ := (integral_mul_const _ _).trans (congrArg (· * f j u) hM.symm)

/-- Rank-one insertions detect every scalar matrix entry of a single zero block.
Two applications of uniform boundedness give one operator-norm bound for all blocks. -/
private theorem spectralConvolutionFiniteSum_singleton_norm_bound
    {E J Z : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (x : J → E) (Λ : J → StrongDual ℂ E)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (h : ∀ (v : E) (f : StrongDual ℂ E),
      Summable (fun z ↦ ∑ m, Λ (jet z m) (A ((f.smulRight v) (x (jet z m)))))) :
    ∃ C ≥ (0 : ℝ), ∀ z, ‖spectralConvolutionFiniteSum A x Λ {z} N jet‖ ≤ C := by
  let B (z : Z) := spectralConvolutionFiniteSum A x Λ {z} N jet
  obtain ⟨C, hC⟩ := banach_steinhaus (g := B) fun v ↦ by
    let G (z : Z) := NormedSpace.inclusionInDoubleDual ℂ E (B z v)
    obtain ⟨R, hR⟩ := banach_steinhaus (g := G) fun f ↦ by
      let term (z : Z) := ∑ m, Λ (jet z m) (A ((f.smulRight v) (x (jet z m))))
      refine ⟨∑' z, ‖term z‖, fun z ↦ ?_⟩
      have he : G z f = term z := by
        change f (B z v) = term z
        simp [B, spectralConvolutionFiniteSum, term, smul_eq_mul, mul_comm]
      rw [he]
      exact (h v f).norm.le_tsum z (fun _ _ ↦ norm_nonneg _)
    exact ⟨R, fun z ↦ ((NormedSpace.inclusionInDoubleDualLi ℂ).norm_map (B z v)).ge.trans (hR z)⟩
  exact ⟨max C 0, le_max_right _ _, fun z ↦ (hC z).trans (le_max_left _ _)⟩

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. If the zero-block traces for a
fixed test are summable after every rank-one insertion, the Mellin value times
the norm of each surviving zeroth coordinate is bounded by one constant times
its distance from the span of all coordinates at the other zeros. -/
theorem spectralStripConvolution_mellin_norm_le_of_summable_rankOne_blocks
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽)
    (h : ∀ (v : Q(a, hStrip(hα), hs₀(hs))) (f : StrongDual ℂ Q(a, hStrip(hα), hs₀(hs))),
      Summable (fun z : Z(χ, α) ↦ ∑ m : Fin (N(χ, α, s, z)), Λ (jet(z, m))
        (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ ((f.smulRight v) (x (jet(z, m))))))) :
    ∃ C > (0 : ℝ), ∀ (z : Z(χ, α)) (hz : 0 < N(χ, α, s, z)),
      let Λ₀ := Λ (jet(z, (⟨0, hz⟩ : Fin (N(χ, α, s, z)))))
      let P := Submodule.span ℂ {f | ∃ (w : Z(χ, α)) (_ : w ≠ z) (m : Fin (N(χ, α, s, w))),
        f = Λ (jet(w, m))}
      ‖M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))‖ * ‖Λ₀‖ ≤ C * Metric.infDist Λ₀ (P : Set _) := by
  classical
  let A := spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ
  let j (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))) : J(χ) := jet(z, m)
  obtain ⟨C, hC, hbound⟩ := spectralConvolutionFiniteSum_singleton_norm_bound A x Λ _ j h
  have hpos : 0 < C + 1 := by linarith
  refine ⟨C + 1, hpos, fun z hz ↦ ?_⟩
  intro Λ₀ P
  let B := spectralConvolutionFiniteSum A x Λ {z} _ j
  let e := M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))
  have hinj : Injective (fun zm : (w : Z(χ, α)) × Fin (N(χ, α, s, w)) ↦ j zm.1 zm.2) := by
    rintro ⟨w,m⟩ ⟨t,n⟩ hwt
    have he : w = t := Subtype.ext (congrArg (fun i : J(χ) ↦ (i.val.1, i.val.2.1, i.val.2.2.1)) hwt)
    subst t
    exact congrArg (Sigma.mk w) (Fin.ext (congrArg (fun i : J(χ) ↦ i.val.2.2.2) hwt))
  have he : Λ₀.comp B = e • Λ₀ := by
    ext v
    exact (spectralConvolutionFiniteSum_limit_of_traceCauchy_coordinate A x Λ {z} _ j hb hinj z
      (Finset.mem_singleton_self _) ⟨0,hz⟩ v).trans
      (spectralStripConvolution_jet_top a hα hs χ Λ hj φ z ⟨0,hz⟩ v (fun k hk ↦ (Nat.not_lt_zero _ hk).elim))
  rw [mul_comm (C + 1)]
  apply (div_le_iff₀ hpos).mp
  apply (Metric.le_infDist (x := Λ₀) (s := (P : Set _)) ⟨0, P.zero_mem⟩).mpr
  intro g hg
  rw [dist_eq_norm, div_le_iff₀ hpos]
  have hgB : g.comp B = 0 := by
    apply (show Submodule.span ℂ _ ≤ (B.precomp ℂ).ker from ?_) hg
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, m, rfl⟩
    change (Λ (j w m)).comp B = 0
    ext v
    simp only [ContinuousLinearMap.comp_apply, B, spectralConvolutionFiniteSum, Finset.sum_singleton,
      sum_apply, map_sum, ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul, zero_apply]
    apply Finset.sum_eq_zero
    intro n _
    have hne : j z n ≠ j w m := fun h' ↦ hw (congrArg Sigma.fst (hinj (a₁ := ⟨z,n⟩) (a₂ := ⟨w,m⟩) h')).symm
    rw [hb.2.1 _ _ hne, mul_zero]
  have hnorm := (Λ₀ - g).opNorm_comp_le B
  rw [ContinuousLinearMap.sub_comp, he, hgB, sub_zero, norm_smul] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_left ((hbound z).trans (by linarith)) (norm_nonneg _))

/-- Paper: (10.3.1.17), p. 450, and Theorem 10.3.2.1(2), p. 454. In a basis realizing the strip jets, the
convolution matrix has no coefficients between distinct zeros. Each diagonal coefficient
is the Mellin value at the unshifted exponent of its zero. -/
theorem spectralStripConvolution_jetCoefficients
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (f : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x f)
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽) :
    (∀ (z z' : Z(χ, α)), z ≠ z' → ∀ (m : Fin (N(χ, α, s, z))) (n : Fin (N(χ, α, s, z'))),
      f (jet(z, m)) (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ (x (jet(z', n)))) = 0) ∧
    (∀ (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))),
      f (jet(z, m)) (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ (x (jet(z, m)))) =
        M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))) := by
  have coeff := spectralStripConvolution_jet_top a hα hs χ f hj φ
  constructor
  · intro z z' hzz m n
    have hindex (k : Fin (N(χ, α, s, z))) : (jet(z', n) : J(χ)) ≠ jet(z, k) := by
      intro h
      exact hzz (Subtype.ext (congrArg (fun u : J(χ) ↦ (u.val.1, u.val.2.1, u.val.2.2.1)) h).symm)
    exact (coeff z m _ (fun k _ ↦ hb.2.1 _ _ (hindex k))).trans
      ((congrArg (_ * ·) (hb.2.1 _ _ (hindex m))).trans (mul_zero _))
  · intro z m
    have hindex (k : Fin (N(χ, α, s, z))) (hk : k < m) : (jet(z, m) : J(χ)) ≠ jet(z, k) := by
      intro h
      exact (ne_of_lt hk) (Fin.ext (congrArg (fun u : J(χ) ↦ u.val.2.2.2) h).symm)
    exact (coeff z m _ (fun k hk ↦ hb.2.1 _ _ (hindex k hk))).trans
      ((congrArg (_ * ·) (hb.1 _)).trans (mul_one _))

end StripConvolutionCoefficients

/-- Linear independence passes to the conjugate Riesz representatives. -/
private theorem stripDualTrace_riesz_independent {H J : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (f : J → StrongDual ℂ H)
    (hf : LinearIndependent ℂ f) :
    LinearIndependent ℂ (fun j ↦ (toDual ℂ H).symm (f j)) := by
  apply linearIndependent_iff'.mpr
  intro s c h i hi
  have h' := congrArg (toDual ℂ H) h
  simp only [map_sum, map_smulₛₗ, LinearIsometryEquiv.apply_symm_apply, map_zero] at h'
  have hz := linearIndependent_iff'.mp hf s _ h' i hi
  simpa using hz

/-- The common-kernel identity lifts the strip moments to a separating family on the quotient. -/
private theorem stripDualTrace_separating (a : ℝ) (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a α s
    let H := Q(a, hStrip(hα), hs)
    let D := spectralSobolevDualEmbedding F a (hStrip(hα)) hs
    let raw (j : J) := spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2
    (∀ v, v ∈ Θ(a, hStrip(hα), hs) ↔
      ∀ j, spectralSobolevPairing v ((spectralStripJet_memLp χ hα hs j).toLp (raw j)) = 0) →
    ∃ f : J → StrongDual ℂ H,
      (∀ j, D (f j) = (spectralStripJet_memLp χ hα hs j).toLp (raw j)) ∧
      ∀ v : H, (∀ j, f j v = 0) → v = 0 := by
  classical
  intro J H D raw hK
  let θ := Θ(a, hStrip(hα), hs)
  let w (j : J) := (spectralStripJet_memLp χ hα hs j).toLp (raw j)
  have hr (j : J) : w j ∈ Set.range D := by
    rw [(spectralSobolevDualEmbedding_isometry_range (F := F) a (hStrip(hα)) hs).2]
    exact fun v hv ↦ (hK v).mp hv j
  choose f hf using hr
  refine ⟨f, hf, ?_⟩
  intro v hv
  obtain ⟨y, hy⟩ := θ.mkQ_surjective v
  rw [← hy]
  apply (spectralSobolevQuotient_eq_zero a (hStrip(hα)) hs y).mpr
  apply (hK y).mpr
  intro j
  have hp : f j (θ.mkQ y) = spectralSobolevPairing y (D (f j)) :=
    (spectralSobolevPairing_dual (hStrip(hα)) hs ((f j).comp θ.mkQL) y).2
  rw [hy, hv, hf] at hp
  exact hp.symm

/-- Paper: Theorem 10.3.2.1(2), p. 454. For a given nuclear convolution the
strip trace formula follows if the surviving moments identify the theta closure
at this width and Sobolev exponent.
Deviation: This conditional form isolates the common-kernel assertion of p. 446
and uses the strict boundary multiplicity. -/
theorem spectralStripConvolution_trace_of_commonKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω)) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (hk : ∀ v, v ∈ Θ(a, hStrip(hα), hs₀(hs)) ↔ ∀ j : SpectralStripJetIndex χ a α s,
      spectralSobolevPairing v ((spectralStripJet_memLp χ hα hs₀(hs) j).toLp
        (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) = 0) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let term (z : Z(χ, α)) := (N(χ, α, s, z) : ℂ) * M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace (H := H) T) := by
  intro H term T hT
  classical
  obtain ⟨_, e, _⟩ := spectralLineConvolution_nuclear_indices χ
    (fun z : Z(χ, α) ↦ z.val.1) (fun z ↦ shift(a + z.val.2.1, z.val.2.2)) (by
      intro i j h
      have hrow := congrArg Prod.fst h
      have hre := congrArg (fun p ↦ (p.2 : ℂ).re) h
      have him := congrArg (fun p ↦ (p.2 : ℂ).im) h
      exact Subtype.ext (Prod.ext hrow
        (Prod.ext (by simpa using hre) (by simpa using him)))) (fun z ↦ z.property.2)
  let : Countable (Z(χ, α)) := e.injective.countable
  let count (z : Z(χ, α)) := N(χ, α, s, z)
  let jet (z : Z(χ, α)) (m : Fin (count z)) : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let index (j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s) : (z : Z(χ, α)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩, ⟨j.val.2.2.2, j.property⟩⟩
  let equiv : ((z : Z(χ, α)) × Fin (count z)) ≃ SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  obtain ⟨f, hf, hsep⟩ := stripDualTrace_separating a χ hα hs₀(hs) hk
  let D := spectralSobolevDualEmbedding F a (hStrip(hα)) hs₀(hs)
  have hli : LinearIndependent ℂ f := LinearIndependent.of_comp D (by
    have eqw : D ∘ f = _ := funext hf
    rw [eqw]
    exact spectralStripJet_toLp_linearIndependent χ _hχ a hα hs₀(hs))
  let u (z : Z(χ, α)) (m : Fin (count z)) := (toDual ℂ H).symm (f (jet z m))
  have hu : LinearIndependent ℂ (fun i : (z : Z(χ, α)) × Fin (count z) ↦ u i.1 i.2) :=
    (stripDualTrace_riesz_independent f hli).comp equiv equiv.injective
  have heval (z : Z(χ, α)) (m : Fin (count z)) (v : H) :
      ⟪u z m, v⟫_ℂ = f (jet z m) v := toDual_symm_apply
  have htotal (v : H) (hv : ∀ z m, ⟪u z m, v⟫_ℂ = 0) : v = 0 := by
    apply hsep v
    intro i
    obtain ⟨⟨z, m⟩, rfl⟩ := equiv.surjective i
    exact (heval z m v).symm.trans (hv z m)
  have ht : HasSum term (hilbertTrace T) := stripDualTrace_hasSum count u hu htotal T
    (fun z ↦ M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))) (by
      intro z m v hlow
      simp only [heval] at hlow ⊢
      rw [hT]
      exact spectralStripConvolution_jet_top a hα hs χ f hf φ z m v hlow)
  exact ⟨ht.summable.norm, ht⟩

/-- Paper: Theorem 10.3.2.1(2) and (10.3.2.3)–(10.3.2.4), p. 454. The trace
is the absolutely convergent sum of the Mellin values at the strip zeros with
full interior multiplicities and truncated boundary multiplicities.
Deviation: Use the strict boundary cutoff and positive meromorphic order.
The dependent double sum is expressed as one family. -/
theorem spectralStripConvolution_trace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω)) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let term (z : Z(χ, α)) := (N(χ, α, s, z) : ℂ) * M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace (H := H) T) := by
  exact spectralStripConvolution_trace_of_commonKernel a χ _hχ hα hs φ
    (spectralStripJet_commonKernel (a := a) χ _hχ hα hs₀(hs))

/-- Paper: Theorem 10.3.1.1(2) and (10.3.1.3)–(10.3.1.4), p. 448. The
trace of convolution is the absolutely convergent sum of the Mellin values at
the line zeros weighted by their surviving multiplicities.
Deviation: Apply the strict cutoff of §10.2 and use positive meromorphic
order to exclude poles. The dependent double sum is expressed as one family. -/
theorem spectralLineConvolution_trace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, h₀, hs₀(hs))
    let term (z : Z(χ)) := (N(χ, s, z) : ℂ) * M(φ, χ z.val.1, shift(0, z.val.2))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralConvolution (F := F) a h₀ hs₀(hs) φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace (H := H) T) := by
  let L := Z(χ)
  let term (z : L) := (N(χ, s, z) : ℂ) * M(φ, χ z.val.1, shift(0, z.val.2))
  let claim (l : ℝ) (hl : l ≤ 0) := ∀ T : nuclearEndomorphisms Q(a, hl, hs₀(hs)),
    T.val = spectralConvolution (F := F) a hl hs₀(hs) φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace T)
  have transport (l : ℝ) (hl : l ≤ 0) (h : l = 0) : claim l hl → claim 0 le_rfl := by
    subst l
    exact id
  apply transport (-0) (hStrip(le_refl (0 : ℝ))) neg_zero
  intro T hT
  let Z := Z(χ, 0)
  have hoff (z : Z) : z.val.2.1 = 0 := by simpa using z.property.1
  let e : L ≃ Z :=
    { toFun := fun z ↦ ⟨(z.val.1, 0, z.val.2), by simp, by simpa only [add_zero] using z.property⟩
      invFun := fun z ↦ ⟨(z.val.1, z.val.2.2), by simpa only [hoff z, add_zero] using z.property.2⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun z ↦ Subtype.ext (Prod.ext rfl (Prod.ext (hoff z).symm rfl)) }
  let u (z : Z) := (N(χ, 0, s, z) : ℂ) * M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))
  have hsum : HasSum u (hilbertTrace T) :=
    (spectralStripConvolution_trace (F := F) a χ _hχ le_rfl hs φ T hT).2
  have hterm (z : L) : u (e z) = term z := by
    simp only [u, e, Equiv.coe_fn_mk, term, add_zero, spectralStripMultiplicity_boundary
      (le_refl (0 : ℝ)) (Or.inr rfl)]
  have h := (e.hasSum_iff.mpr hsum).congr_fun fun z ↦ (hterm z).symm
  exact ⟨h.summable.norm, h⟩

end StripTraceFormula

/-- Paper: Theorem 10.3.1.1(3), p. 449. The singular values decay faster than every inverse power.
Deviation: Assume trace class for all tests. Factor the homogeneous radial profile into
finite sums of iterated convolutions of smooth compactly supported functions on ℝ.
The approximation-number product inequality then gives arbitrary polynomial decay. -/
theorem spectralLineIsotypeConvolution_rapid_approximationNumbers
    {s : ℝ} (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x)
    (_htrace : ∀ ψ : BruhatCompactSupport C𝔽,
      IsNuclearOperator (spectralConvolution (F := F) a h₀ hs₀(hs) ψ)) :
    let H := Qω(a, h₀, hs₀(hs), ω)
    let A : H →L[ℂ] H := spectralIsotypeConvolution (F := F) a h₀ hs₀(hs) ω φ
    ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n) atTop (𝓝 0) := by
  exact spectralApprox_isotype_rapid (F := F) a h₀ hs₀(hs) ω φ _hφ _htrace

/-- Paper: Theorem 10.3.1.1(3), p. 449. Convolution by a homogeneous
test acts by a strongly nuclear operator on the corresponding quotient isotype.
Deviation: Use the left-translation eigencharacter ω. -/
theorem spectralLineIsotypeConvolution_stronglyNuclear
    {s : ℝ} (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    let H := Qω(a, h₀, hs₀(hs), ω)
    IsStronglyNuclearBanachOperator (E := H) (G := H)
      (spectralIsotypeConvolution (F := F) a h₀ hs₀(hs) ω φ) := by
  exact isStronglyNuclearBanachOperator_of_rapid_approximationNumbers _
    (spectralLineIsotypeConvolution_rapid_approximationNumbers (F := F) a hs ω φ _hφ
      (spectralLineConvolution_nuclear (F := F) a hs))

/-- Cyclicity identifies the trace with its restriction when the range lies in an isometric copy. -/
private theorem spectralIsotype_trace_of_range {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [PolynormableSpace ℂ H] [PolynormableSpace ℂ K]
    (A : nuclearEndomorphisms H) (D : nuclearEndomorphisms K)
    (J : K →L[ℂ] H) (P : H →L[ℂ] K) (hPJ : LeftInverse P J)
    (hr : ∀ x, A.val x ∈ range J) (hJ : ∀ y, A.val (J y) = J (D.val y)) :
    hilbertTrace A = hilbertTrace D := by
  let B := P.comp A.val
  have hB : IsNuclearOperator B := by
    obtain ⟨c, Λ, v, hc, hΛ, hv, hsum⟩ :=
      (isNuclearOperator_iff_isBanachNuclear A.val).mp A.property
    refine (isNuclearOperator_iff_isBanachNuclear B).mpr
      ⟨c, Λ, P ∘ v, hc, hΛ, (P.continuous.tendsto' 0 0 (map_zero P)).comp hv, fun x ↦ ?_⟩
    simpa only [B, Function.comp_apply, ContinuousLinearMap.comp_apply, map_smul]
      using P.hasSum (hsum x)
  have hJB : J.comp B = A.val := by
    ext x
    obtain ⟨y, hy⟩ := hr x
    change J (P (A.val x)) = A.val x
    rw [← hy, hPJ y]
  have hBJ : B.comp J = D.val := by
    ext y
    exact (congrArg P (hJ y)).trans (hPJ _)
  have hn := isNuclearOperator_factor_comps J hPJ.injective B hB
  calc
    hilbertTrace A = hilbertTrace ⟨J.comp B, hn.2⟩ :=
      congrArg (hilbertTrace (H := H)) (Subtype.ext hJB.symm)
    _ = hilbertTrace ⟨B.comp J, hn.1⟩ := by
      rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
      exact (nuclearTrace_factor_comps (hilbert_approximationProperty (H := K))
        (hilbert_approximationProperty (H := H)) J hPJ.injective B hB).symm
    _ = hilbertTrace D := congrArg (hilbertTrace (H := K)) (Subtype.ext hBJ)

/-- Check range containment and intertwining on quotient representatives before comparing traces. -/
private theorem spectralIsotype_trace_representatives {H K V W : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [PolynormableSpace ℂ H] [PolynormableSpace ℂ K]
    (A : nuclearEndomorphisms H) (D : nuclearEndomorphisms K)
    (S : Submodule ℂ H) [CompleteSpace S] (U : K ≃ₗᵢ[ℂ] S)
    (q : V → K) (π : W → H) (i : V → W) (B : V → V) (C : W → W)
    (hq : Surjective q) (hU : ∀ v, (U (q v) : H) = π (i v))
    (hr : range A.val ⊆ range (fun v ↦ π (i v)))
    (hD : ∀ v, D.val (q v) = q (B v))
    (hA : ∀ w, A.val (π w) = π (C w)) (hB : ∀ v, C (i v) = i (B v)) :
    hilbertTrace A = hilbertTrace D := by
  let J := S.subtypeL.comp U.toContinuousLinearEquiv.toContinuousLinearMap
  let P := U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp S.orthogonalProjectionOnto
  have hPJ : LeftInverse P J := fun x ↦ by
    change U.symm (S.orthogonalProjectionOnto (U x : H)) = x
    rw [S.orthogonalProjectionOnto_mem_subspace_eq_self, U.symm_apply_apply]
  apply spectralIsotype_trace_of_range A D J P hPJ
  · intro x
    obtain ⟨v, hv⟩ := hr ⟨x, rfl⟩
    exact ⟨q v, (hU v).trans hv⟩
  · intro y
    obtain ⟨v, rfl⟩ := hq y
    change A.val (U (q v) : H) = (U (D.val (q v)) : H)
    rw [hU, hA, hB, hD, hU]

/-- The isometric quotient-isotype inclusion intertwines the two convolutions on representatives. -/
private theorem spectralIsotype_trace_eq (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x)
    (hA : IsNuclearOperator (spectralConvolution (F := F) a hI hs φ))
    (D : nuclearEndomorphisms Qω(a, hI, hs, ω))
    (hD : D.val = spectralIsotypeConvolution (F := F) a hI hs ω φ) :
    hilbertTrace ⟨spectralConvolution (F := F) a hI hs φ, hA⟩ = hilbertTrace D := by
  have hiso := spectralSobolevIsotypeQuotient_isometry (F := F) a hI hs ω
  with_reducible obtain ⟨ρQ, _, _, U, hU⟩ := hiso
  let S := actionIsotype (ρQ.comp (ideleClassNorm F).ker.subtype) ω
  let : CompleteSpace S := (isClosed_actionIsotype _ _).completeSpace_coe
  let : PolynormableSpace ℂ Qω(a, hI, hs, ω) :=
    (norm_withSeminorms ℂ Qω(a, hI, hs, ω)).toPolynormableSpace
  let q := spectralSobolevIsotypeQuotient_mk (F := F) a hI hs ω
  let N := Θ(a, hI, hs)
  let B := (testAction(l, r, s, hI, hs) φ).restrict
    (hardySobolevTestAction_preserves_spectralIsotype (F := F) hI hs ω φ)
  refine spectralIsotype_trace_representatives _ D S U q N.mkQ Subtype.val B
    (testAction(l, r, s, hI, hs) φ) (spectralSobolevIsotypeQuotient_mk_surjective a hI hs ω) hU
    (spectralConvolution_range_isotype (F := F) a hI hs ω φ hφ) ?_
    (spectralConvolution_mkQ (F := F) a hI hs φ) (fun _ ↦ rfl)
  intro v
  exact (congrArg (fun L : Qω(a, hI, hs, ω) →L[ℂ] Qω(a, hI, hs, ω) ↦
    L (q v)) hD).trans
    (spectralIsotypeConvolution_mkQ (F := F) a hI hs ω φ v)

/-- Haar translation forces the Mellin transform of a homogeneous test to vanish off its character. -/
private theorem spectralIsotype_mellin_eq_zero
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {ω η : PontryaginDual C₁} (hne : η ≠ ω) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) (z : ℂ) :
    M(φ, χ η, z) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : C₁, (η k : ℂ) ≠ (ω k : ℂ) := by
    by_contra! heq
    exact hne (DFunLike.ext _ _ fun k ↦ Subtype.ext (heq k))
  let ξ := ideleClassNormTwist (F := F) (χ η) z
  have hkξ : ξ k.val = (η k : ℂ) := by
    have h := DFunLike.congr_fun (hχ η) k
    change (χ η) k.val = η k at h
    change (χ η k.val : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ z = _
    rw [k.property]
    simpa using congrArg (fun u : Circle ↦ (u : ℂ)) h
  rw [(spectralConvolution_mellin_integrable φ (χ η) z).2]
  let I := ∫ g, φ.val g * ξ g ∂μ𝔽
  have heq : (ω k : ℂ) * I = (η k : ℂ) * I := calc
    _ = ∫ g, φ.val (k.val⁻¹ * g) * ξ g ∂μ𝔽 := by
      rw [← integral_const_mul]
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      rw [hφ, mul_assoc]
    _ = ∫ g, φ.val (k.val⁻¹ * (k.val * g)) * ξ (k.val * g) ∂μ𝔽 :=
      (integral_mul_left_eq_self (fun g ↦ φ.val (k.val⁻¹ * g) * ξ g) k.val).symm
    _ = (η k : ℂ) * I := by
      rw [← integral_const_mul]
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      rw [inv_mul_cancel_left, map_mul, hkξ]
      ring
  exact (mul_eq_mul_right_iff.mp heq).resolve_left hk.symm

/-- A sum on pairs supported on one character is the sum over that character's fiber. -/
private theorem spectralIsotype_trace_fiber {Ω X : Type*} (ω : Ω) (p : Ω → X → Prop)
    (f : {z : Ω × X // p z.1 z.2} → ℂ) {L : ℂ}
    (hn : Summable (fun z ↦ ‖f z‖)) (hsum : HasSum f L)
    (hzero : ∀ z, z.val.1 ≠ ω → f z = 0) :
    let j (x : {x : X // p ω x}) : {z : Ω × X // p z.1 z.2} := ⟨(ω, x.val), x.property⟩
    Summable (fun x ↦ ‖f (j x)‖) ∧ HasSum (fun x ↦ f (j x)) L := by
  let j (x : {x : X // p ω x}) : {z : Ω × X // p z.1 z.2} := ⟨(ω, x.val), x.property⟩
  have hj : Injective j := fun x y h ↦ Subtype.ext (congrArg (fun z ↦ z.val.2) h)
  have hoff (z) (hz : z ∉ range j) : f z = 0 := by
    apply hzero
    rcases z with ⟨⟨η, x⟩, hx⟩
    rintro rfl
    exact hz ⟨⟨x, hx⟩, rfl⟩
  exact ⟨(hj.summable_iff (fun z hz ↦ by simp [hoff z hz])).mpr hn,
    (hj.hasSum_iff hoff).mpr hsum⟩

/-- Paper: Theorem 10.3.1.1(3) and (10.3.1.5), p. 449. The isotype
trace is the absolutely convergent zero sum of its base character.
Deviation: Use the strict cutoff and the left-translation eigencharacter ω
as in spectralConvolution_range_isotype. -/
theorem spectralLineIsotypeConvolution_trace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    let H := Qω(a, h₀, hs₀(hs), ω)
    let term (t : {t : ℝ // 0 < order(χ ω, shift(a, t))}) :=
      (spectralBoundaryMultiplicity s (mult(χ ω, shift(a, t.val))) : ℂ) *
        M(φ, χ ω, shift(0, t.val))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralIsotypeConvolution (F := F) a h₀ hs₀(hs) ω φ →
      Summable (fun t ↦ ‖term t‖) ∧ HasSum term (hilbertTrace (H := H) T) := by
  intro H term D hD
  let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
  have hA : IsNuclearOperator A := spectralLineConvolution_nuclear (F := F) a hs φ
  have hfull := spectralLineConvolution_trace (F := F) a χ _hχ hs φ ⟨A, hA⟩ rfl
  have ht := spectralIsotype_trace_eq (F := F) a h₀ hs₀(hs) ω φ _hφ hA D hD
  have sub := spectralIsotype_trace_fiber ω (fun η t ↦ 0 < order(χ η, shift(a, t)))
    (fun z ↦ (N(χ, s, z) : ℂ) * M(φ, χ z.val.1, shift(0, z.val.2))) hfull.1 hfull.2
    (fun z hz ↦ by rw [spectralIsotype_mellin_eq_zero χ _hχ hz φ _hφ, mul_zero])
  exact ⟨sub.1, ht ▸ sub.2⟩

end Line

section Strip

variable (a : ℝ)

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

-- TODO(paper-gap): The strip synthesis gap in §10.2 remains. The proof on
-- p. 455 also replaces log powers of unbounded order by a fixed Sobolev
-- weight and concludes only p > 1 for the displayed scalar sum.

section StripJetConvolutionBounds

section

open Metric

variable {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [T2Space G] (μ : Measure G) [IsLocallyFiniteMeasure μ]
    (l : G → ℝ) (φ : G → ℂ)

private def stripMellinMoment (z : ℂ) (q : ℕ) :=
  ∫ g, φ g * Complex.exp (z * (l g : ℂ)) * (l g : ℂ) ^ q ∂μ

private theorem stripMellinMoment_hasDerivAt (hl : Continuous l) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (z : ℂ) (q : ℕ) :
    HasDerivAt (fun w ↦ stripMellinMoment μ l φ w q) (stripMellinMoment μ l φ z (q + 1)) z := by
  let K := tsupport φ
  let F (w : ℂ) (g : G) := φ g * Complex.exp (w * (l g : ℂ)) * (l g : ℂ) ^ q
  let D (w : ℂ) (g : G) := φ g * Complex.exp (w * (l g : ℂ)) * (l g : ℂ) ^ (q + 1)
  have hF (w) : Continuous (F w) := by dsimp [F]; fun_prop
  have hD : Continuous (fun p : ℂ × G ↦ D p.1 p.2) := by dsimp [D]; fun_prop
  obtain ⟨B, hB⟩ := ((isCompact_closedBall z 1).prod hc).exists_bound_of_continuousOn hD.continuousOn
  let bound := K.indicator (fun _ ↦ B)
  have hbound : Integrable bound μ :=
    (integrable_indicator_iff hc.measurableSet).mpr (integrableOn_const hc.measure_lt_top.ne)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := D)
    (bound := bound) (Metric.closedBall_mem_nhds z zero_lt_one)
    (Eventually.of_forall (fun w ↦ (hF w).aestronglyMeasurable))
    ((hF z).integrable_of_hasCompactSupport (hc.mul_right.mul_right))
    ((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall (fun g w hw ↦ ?_)) hbound (Eventually.of_forall (fun g w _ ↦ ?_))).2
  · by_cases hg : g ∈ K
    · rw [show bound g = B from indicator_of_mem hg _]
      exact hB (w, g) ⟨hw, hg⟩
    · simp [bound, D, hg, image_eq_zero_of_notMem_tsupport hg]
  · simpa only [F, D, pow_succ, id_eq] using
      (((((hasDerivAt_id w).mul_const (l g : ℂ)).cexp).const_mul (φ g)).mul_const ((l g : ℂ) ^ q) |>.congr_deriv
        (by simp; ring))

private theorem stripMellinMoment_cauchy (hl : Continuous l) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (z : ℂ) (q : ℕ) {R M : ℝ} (hR : 0 < R)
    (hM : ∀ w ∈ sphere z R, ‖stripMellinMoment μ l φ w 0‖ ≤ M) :
    ‖stripMellinMoment μ l φ z q‖ ≤ q.factorial * M / R ^ q := by
  have hder (n : ℕ) : iteratedDeriv n (fun w ↦ stripMellinMoment μ l φ w 0) = (fun w ↦ stripMellinMoment μ l φ w n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      funext w
      rw [iteratedDeriv_succ, ih, (stripMellinMoment_hasDerivAt μ l φ hl hφ hc w n).deriv]
  have hol : Differentiable ℂ (fun w ↦ stripMellinMoment μ l φ w 0) :=
    fun w ↦ (stripMellinMoment_hasDerivAt μ l φ hl hφ hc w 0).differentiableAt
  simpa only [hder] using Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le q hR hol.diffContOnCl hM

end

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem stripRectangles_of_rankOne_majorant {J Z : Type*}
    (A : H →L[ℂ] H) (x : J → H) (L : J → StrongDual ℂ H) (N : Z → ℕ)
    (j : (z : Z) → Fin (N z) → J) (e : Z ↪ ℕ × ℕ)
    (g : Z → ℝ) (hg : Summable g)
    (h : ∀ z, (∑ m : Fin (N z), ‖(L (j z m)).comp A‖ * ‖x (j z m)‖) ≤ g z) :
    SpectralRectanglesTraceCauchy (fun i ↦ spectralConvolutionFiniteSum A x L
      (((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn) N j) := by
  classical
  let T (z : Z) (m : Fin (N z)) : nuclearEndomorphisms H :=
    ⟨((L (j z m)).comp A).smulRight (x (j z m)), smulRight_mem_nuclearEndomorphisms _ _⟩
  let R (z : Z) := ∑ m, T z m
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let : NormedAddCommGroup (nuclearEndomorphisms H) :=
    NormedAddCommGroup.ofCore (traceNorm_normedSpaceCore (H := H))
  let : SeminormedAddCommGroup (nuclearEndomorphisms H) :=
    (inferInstance : NormedAddCommGroup (nuclearEndomorphisms H)).toSeminormedAddCommGroup
  let : MetricSpace (nuclearEndomorphisms H) := NormedAddCommGroup.toMetricSpace
  let : PseudoMetricSpace (nuclearEndomorphisms H) := MetricSpace.toPseudoMetricSpace
  let : UniformSpace (nuclearEndomorphisms H) := PseudoMetricSpace.toUniformSpace
  have hR (z : Z) : ‖R z‖ ≤ g z := by
    apply (norm_sum_le Finset.univ (T z)).trans
    change (∑ m, traceNorm (T z m)) ≤ g z
    simpa only [T, traceNorm_smulRight] using h z
  have hc := cauchySeq_finset_of_norm_bounded_eventually hg (Eventually.of_forall hR)
  intro ε hε
  obtain ⟨S, hS⟩ := (Metric.cauchySeq_iff (u := fun s : Finset Z ↦ ∑ z ∈ s, R z)).mp hc ε hε
  let i := S.sup (fun z ↦ (e z).1)
  let k := S.sup (fun z ↦ (e z).2)
  let E (v : ℕ × ℕ) := ((Finset.Iic v.1).product (Finset.Iic v.2)).preimage e e.injective.injOn
  have hsub (v : ℕ × ℕ) (hv : (i, k) ≤ v) : S ≤ E v := by
    intro z hz
    simpa [E] using And.intro ((Finset.le_sup hz).trans hv.1) ((Finset.le_sup hz).trans hv.2)
  have heq (v : ℕ × ℕ) : (∑ z ∈ E v, R z).val = spectralConvolutionFiniteSum A x L (E v) N j := by
    simp only [R, T, Submodule.coe_sum, spectralConvolutionFiniteSum]
  refine ⟨(i, k), fun v w hv hw ↦ ⟨(∑ z ∈ E v, R z) - (∑ z ∈ E w, R z), ?_,?_⟩⟩
  · exact congrArg₂ (· - ·) (heq _) (heq _)
  · have hdist (T U : nuclearEndomorphisms H) : dist T U = traceNorm (T - U) := by
      rw [dist_eq_norm]
      rfl
    have hr := hS (E v) (hsub v hv) (E w) (hsub w hw)
    rwa [hdist] at hr

end
variable {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)

local notation "logNorm" => (logIdeleClassNorm F)
local notation "D" => spectralSobolevDualEmbedding F a (hStrip(hα)) hs₀(hs)
local notation "raw(" χ ", " j ")" =>
  spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "jet(" z ", " m ")" => ⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩
local notation "J(" χ ")" => SpectralStripJetIndex (F := F) χ a α s

private def stripJetMomentWeight (α s b x : ℝ) :=
  Real.exp (2 * b * x) / intervalSobolevDensity (-α) α s x

private def stripJetWeightedMoment (α s b : ℝ) (k : ℕ) (x : ℝ) :=
  |x| ^ (2 * k) * stripJetMomentWeight α s b x

private theorem stripMoment_density_pos (α s x : ℝ) : 0 < intervalSobolevDensity (-α) α s x :=
  mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

private theorem stripJetMomentWeight_pos {α s b x : ℝ} (_hα : 0 ≤ α) : 0 < stripJetMomentWeight α s b x :=
  div_pos (Real.exp_pos _) (stripMoment_density_pos α _ _)

private theorem stripJetMomentWeight_shift {α s b : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hb : b ∈ Icc (-α) α)
    (x d : ℝ) : stripJetMomentWeight α s b x ≤ Real.exp ((4 * α + s) * |d|) * stripJetMomentWeight α s b (x + d) := by
  let density := intervalSobolevDensity (-α) α s
  have hweight : 0 < density x := stripMoment_density_pos α _ _
  have hshifted : 0 < density (x + d) := stripMoment_density_pos α _ _
  have hdx : density (x + d) ≤ (Real.exp (α * |d|) * Real.exp (|d| * (s / 2))) ^ 2 * density x := by
    have h := intervalSobolevDensity_add_le (-α) α s hs d x
    rw [add_comm d x] at h
    refine h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ _) hweight.le)
    apply mul_le_mul _ _ (by positivity) (Real.exp_pos _).le
    · apply max_le <;> apply Real.exp_le_exp.mpr
      · calc - α * d = α * (-d) := by ring
             _ ≤ _ := mul_le_mul_of_nonneg_left (neg_le_abs _) hα
      · exact mul_le_mul_of_nonneg_left (le_abs_self _) hα
    · rw [Real.exp_mul]
      exact Real.rpow_le_rpow (by positivity) (by simpa [add_comm] using Real.add_one_le_exp |d|) (by positivity)
  have hbd : -(b * d) ≤ α * |d| := calc
    _ ≤ |b * d| := neg_le_abs _
    _ = |b| * |d| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (abs_le.mpr hb) (abs_nonneg _)
  dsimp only [stripJetMomentWeight]
  change Real.exp (2 * b * x) / density x ≤ _ * (Real.exp (2 * b * (x + d)) / density (x + d))
  rw [← mul_div_assoc, div_le_div_iff₀ hweight hshifted]
  calc
    _ ≤ Real.exp (2 * b * x) * ((Real.exp (α * |d|) * Real.exp (|d| * (s / 2))) ^ 2 * density x) :=
      mul_le_mul_of_nonneg_left hdx (Real.exp_pos _).le
    _ = Real.exp (2 * b * x + 2 * (α * |d| + |d| * (s / 2))) * density x := by
      rw [← Real.exp_add, sq, ← Real.exp_add, mul_comm (2 : ℝ) _, two_mul,
        ←mul_assoc, ← Real.exp_add]
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr _) hweight.le
      nlinarith only [hbd]

/-- Translating by log norm plus and minus the missing order supplies the factorial and
binomial factors in every term of the translated jet. Haar invariance handles both signs. -/

private theorem stripJetWeightedMoment_compare {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (l : G → ℝ) (hadd : ∀ x y, l (x * y) = l y + l x)
    (onto : Surjective l) {α s b : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hb : b ∈ Icc (-α) α)
    (k m : ℕ) (hk : k ≤ m) (hi : Integrable (fun g : G ↦ stripJetWeightedMoment α s b m (l g)) μ) :
    let q := m - k
    ((m.choose k : ℝ) * (q.factorial : ℝ)) ^ 2 * (∫ g, stripJetWeightedMoment α s b k (l g) ∂μ) ≤
      2 * Real.exp ((4 * α + s) * q) * (∫ g, stripJetWeightedMoment α s b m (l g) ∂μ) := by
  intro q
  let c : ℝ := (m.choose k : ℝ) * (q.factorial : ℝ)
  let A := Real.exp ((4 * α + s) * q)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hm (x : ℝ) : 0 ≤ stripJetWeightedMoment α s b m x := mul_nonneg (by positivity) (stripJetMomentWeight_pos hα).le
  have hq : (q.factorial : ℝ) ≤ (q : ℝ) ^ q := by exact_mod_cast Nat.factorial_le_pow q
  have hp (x : ℝ) : c * |x| ^ k ≤ (|x| + q) ^ m := by
    rw [add_pow]
    apply le_trans _ (Finset.single_le_sum (f := fun i ↦ |x| ^ i * (q : ℝ) ^ (m - i) * (m.choose i : ℝ))
      (fun i _ ↦ by positivity) (Finset.mem_range.mpr (by omega : k < m + 1)))
    calc c * |x| ^ k = (|x| ^ k * (q.factorial : ℝ)) * (m.choose k : ℝ) := by dsimp [c]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by positivity)) (by positivity)
  have part (x d : ℝ) (hd : |d| = q) (hxd : |x + d|=|x| + q) :
      c ^ 2 * stripJetWeightedMoment α s b k x ≤ A * stripJetWeightedMoment α s b m (x + d) := by
    have hw := stripJetMomentWeight_shift hα hs hb x d
    rw [hd] at hw
    calc
      _ = (c * |x| ^ k) ^ 2 * stripJetMomentWeight α s b x := by
        unfold stripJetWeightedMoment
        rw [show 2 * k = k * 2 by omega, pow_mul]
        ring
      _ ≤ ((|x| + q) ^ m) ^ 2 * (A * stripJetMomentWeight α s b (x + d)) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) (hp x) _) hw (stripJetMomentWeight_pos hα).le (by positivity)
      _ = _ := by unfold stripJetWeightedMoment; rw [hxd, show 2 * m=m * 2 by omega, pow_mul]; ring
  have point (x : ℝ) : c ^ 2 * stripJetWeightedMoment α s b k x ≤
      A * stripJetWeightedMoment α s b m (x + q) + A * stripJetWeightedMoment α s b m (x + -(q : ℝ)) := by
    by_cases hx : 0 ≤ x
    · exact (part x q (abs_of_nonneg (Nat.cast_nonneg _)) (by rw [abs_of_nonneg (by positivity), abs_of_nonneg hx])).trans
        (le_add_of_nonneg_right (mul_nonneg hA (hm _)))
    · apply le_trans _ (le_add_of_nonneg_left (mul_nonneg hA (hm _)))
      apply part
      · rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
      · rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) q]), abs_of_nonpos (le_of_not_ge hx)]; ring
  obtain ⟨u, hu⟩ := onto (q : ℝ)
  obtain ⟨v, hv⟩ := onto (-(q : ℝ))
  let M := fun g : G ↦ stripJetWeightedMoment α s b m (l g)
  have hM : Integrable M μ := hi
  have i₁ := (hM.comp_mul_left u).const_mul A
  have i₂ := (hM.comp_mul_left v).const_mul A
  calc
    _ = ∫ g : G, c ^ 2 * stripJetWeightedMoment α s b k (l g) ∂μ := (integral_const_mul ..).symm
    _ ≤ ∫ g : G, (A * M (u * g) + A * M (v * g)) ∂μ := by
      apply integral_mono_of_nonneg (.of_forall fun g ↦ mul_nonneg (sq_nonneg _)
        (mul_nonneg (by positivity) (stripJetMomentWeight_pos hα).le)) (i₁.add i₂)
      apply Eventually.of_forall
      intro g
      change c ^ 2 * stripJetWeightedMoment α s b k (l g) ≤ A * M (u * g) + A * M (v * g)
      simpa only [M, hadd, hu, hv] using point (l g)
    _ = _ := by
      rw [integral_add i₁ i₂, integral_const_mul, integral_const_mul, integral_mul_left_eq_self M u,
        integral_mul_left_eq_self M v]
      dsimp [M, A]
      ring

private theorem stripWeightedMoment_norm {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (w : G → ℝ) (hw : Measurable w) (hw₀ : ∀ y, 0 ≤ w y) (f : G → ℂ)
    (hf : MemLp f 2 (μ.withDensity (fun y ↦ ENNReal.ofReal (w y)))) :
    Integrable (fun y ↦ w y * ‖f y‖ ^ 2) μ ∧
      ‖hf.toLp f‖ ^ 2 = ∫ y, w y * ‖f y‖ ^ 2 ∂μ := by
  let ν := μ.withDensity (fun y ↦ ENNReal.ofReal (w y))
  let u : Lp ℂ 2 ν := hf.toLp f
  have H := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have htop : ∀ᵐ y ∂μ, ENNReal.ofReal (w y) < ⊤ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hre (y) : (ENNReal.ofReal (w y)).toReal = w y := ENNReal.toReal_ofReal (hw₀ _)
  constructor
  · simpa only [hre, smul_eq_mul] using (integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal htop).mp H
  have hself : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  change ‖u‖ ^ 2 = _
  have hRe : (∫ g, inner ℂ (u g) (u g) ∂ν).re = ∫ g, (inner ℂ (u g) (u g)).re ∂ν :=
    (Complex.reCLM.integral_comp_comm (L2.integrable_inner u u)).symm
  rw [← hself, L2.inner_def, hRe]
  calc
    _ = ∫ y, ‖f y‖ ^ 2 ∂ν := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hf] with y hy
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (u y)).trans (congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hy)
    _ = _ := by
      rw [show ν = _ from rfl, integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal htop]
      simp only [hre, smul_eq_mul]
-- The pointwise norm computation is from the private jet-norm lemma in §10.2.

private theorem stripMoment_raw_norm_sq (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (g : C𝔽) :
    ‖spectralZeroJet χ b t k g‖ ^ 2 = Real.exp (2 * b * logNorm g) * (logNorm g) ^ (2 * k) := by
  have hpos : 0 < ((ideleClassNorm F g).val : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have htwist : ‖ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) g‖ =
      Real.exp (b * logNorm g) := by
    change ‖(χ g : ℂ) *
      (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Real.rpow_def_of_pos hpos,
      mul_comm]
  change ‖ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) g *
    (logNorm g : ℂ) ^ k‖ ^ 2 = _
  rw [norm_mul, htwist, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hexp : Real.exp (b * logNorm g) ^ 2 = Real.exp (2 * b * logNorm g) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hpow : (|logNorm g| ^ k) ^ 2 = (logNorm g) ^ (2 * k) := by
    calc
      (|logNorm g| ^ k) ^ 2 = (|logNorm g| ^ 2) ^ k := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
      _ = ((logNorm g) ^ 2) ^ k := congrArg (fun y : ℝ ↦ y ^ k) (sq_abs (logNorm g))
      _ = (logNorm g) ^ (2 * k) := (pow_mul _ _ _).symm
  rw [hexp, hpow]

/-- Compare lower and higher jet functionals using only their realization in the reciprocal
weighted Haar space. Membership of each retained jet supplies endpoint integrability. -/

private theorem stripJet_lower_order_norm_le
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (f : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (z : Z(χ, α)) (m k : Fin (N(χ, α, s, z))) (hk : k ≤ m) :
    let q := m.val - k.val
    (m.val.choose k.val : ℝ) * (q.factorial : ℝ) * ‖f (jet(z, k))‖ ≤
      2 * (Real.exp ((4 * α + s) / 2)) ^ q * ‖f (jet(z, m))‖ := by
  intro q
  let b := z.val.2.1
  let p (n : Fin (N(χ, α, s, z))) := ‖f (jet(z, n))‖
  let w (g : C𝔽) : ℝ := (intervalSobolevDensity (-α) α s (logNorm g))⁻¹
  let mod : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  have hlog : Continuous logNorm := continuous_logModule' (G := C𝔽) mod
  have hw : Measurable w := ((continuous_intervalSobolevDensity (-α) α s).comp hlog).measurable.inv
  have hw₀ (g : C𝔽) : 0 ≤ w g := inv_nonneg.mpr (stripMoment_density_pos α s _).le
  have hm (n : Fin (N(χ, α, s, z))) :
      Integrable (fun g : C𝔽 ↦ stripJetWeightedMoment α s b n.val (logNorm g)) μ𝔽 ∧
      p n ^ 2 = ∫ g : C𝔽, stripJetWeightedMoment α s b n.val (logNorm g) ∂μ𝔽 := by
    let j : J(χ) := jet(z, n)
    have hd := (spectralSobolevDualEmbedding_isometry_range (F := F) a (hStrip(hα)) hs₀(hs)).1.dist_eq (f j) 0
    have he : ‖D (f j)‖ = ‖f j‖ := by simpa only [map_zero, dist_eq_norm, sub_zero] using hd
    have H := stripWeightedMoment_norm μ𝔽 w hw hw₀ (raw(χ, j)) (spectralStripJet_memLp χ hα hs₀(hs) j)
    have H' (g : C𝔽) : w g * ‖raw(χ, j) g‖ ^ 2 = stripJetWeightedMoment α s b n.val (logNorm g) := by
      rw [stripMoment_raw_norm_sq]
      change (intervalSobolevDensity (-α) α s (logNorm g))⁻¹ *
          (Real.exp (2 * b * logNorm g) * (logNorm g) ^ (2 * n.val)) = _
      have hp : |logNorm g| ^ (2 * n.val) = (logNorm g) ^ (2 * n.val) := by rw [pow_mul, pow_mul, sq_abs]
      simp only [stripJetWeightedMoment, stripJetMomentWeight, hp, div_eq_mul_inv]
      ring
    refine ⟨H.1.congr (.of_forall H'),?_⟩
    change ‖f j‖ ^ 2 = _
    rw [← he, hj, H.2]
    exact integral_congr_ae (.of_forall H')
  have hadd (g v : C𝔽) : logNorm (g * v) = logNorm v + logNorm g := by
    dsimp only [logIdeleClassNorm]
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
      (NNReal.coe_ne_zero.2 (ideleClassNorm F v).ne_zero), add_comm]
  have onto : Surjective logNorm := by
    intro r
    let y : ℝ≥0 := ⟨Real.exp r, (Real.exp_pos r).le⟩
    have hy : y ≠ 0 := (show 0 < y from (NNReal.coe_pos).mp (Real.exp_pos r)).ne'
    let t : ℝ≥0ˣ := Units.mk0 y hy
    obtain ⟨g, hg⟩ := (ideleGroup_quotient.{_,0} F).2.2.2.2.2.2.2.2.2.1 t
    refine ⟨g,?_⟩
    change Real.log ((ideleClassNorm F g).val : ℝ) = r
    rw [hg]
    exact Real.log_exp _
  have c := stripJetWeightedMoment_compare μ𝔽 logNorm hadd onto hα hs₀(hs) z.property.1 k.val m.val hk (hm m).1
  let R := Real.exp ((4 * α + s) / 2)
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have he : Real.exp ((4 * α + s) * q) = (R ^ q) ^ 2 := by
    dsimp [R]
    rw [← Real.exp_nat_mul, sq, ← Real.exp_add]
    congr 1; ring
  change ((m.val.choose k.val : ℝ) * (q.factorial : ℝ)) ^ 2 * _ ≤ 2 * Real.exp ((4 * α + s) * q) * _ at c
  rw [he] at c
  have hsq : ((m.val.choose k.val : ℝ) * (q.factorial : ℝ) * p k) ^ 2 ≤
      2 * (R ^ q) ^ 2 * (p m) ^ 2 := by
    rw [mul_pow, (hm k).2, (hm m).2]
    exact c
  have hpos : 0 ≤ 2 * R ^ q * p m := by dsimp [p]; positivity
  change _ ≤ 2 * R ^ q * p m
  nlinarith only [hsq, hpos, (sq_nonneg (R ^ q * p m))]
section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (μ : Measure G) [μ.IsHaarMeasure] (n : G →* ℝ≥0ˣ) (hn : Continuous n)
    (l r s₀ : ℝ) (hl : l ≤ r) (hs₀ : 0 ≤ s₀)
local notation "Uraw" => CompactIntervalSobolev μ (fun g : G ↦ Real.log ((n g).val:ℝ)) l r s₀
local notation "ncont" => (⟨n, hn⟩ : G →ₜ* ℝ≥0ˣ)

private abbrev stripJetTranslation : G →* (Uraw →L[ℂ] Uraw) :=
  hardySobolevTranslation μ ncont l r s₀ hl hs₀

private theorem stripJetTranslation_apply (g : G) (v : Uraw) :
    (stripJetTranslation μ n hn l r s₀ hl hs₀ g v : G → ℂ) =ᵐ[μ] (fun x ↦ v (g⁻¹ * x)) :=
  hardySobolevTranslation_apply μ ncont l r s₀ hl hs₀ g v

private abbrev stripJetTestAction (φ : BruhatCompactSupport G) : Uraw →L[ℂ] Uraw :=
  hardySobolevTestAction μ ncont l r s₀ hl hs₀ φ

private theorem stripJetTranslation_pettis (φ : BruhatCompactSupport G)
    (v : Uraw) (ℓ : StrongDual ℂ Uraw) :
    ℓ (stripJetTestAction μ n hn l r s₀ hl hs₀ φ v) =
      ∫ g, ℓ (φ.val g • stripJetTranslation μ n hn l r s₀ hl hs₀ g v) ∂μ := by
  let τ := stripJetTranslation μ n hn l r s₀ hl hs₀
  have hP := bruhatRegularizedAction_apply μ τ
    (exists_hardySobolevTranslation μ ncont l r s₀ hl hs₀).choose_spec.2 φ v
  exact congrArg (fun p : PettisWeakCompletion Uraw ↦
    (show Module.Dual ℂ (StrongDual ℂ Uraw) from p) ℓ) hP.2

end

private theorem stripJet_scalar_integral {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (u v w : G → ℂ) (c y : ℂ) :
    (∫ g, u g * ((v g * w g * c) * y) ∂μ) = c * (∫ g, u g * v g * w g ∂μ) * y := by
  rw [← integral_const_mul, ← integral_mul_const]
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  ring

private theorem stripJet_integrated_product_congr {G : Type*} [MeasurableSpace G] (μ : Measure G)
    {u v : G → ℂ} (j : G → ℂ) (h : u =ᵐ[μ] v) :
    (∫ x, u x * j x ∂μ) = ∫ x, v x * j x ∂μ :=
  integral_congr_ae (h.mono fun x hx ↦ congrArg (· * j x) hx)

private theorem stripJet_all_translated_moments (η : PontryaginDual C𝔽) (b t : ℝ)
    (m : ℕ) (v : W(-α, α, s))
    (hint : ∀ i ≤ m, Integrable (fun x ↦ v x * spectralZeroJet (F := F) η b t i x) μ𝔽)
    (g : C𝔽) :
    ∫ y : C𝔽, (v : C𝔽 → ℂ) (g⁻¹ * y) * spectralZeroJet (F := F) η b t m y ∂μ𝔽 =
      ∑ i : Fin (m + 1), (ideleClassNormTwist (F := F) η (shift(b, t)) g *
        (logNorm g : ℂ) ^ (m - i.val) * (m.choose i.val : ℂ)) *
        ∫ y, v y * spectralZeroJet (F := F) η b t i.val y ∂μ𝔽 := by
  let T := ideleClassNormTwist (F := F) η ((b : ℂ) + (t : ℂ) * Complex.I)
  let L (y : C𝔽) : ℂ := logNorm y
  let c (i : ℕ) := T g * L g ^ (m - i) * (m.choose i : ℂ)
  have hlog (y : C𝔽) : L (g * y) = L y + L g := by
    dsimp only [L, logIdeleClassNorm]
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
      (NNReal.coe_ne_zero.2 (ideleClassNorm F y).ne_zero), Complex.ofReal_add, add_comm]
  have hsum (y : C𝔽) : v y * spectralZeroJet (F := F) η b t m (g * y) =
      ∑ i ∈ Finset.range (m + 1), c i * (v y * spectralZeroJet (F := F) η b t i y) := by
    change v y * (T (g * y) * L (g * y) ^ m) = _
    rw [map_mul, hlog, add_pow]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change v y * (T g * T y * (L y ^ i * L g ^ (m - i) * (m.choose i : ℂ))) =
      (T g * L g ^ (m - i) * (m.choose i : ℂ)) * (v y * (T y * L y ^ i))
    ring
  let J := spectralZeroJet (F := F) η b t m
  let H (y : C𝔽) := v (g⁻¹ * y) * J y
  calc
    _ = ∫ y, H y ∂μ𝔽 := rfl
    _ = ∫ y, H (g * y) ∂μ𝔽 := (integral_mul_left_eq_self H g).symm
    _ = ∫ y, v y * J (g * y) ∂μ𝔽 := by simp only [H, inv_mul_cancel_left]
    _ = _ := by
      simp_rw [show ∀ y, v y * J (g * y) = _ from hsum]
      rw [integral_finsetSum _ fun i hi ↦ (hint i (Finset.mem_range_succ_iff.mp hi)).const_mul (c i)]
      simp_rw [integral_const_mul]
      exact (Fin.sum_univ_eq_sum_range (fun i ↦ c i * ∫ y, v y * spectralZeroJet (F := F) η b t i y ∂μ𝔽) _).symm

/-- The transpose convolution acts by the complete triangular matrix of logarithmic Mellin
moments, before passing to the kernel of the lower coordinates. -/

private theorem spectralStripConvolution_all_jet_coefficients
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (f : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽) (z : Z(χ, α)) (m : Fin (N(χ, α, s, z)))
    (u : Q(a, hStrip(hα), hs₀(hs))) :
    f (jet(z, m)) (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ u) =
      ∑ i : Fin (m.val + 1), (m.val.choose i.val : ℂ) *
        (∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g *
           (logNorm g : ℂ) ^ (m.val - i.val) ∂μ𝔽) *
        f (jet(z, (⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ : Fin (N(χ, α, s, z))))) u := by
  let θ : Submodule ℂ W(-α, α, s) := globalThetaSobolev F (α := -α) (β := α) (s := s) a (hStrip(hα)) hs₀(hs)
  obtain ⟨v, hv⟩ := θ.mkQ_surjective u
  let J (i : ℕ) := spectralZeroJet (χ z.val.1) z.val.2.1 z.val.2.2 i
  let j : J(χ) := jet(z, m)
  have hnorm : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  let mod : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, hnorm⟩
  let τ := stripJetTranslation (G := C𝔽) μ𝔽 (ideleClassNorm F) hnorm (-α) α s (hStrip(hα)) hs₀(hs)
  let ℓ := (f j).comp θ.mkQL
  let η := ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2))
  have heval (j : J(χ)) (w : W(-α, α, s)) :=
    spectralStripConvolution_jet_eval (a := a) hα hs χ j (f j) (hj j) w
  have hint (i : ℕ) (hi : i ≤ m.val) : Integrable (fun y ↦ v y * J i y) μ𝔽 := by
    let k : Fin (N(χ, α, s, z)) := ⟨i, hi.trans_lt m.isLt⟩
    exact (heval (jet(z, k)) v).1
  let idx (i : Fin (m.val + 1)) : Fin (N(χ, α, s, z)) := ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩
  let y (i : Fin (m.val + 1)) := f (jet(z, idx i)) u
  let h (i : Fin (m.val + 1)) (g : C𝔽) := (η g * (logNorm g : ℂ) ^ (m.val - i.val) * (m.val.choose i.val : ℂ)) * y i
  have hi (i : Fin (m.val + 1)) : (∫ x, v x * J i.val x ∂μ𝔽) = y i :=
    (heval (jet(z, idx i)) v).2.symm.trans (congrArg (f (jet(z, idx i))) hv)
  have hτ (g : C𝔽) : ℓ (τ g v) = ∑ i : Fin (m.val + 1), h i g := by
    have haeFormula := stripJetTranslation_apply (G := C𝔽) μ𝔽 (ideleClassNorm F) hnorm (-α) α s (hStrip(hα)) hs₀(hs) g
    have hae := haeFormula v
    have hshift := stripJet_integrated_product_congr μ𝔽 (J m.val) hae
    have ht := stripJet_all_translated_moments (F := F) (α := α) (s := s) (χ z.val.1) z.val.2.1 z.val.2.2 m.val v hint g
    refine (heval j (τ g v)).2.trans (hshift.trans (ht.trans ?_))
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg ((η g * (logNorm g : ℂ) ^ (m.val - i.val) * (m.val.choose i.val : ℂ)) * ·) (hi i)
  have hφ : Continuous φ.val := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hg (i : Fin (m.val + 1)) : Integrable (fun g : C𝔽 ↦ φ.val g * h i g) μ𝔽 := by
    have hl : Continuous (fun g : C𝔽 ↦ (logNorm g : ℂ)) := Complex.continuous_ofReal.comp (continuous_logModule' (G := C𝔽) mod)
    exact (hφ.mul (((η.continuous.mul (hl.pow _)).mul continuous_const).mul continuous_const)).integrable_of_hasCompactSupport
      (show HasCompactSupport φ.val from φ.property.2).mul_right
  have pettis := stripJetTranslation_pettis (G := C𝔽) μ𝔽 (ideleClassNorm F) hnorm (-α) α s (hStrip(hα)) hs₀(hs) φ
  have he := pettis v ℓ
  have conv := spectralConvolution_mkQ (F := F) a (hStrip(hα)) hs₀(hs) φ
  simp only at conv
  calc
    _ = ℓ (stripJetTestAction (G := C𝔽) μ𝔽 (ideleClassNorm F) hnorm (-α) α s (hStrip(hα)) hs₀(hs) φ v) :=
      (congrArg (fun w ↦ f j (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ w)) hv.symm).trans
        (congrArg (f j) (conv v))
    _ = ∫ g, ℓ (φ.val g • τ g v) ∂μ𝔽 := he
    _ = ∫ g, ∑ i : Fin (m.val + 1), φ.val g * h i g ∂μ𝔽 := integral_congr_ae (.of_forall fun g ↦ by
      exact (map_smul ℓ (φ.val g) (τ g v)).trans
        ((congrArg (φ.val g * ·) (hτ g)).trans (Finset.mul_sum ..)))
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ ↦ hg i)]
      apply Finset.sum_congr rfl
      intro i _
      change (∫ g : C𝔽, φ.val g * ((η g * (logNorm g : ℂ) ^ (m.val - i.val) * (m.val.choose i.val : ℂ)) * y i) ∂μ𝔽) =
        (m.val.choose i.val : ℂ) * (∫ g : C𝔽, φ.val g * η g * (logNorm g : ℂ) ^ (m.val - i.val) ∂μ𝔽) * y i
      exact stripJet_scalar_integral μ𝔽 φ.val η (fun g ↦ (logNorm g : ℂ) ^ (m.val - i.val)) _ _

private theorem stripMellinMoment_eq_twisted_integral (χ : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽)
    (w : ℂ) (q : ℕ) :
    (∫ g : C𝔽, φ.val g * ideleClassNormTwist χ w g * (logNorm g : ℂ) ^ q ∂μ𝔽) =
      stripMellinMoment μ𝔽 logNorm (fun g ↦ φ.val g * (χ g : ℂ)) w q := by
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  have hp : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have he : ideleClassNormTwist χ w g = (χ g : ℂ) * Complex.exp (w * (logNorm g : ℂ)) := by
    change (χ g : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ w) = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]
    exact congrArg ((χ g : ℂ) * ·) (congrArg Complex.exp (mul_comm _ _))
  rw [he]; ring

private theorem stripJet_geometric_sum_le (n : ℕ) :
    ∑ i : Fin (n + 1), (1 / 2 : ℝ) ^ (n - i.val) ≤ 2 := by
  have eq : (∑ i : Fin (n + 1), (1 / 2 : ℝ) ^ (n - i.val)) =
      ∑ i ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ i := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (1 / 2 : ℝ) ^ (n - i)) (n + 1)]
    simpa using Finset.sum_range_reflect (fun i ↦ (1 / 2 : ℝ) ^ i) (n + 1)
  rw [eq]
  have hs := hasSum_geometric_of_lt_one (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  exact (hs.summable.sum_le_tsum _ (fun _ _ ↦ by positivity)).trans_eq (by rw [hs.tsum_eq]; norm_num)

private theorem stripJet_scaled_coefficient_le {c f r u v M t : ℝ} (q : ℕ) (hr : 0 < r) (hM : 0 ≤ M)
    (hc : 0 ≤ c) (hv : 0 ≤ v)
    (hw : c * f * v ≤ 2 * r ^ q * u) (ht : t ≤ f * M / (2 * r) ^ q) :
    c * t * v ≤ (1 / 2 : ℝ) ^ q * (2 * M * u) := by
  have hrq : 0 < r ^ q := pow_pos hr _
  have h₂ : (0 : ℝ) < 2 ^ q := by positivity
  calc
    _ ≤ c * (f * M / (2 * r) ^ q) * v := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hc) hv
    _ = c * f * v * (M / (2 ^ q * r ^ q)) := by rw [mul_pow]; ring
    _ ≤ (2 * r ^ q * u) * (M / (2 ^ q * r ^ q)) := mul_le_mul_of_nonneg_right hw (by positivity)
    _ = _ := by rw [div_pow]; field_simp; ring

private theorem stripJet_dual_norm_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (c : ℂ) (f : StrongDual ℂ V) : ‖c • f‖ = ‖c‖ * ‖f‖ := norm_smul c f

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. A bound for the scalar Mellin transform on one
circle bounds each retained coordinate after convolution, uniformly in the order of the jet.
The same radius works throughout the closed strip, including its admissible endpoint jets. -/
theorem spectralStripConvolution_jet_norm_le_mellin_circle
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (f : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽) (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))) (M : ℝ) (hM : 0 ≤ M)
    (hMellin : ∀ w ∈ Metric.sphere (shift(z.val.2.1, z.val.2.2)) (2 * Real.exp ((4 * α + s) / 2)),
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖ ≤ M) :
    ‖(f (jet(z, m))).comp (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ)‖ ≤
      4 * M * ‖f (jet(z, m))‖ := by
  let R := Real.exp ((4 * α + s) / 2)
  let w₀ := shift(z.val.2.1, z.val.2.2)
  let t (q : ℕ) := ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w₀ g * (logNorm g : ℂ) ^ q ∂μ𝔽
  let idx (i : Fin (m.val + 1)) : Fin (N(χ, α, s, z)) := ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩
  let L (i : Fin (m.val + 1)) := f (jet(z, idx i))
  let coeff (i : Fin (m.val + 1)) : ℂ := (m.val.choose i.val : ℂ) * t (m.val - i.val)
  have hφ : Continuous φ.val := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have ht (q : ℕ) : ‖t q‖ ≤ q.factorial * M / (2 * R) ^ q := by
    rw [show t q = _ from stripMellinMoment_eq_twisted_integral (χ z.val.1) φ w₀ q]
    apply stripMellinMoment_cauchy μ𝔽 logNorm (fun g : C𝔽 ↦ φ.val g * (χ z.val.1 g : ℂ)) (continuous_logModule' (G := C𝔽) m𝔽)
      (hφ.mul (continuous_subtype_val.comp (χ z.val.1).continuous))
      (show HasCompactSupport φ.val from φ.property.2).mul_right _ _ (by dsimp [R]; positivity)
    intro w hw
    have h := stripMellinMoment_eq_twisted_integral (χ z.val.1) φ w 0
    simp only [pow_zero, mul_one] at h
    exact (congrArg norm h.symm).le.trans (hMellin w hw)
  have hL : (f (jet(z, m))).comp (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ) =
      ∑ i : Fin (m.val + 1), coeff i • L i := by
    ext u
    simp only [sum_apply, ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul]
    exact spectralStripConvolution_all_jet_coefficients a hα hs χ f hj φ z m u
  rw [hL]
  apply (norm_sum_le Finset.univ (fun i : Fin (m.val + 1) ↦ coeff i • L i)).trans
  calc
    _ ≤ ∑ i : Fin (m.val + 1), (1 / 2 : ℝ) ^ (m.val - i.val) * (2 * M * ‖f (jet(z, m))‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [stripJet_dual_norm_smul]
      change ‖(m.val.choose i.val : ℂ) * t (m.val - i.val)‖ * ‖L i‖ ≤ _
      rw [norm_mul, Complex.norm_natCast]
      exact stripJet_scaled_coefficient_le _ (Real.exp_pos _) hM (Nat.cast_nonneg _) (norm_nonneg (L i))
        (stripJet_lower_order_norm_le a hα hs χ f hj z m (idx i) (Nat.le_of_lt_succ i.isLt)) (ht _)
    _ = (∑ i : Fin (m.val + 1), (1 / 2 : ℝ) ^ (m.val - i.val)) * (2 * M * ‖f (jet(z, m))‖) := (Finset.sum_mul ..).symm
    _ ≤ 2 * (2 * M * ‖f (jet(z, m))‖) := mul_le_mul_of_nonneg_right (stripJet_geometric_sum_le _) (by positivity)
    _ = _ := by ring

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. Rectangular sections are Cauchy in trace norm
if the scalar Mellin circle bounds, multiplied by the sums of the coordinate projection
norms at their respective zeros, are summable. This criterion applies to every injection
of the zero sites into the quadrant. -/
theorem spectralStripConvolution_traceCauchy_of_summable_jetNorms
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (f : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽) (M : Z(χ, α) → ℝ) (hM : ∀ z, 0 ≤ M z)
    (hMellin : ∀ z : Z(χ, α), ∀ w ∈ Metric.sphere (shift(z.val.2.1, z.val.2.2)) (2 * Real.exp ((4 * α + s) / 2)),
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖ ≤ M z)
    (hcoordinates : Summable (fun z : Z(χ, α) ↦ M z *
      ∑ m : Fin (N(χ, α, s, z)), ‖f (jet(z, m))‖ * ‖x (jet(z, m))‖))
    (e : Z(χ, α) ↪ ℕ × ℕ) :
    SpectralRectanglesTraceCauchy (fun i ↦ spectralConvolutionFiniteSum
      (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ) x f
      (((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn)
      (fun z : Z(χ, α) ↦ N(χ, α, s, z)) (fun z m ↦ jet(z, m))) := by
  apply stripRectangles_of_rankOne_majorant _ _ _ _ _ e _ (hcoordinates.mul_left 4)
  intro z
  change _ ≤ 4 * (M z * ∑ m : Fin (N(χ, α, s, z)), ‖f (jet(z, m))‖ * ‖x (jet(z, m))‖)
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (spectralStripConvolution_jet_norm_le_mellin_circle a hα hs χ f hj φ z m _ (hM z) (hMellin z))
    (norm_nonneg _)

/-- Quotient translations act on every jet at one zero by the finite binomial matrix. -/
private theorem strip_translation_finite_block
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (L : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs))) (hj : ∀ j, D (L j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))) :
    ∃ ρ : C𝔽 →* (Q(a, hStrip(hα), hs₀(hs)) →L[ℂ] Q(a, hStrip(hα), hs₀(hs))),
      ∀ (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))) (g : C𝔽) (u : Q(a, hStrip(hα), hs₀(hs))),
        L (jet(z,m)) (ρ g u) = ∑ i : Fin (m.val+1),
          (ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1,z.val.2.2)) g *
          (logIdeleClassNorm F g : ℂ)^(m.val-i.val) * (m.val.choose i.val : ℂ)) *
          L (jet(z,(⟨i.val,(Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ : Fin (N(χ, α, s, z))))) u := by
  let hS := le_of_lt (zero_lt_one.trans hs)
  let hI := neg_le_self hα
  let θ := globalThetaSobolev F (α := -α) (β := α) (s := s) a hI hS
  obtain ⟨ρ,hρ,_⟩ := spectralSobolevIsotypeQuotient_isometry (F:=F) a hI hS (1 : PontryaginDual C₁)
  refine ⟨ρ,?_⟩
  intro z m g u
  obtain ⟨v,hv⟩ := θ.mkQ_surjective u
  let J (i : ℕ) := spectralZeroJet (χ z.val.1) z.val.2.1 z.val.2.2 i
  let j : J(χ) := jet(z,m)
  have hnorm : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  let τ := stripJetTranslation (G := C𝔽) μ𝔽 (ideleClassNorm F) hnorm (-α) α s hI hS
  have heval (k : J(χ)) := spectralStripConvolution_jet_eval (a:=a) hα hs χ k (L k) (hj k)
  have hint (i : ℕ) (hi : i ≤ m.val) : Integrable (fun y ↦ v y * J i y) μ𝔽 := by
    let k : Fin (N(χ, α, s, z)) := ⟨i, hi.trans_lt m.isLt⟩
    exact (heval (jet(z,k)) v).1
  have hae := stripJetTranslation_apply (G := C𝔽) μ𝔽 (ideleClassNorm F) hnorm (-α) α s hI hS g v
  have ht := stripJet_all_translated_moments (F:=F) (α:=α) (s:=s) (χ z.val.1) z.val.2.1 z.val.2.2 m.val v hint g
  rw [← hv, hρ]
  refine (heval j (τ g v)).2.trans ((stripJet_integrated_product_congr μ𝔽 (J m.val) hae).trans (ht.trans ?_))
  apply Finset.sum_congr rfl
  intro i _
  let k : Fin (N(χ, α, s, z)) := ⟨i.val,(Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩
  exact congrArg (_ * ·) (heval (jet(z,k)) v).2.symm

open Matrix in
/-- At a uniformly bounded jet length the moment interpolation matrix is fixed once and for all. -/
private theorem finite_jet_moment_interpolation (k : ℕ) :
    ∃ T : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ), ∀ (a : Fin k → ℂ) (q : Fin k),
      ∑ j : Fin k, T a j * (j.val : ℂ)^q.val = a q := by
  classical
  let v : Fin k → ℂ := fun j ↦ (j.val : ℂ)
  let V := Matrix.vandermonde v
  have hv : Function.Injective v := fun i j h ↦ Fin.ext (by dsimp [v] at h; exact_mod_cast h)
  have hd : IsUnit V.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hv)
  refine ⟨(V⁻¹.vecMulLinear).toContinuousLinearMap,?_⟩
  intro a q
  change ((a ᵥ* V⁻¹) ᵥ* V) q = _
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hd, Matrix.vecMul_one]

/-- On a complete block of length at most k, its convolution is a finite linear
combination of fixed translations, with weights given by interpolation of its moments. -/
private theorem complete_block_moment_interpolation {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {k n : ℕ} (hn : n ≤ k) (L : Fin n → StrongDual ℂ V) (x : Fin n → V)
    (A : V →L[ℂ] V) (U : Fin k → (V →L[ℂ] V)) (κ : Fin k → ℂ) (hκ : ∀ j, κ j ≠ 0)
    (b c : Fin k → ℂ)
    (hm : ∀ q : Fin k, ∑ j : Fin k, c j * (j.val : ℂ)^q.val = b q)
    (hA : ∀ (m : Fin n) (v : V), L m (A v) =
      ∑ i : Fin (m.val+1), (m.val.choose i.val : ℂ) *
        b ⟨m.val-i.val, by have H := m.isLt; omega⟩ *
        L ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ v)
    (hU : ∀ (m : Fin n) (j : Fin k) (v : V), L m (U j v) =
      ∑ i : Fin (m.val+1), (κ j * (j.val : ℂ)^(m.val-i.val) * (m.val.choose i.val : ℂ)) *
        L ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ v) :
    (∑ m : Fin n, ((L m).comp A).smulRight (x m)) =
      ∑ j : Fin k, (c j / κ j) • ((∑ m : Fin n, (L m).smulRight (x m)).comp (U j)) := by
  classical
  have hrow (m : Fin n) (v : V) : L m (A v) = ∑ j, (c j / κ j) * L m (U j v) := by
    rw [hA]
    simp_rw [hU,Finset.mul_sum]
    rw [Finset.sum_comm (f := fun j (i : Fin (m.val+1)) ↦ _)]
    apply Finset.sum_congr rfl
    intro i _
    let q : Fin k := ⟨m.val-i.val, by have H := m.isLt; omega⟩
    let l := L ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ v
    change (m.val.choose i.val : ℂ) * b q * l = _
    rw [← hm q,Finset.mul_sum,Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp only [q,l]
    field_simp [hκ j]

  ext v
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, smul_apply]
  simp_rw [hrow,Finset.sum_smul,Finset.smul_sum,smul_smul]
  exact Finset.sum_comm

private theorem finite_jet_translation_insertion_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {k : ℕ} (U : Fin k → (V →L[ℂ] V)) (P B : V →L[ℂ] V) (κ c : Fin k → ℂ)
    (r : Fin k → ℝ) {M : ℝ} (hM : 0 ≤ M) (hr : ∀ j, ‖(κ j)⁻¹‖ ≤ r j)
    (hc : ∀ j, ‖c j‖ ≤ M) (hB : B = ∑ j : Fin k, (c j / κ j) • (P.comp (U j))) :
    ‖B‖ ≤ (∑ j : Fin k, r j * ‖U j‖) * M * ‖P‖ := by
  rw [hB,Finset.sum_mul,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [norm_smul,div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (M*r j)*(‖P‖ * ‖U j‖) := mul_le_mul (mul_le_mul (hc j) (hr j) (norm_nonneg _) hM)
      (ContinuousLinearMap.opNorm_comp_le ..) (norm_nonneg _) (mul_nonneg hM ((norm_nonneg _).trans (hr j)))
    _ = _ := by ring

private theorem strip_block_jet_moments_cauchy (χ : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽)
    (w₀ : ℂ) {M : ℝ} (hM : ∀ w∈Metric.sphere w₀ 1, ‖∫ g, φ.val g * ideleClassNormTwist χ w g ∂μ𝔽‖ ≤ M)
    (q : ℕ) : ‖∫ g, φ.val g * ideleClassNormTwist χ w₀ g * (logIdeleClassNorm F g : ℂ)^q ∂μ𝔽‖ ≤ q.factorial*M := by
  rw [stripMellinMoment_eq_twisted_integral χ φ w₀ q]
  have hφ := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  let n : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F,(isProperMap_ideleClassNorm F).continuous⟩
  simpa only [one_pow,div_one] using
    stripMellinMoment_cauchy μ𝔽 (logIdeleClassNorm F) (fun g : C𝔽 ↦ φ.val g * (χ g : ℂ)) (continuous_logModule' n)
      (hφ.mul (continuous_subtype_val.comp χ.continuous)) (show HasCompactSupport φ.val from φ.property.2).mul_right w₀ q
      (show (0:ℝ) < 1 by norm_num) (fun w hw ↦ by
        have h := stripMellinMoment_eq_twisted_integral χ φ w 0
        simp only [pow_zero,mul_one] at h
        exact (congrArg norm h.symm).le.trans (hM w hw))

private theorem strip_twist_norm (χ : PontryaginDual C𝔽) (b t : ℝ) (g : C𝔽) :
    ‖ideleClassNormTwist χ (shift(b,t)) g‖ = Real.exp (b * logIdeleClassNorm F g) := by
  have hp : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change ‖(χ g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (shift(b,t))‖ = _
  rw [norm_mul,Circle.norm_coe,one_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Real.rpow_def_of_pos hp,mul_comm]

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The operator norm of every complete convolved zero block of at most k jets
is controlled by its full projection and the Mellin transform on the unit circle.
Deviation: A conditional estimate on complete blocks in the proof of (10.3.2.6). -/
theorem spectralStripConvolution_complete_block_circle (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (L : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hj : ∀ i, D (L i) = (spectralStripJet_memLp χ hα hs₀(hs) i).toLp (raw(χ, i))) (k : ℕ) :
    ∃ C ≥ (0:ℝ), ∀ (z : Z(χ, α)), N(χ, α, s, z) ≤ k →
      ∀ (φ : BruhatCompactSupport C𝔽) (M : ℝ), 0 ≤ M →
      (∀ w∈Metric.sphere (shift(z.val.2.1,z.val.2.2)) 1, ‖∫ g, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖ ≤ M) →
      ‖∑ m : Fin (N(χ, α, s, z)), ((L (jet(z,m))).comp (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ)).smulRight (x (jet(z,m)))‖ ≤
        C * M * ‖∑ m : Fin (N(χ, α, s, z)), (L (jet(z,m))).smulRight (x (jet(z,m)))‖ := by
  obtain ⟨ρ,hρ⟩ := strip_translation_finite_block a hα hs χ L hj
  obtain ⟨T,hT⟩ := finite_jet_moment_interpolation k
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let g (j : Fin k) : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F (e j.val))
  have hg (j) : logIdeleClassNorm F (g j) = j.val := by
    change Real.log ((ideleClassNorm F (g j)).val : ℝ) = _
    rw [show ideleClassNorm F (g j) = _ from canonicalIdeleNormSection_rightInverse F (e j.val)]
    exact Real.log_exp _
  let U (j : Fin k) := ρ (g j)
  let r (j : Fin k) := Real.exp (α*j.val)
  let S := ∑ j : Fin k, r j * ‖U j‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  refine ⟨S * ‖T‖ * k.factorial, by positivity,?_⟩
  intro z hn φ M hM hc
  let w₀ := shift(z.val.2.1,z.val.2.2)
  let κ (j : Fin k) := ideleClassNormTwist (χ z.val.1) w₀ (g j)
  let b (q : Fin k) := ∫ y, φ.val y * ideleClassNormTwist (χ z.val.1) w₀ y * (logIdeleClassNorm F y : ℂ)^q.val ∂μ𝔽
  have hb : ‖b‖ ≤ k.factorial * M := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro q
    exact (strip_block_jet_moments_cauchy (χ z.val.1) φ w₀ hc q.val).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le (Nat.le_of_lt q.isLt)) hM)
  have hκnorm (j) : ‖κ j‖ = Real.exp (z.val.2.1 * j.val) := by
    simpa only [hg] using strip_twist_norm (χ z.val.1) z.val.2.1 z.val.2.2 (g j)
  have hκ (j) : κ j ≠ 0 := norm_ne_zero_iff.mp ((hκnorm j).trans_ne (Real.exp_pos _).ne')
  have hr (j) : ‖(κ j)⁻¹‖ ≤ r j := by
    rw [norm_inv,hκnorm,←Real.exp_neg]; apply Real.exp_le_exp.mpr
    rw [←neg_mul]; exact mul_le_mul_of_nonneg_right (by linarith [z.property.1.1]) (Nat.cast_nonneg _)
  let l (m : Fin (N(χ, α, s, z))) := L (jet(z,m))
  let y (m : Fin (N(χ, α, s, z))) := x (jet(z,m))
  have row := complete_block_moment_interpolation hn l y (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ) U κ hκ b (T b) (hT b)
    (spectralStripConvolution_all_jet_coefficients a hα hs χ L hj φ z)
    (fun m j v ↦ by simpa only [hg,Complex.ofReal_natCast] using hρ z m (g j) v)
  have est := finite_jet_translation_insertion_norm U _ _ κ (T b) r
    (show 0 ≤ ‖T‖ * (k.factorial * M) by positivity) hr
    (fun j ↦ (norm_le_pi_norm (T b) j).trans ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _)))) row
  convert est using 1
  change S * ‖T‖ * _ * _ * _ = S * (_ * (_ * _)) * _
  ring

/-- A diagonal flag of jet rows annihilates the k-th power of the centered operator. -/
private theorem finite_block_triangular_annihilates {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {n k : ℕ} (hn : n ≤ k) (L : Fin n → StrongDual ℂ V) (x : Fin n → V)
    (A : V →L[ℂ] V) (c : ℂ)
    (ht : ∀ (m : Fin n) (u : V), (∀ i < m, L i u = 0) → L m (A u) = c*L m u) :
    (∑ m : Fin n, (L m).smulRight (x m)) * ((c • (1 : V →L[ℂ] V)) - A)^k = 0 := by
  let R := (c • (1 : V →L[ℂ] V)) - A
  have hv (j : ℕ) (m : Fin n) (hm : m.val < j) (u : V) : L m ((R^j) u) = 0 := by
    induction j generalizing m with
    | zero => omega
    | succ j ih =>
      rw [pow_succ']
      change L m (c • ((R^j) u) - A ((R^j) u)) = 0
      rw [map_sub,map_smul, ht m _ (fun i hi ↦ ih i (by change i.val < m.val at hi; omega))]
      exact sub_self _
  ext u
  change (∑ m : Fin n, (L m).smulRight (x m)) ((R^k) u) = 0
  simp only [sum_apply,ContinuousLinearMap.smulRight_apply]
  exact Finset.sum_eq_zero (fun m _ ↦ by rw [hv k m (m.isLt.trans_le hn),zero_smul])

/-- From a fixed uniform bound for the spectral parameter and the convolved blocks,
the eigenvalue to the power k controls each whole block. -/
private theorem bounded_blocks_control_power {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →L[ℂ] V) (k : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    ∃ B ≥ (0:ℝ), ∀ (P : V →L[ℂ] V) (c : ℂ), ‖c‖ ≤ M →
      P * (c • (1 : V →L[ℂ] V) - A)^k = 0 → ‖c‖^k * ‖P‖ ≤ ‖P*A‖ * B := by
  rcases subsingleton_or_nontrivial V with h | h
  · exact ⟨0,le_rfl,fun P _ _ _ ↦ by rw [Subsingleton.elim P 0]; simp⟩
  let := h
  let R := 1 + M * ‖(1 : V →L[ℂ] V)‖ + ‖A‖
  have hR : 1 ≤ R := by dsimp [R]; linarith [mul_nonneg hM (norm_nonneg (1 : V →L[ℂ] V)),norm_nonneg A]
  refine ⟨k*R^k,by positivity,?_⟩
  intro P c hc hnil
  let X := c • (1 : V →L[ℂ] V)
  let Y := X-A
  have hXY : Commute X Y := (Commute.refl X).sub_right ((Commute.one_left A).smul_left c)
  let W := ∑ i ∈ Finset.range k, X^i * Y^(k-1-i)
  have he : A * W = X^k - Y^k := by simpa only [Y,sub_sub_cancel] using hXY.mul_geom_sum₂ k
  have hPW : P*A*W = (c ^ k) • P := by
    rw [mul_assoc,he,mul_sub,hnil,sub_zero,show X^k = c ^ k • (1 : V →L[ℂ] V) by simp [X,smul_pow]]
    simp only [mul_smul_comm,mul_one]
  have hX : ‖X‖ ≤ M*‖(1 : V →L[ℂ] V)‖ := by rw [show ‖X‖ = _ from norm_smul c _]; gcongr
  have hx : ‖X‖ ≤ R := hX.trans (by dsimp [R]; linarith [norm_nonneg A])
  have hy : ‖Y‖ ≤ R := (norm_sub_le _ _).trans (by dsimp only [R]; linarith)
  have hW : ‖W‖ ≤ k*R^k := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i ∈ Finset.range k, R^k := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        apply (norm_mul_le ..).trans
        apply (mul_le_mul ((norm_pow_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) hx _)) ((norm_pow_le ..).trans
          (pow_le_pow_left₀ (norm_nonneg _) hy _)) (norm_nonneg _) (by positivity)).trans
        rw [← pow_add]; apply pow_le_pow_right₀ hR; have := Finset.mem_range.mp hi; omega
      _ = _ := by simp
  calc
    _ = ‖P*A*W‖ := by rw [hPW,norm_smul,norm_pow]
    _ ≤ ‖P*A‖ * (k*R^k) := (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left hW (norm_nonneg _))

private theorem strip_fixed_test_mellin_bound (φ : BruhatCompactSupport C𝔽) (α : ℝ) :
    ∃ M ≥ (0:ℝ), ∀ (χ : PontryaginDual C𝔽) (b t : ℝ), |b| ≤ α →
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist χ (shift(b,t)) g ∂μ𝔽‖ ≤ M := by
  let p (g : C𝔽) := ‖φ.val g‖ * Real.exp (α*|logIdeleClassNorm F g|)
  have hp : Integrable p μ𝔽 := by
    have hφ := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
    let n : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F,(isProperMap_ideleClassNorm F).continuous⟩
    exact (hφ.norm.mul (Real.continuous_exp.comp ((continuous_logModule' n).abs.const_mul α))).integrable_of_hasCompactSupport
      (show HasCompactSupport φ.val from φ.property.2).norm.mul_right
  refine ⟨∫ g,p g ∂μ𝔽, integral_nonneg (fun g ↦ mul_nonneg (norm_nonneg _) (Real.exp_pos _).le),?_⟩
  intro χ b t hb
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ ↦ norm_nonneg _)) hp
  refine ae_of_all _ fun g ↦ ?_
  change ‖φ.val g * ideleClassNormTwist χ (shift(b,t)) g‖ ≤ ‖φ.val g‖ * Real.exp (α*|logIdeleClassNorm F g|)
  rw [norm_mul,strip_twist_norm]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((le_abs_self _).trans
    ((abs_mul ..).le.trans (mul_le_mul_of_nonneg_right hb (abs_nonneg _))))) (norm_nonneg _)

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. If the complete block traces are
summable for a fixed test and every rank-one insertion, the product of the full projection norm
and the kth power of the Mellin absolute value is bounded at every site of jet length at most k.
Deviation: A necessary condition on the rank-one insertions in (10.3.2.6). -/
theorem spectralStripConvolution_mellin_pow_mul_block_norm_bound
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (L : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hj : ∀ i, D (L i) = (spectralStripJet_memLp χ hα hs₀(hs) i).toLp (raw(χ, i))) (φ : BruhatCompactSupport C𝔽)
    (h : ∀ (v : Q(a, hStrip(hα), hs₀(hs))) (g : StrongDual ℂ Q(a, hStrip(hα), hs₀(hs))),
      Summable (fun z : Z(χ, α) ↦ ∑ m : Fin (N(χ, α, s, z)),
        L (jet(z,m)) ((spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ) ((g.smulRight v) (x (jet(z,m))))))) (k : ℕ) :
    ∃ C ≥ (0:ℝ), ∀ z : Z(χ, α), N(χ, α, s, z) ≤ k →
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1,z.val.2.2)) g ∂μ𝔽‖^k *
        ‖∑ m : Fin (N(χ, α, s, z)), (L (jet(z,m))).smulRight (x (jet(z,m)))‖ ≤ C := by
  classical
  let A := (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ)
  let j (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))) : J(χ) := jet(z,m)
  obtain ⟨M,hM,hm⟩ := strip_fixed_test_mellin_bound φ α
  obtain ⟨B,hB,hb⟩ := bounded_blocks_control_power A k M hM
  obtain ⟨C,hC,hc⟩ := spectralConvolutionFiniteSum_singleton_norm_bound A x L _ j h
  refine ⟨C*B,mul_nonneg hC hB,?_⟩
  intro z hz
  let P := ∑ m : Fin (N(χ, α, s, z)), (L (j z m)).smulRight (x (j z m))
  let c := ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1,z.val.2.2)) g ∂μ𝔽
  have hnil := finite_block_triangular_annihilates hz (fun m ↦ L (j z m)) (fun m ↦ x (j z m)) A c
    (fun m u hu ↦ by
      have e := spectralStripConvolution_jet_top a hα hs χ L hj φ z m u hu
      rwa [(spectralConvolution_mellin_integrable _ _ _).2] at e)
  have hid : P * A = spectralConvolutionFiniteSum A x L {z} _ j := by
    ext u
    change P (A u) = _
    simp [P,spectralConvolutionFiniteSum,sum_apply]
  refine (hb P c (hm _ _ _ (abs_le.mpr z.property.1)) hnil).trans ?_
  rw [hid]
  exact mul_le_mul_of_nonneg_right (hc _) hB

end StripJetConvolutionBounds

/-- Paper: Theorem 10.3.2.1(1) and (10.3.2.1), p. 453. The rectangular
finite-rank sums over any enumeration of the strip zeros converge to convolution
in every Schatten class.
Deviation: The injections include finite or empty enumerations. The
interval is allowed to be a singleton and the jets use the strict boundary cutoff. -/
theorem spectralStripConvolution_schatten_tendsto (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ, α) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (p : ℝ) (hp : 1 ≤ p) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
    let S := schattenClass H H p hp
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, α, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)
    ∃ (hA : A ∈ S) (hB : ∀ ij, B ij ∈ S),
      Tendsto (fun ij ↦ schattenNorm (E := H) (F := H) (p := p) (hp := hp)
        (⟨B ij, hB ij⟩ - ⟨A, hA⟩ : S)) atTop (𝓝 0) := by
  let count (z : Z(χ, α)) := N(χ, α, s, z)
  let jet (z : Z(χ, α)) (m : Fin (count z)) : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let index (j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s) : (z : Z(χ, α)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩, ⟨j.val.2.2.2, j.property⟩⟩
  let equiv : ((z : Z(χ, α)) × Fin (count z)) ≃ SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact spectralConvolutionFiniteSum_limit_of_traceCauchy
    (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) x Λ e count jet
    _hb equiv.bijective p hp
    (spectralStripConvolution_traceCauchy (F := F) a χ _hχ hα hs φ eχ e _he x Λ _hb _hj)

/-- Paper: Theorem 10.3.2.1(2), p. 454. Convolution on the strip spectral
quotient is trace class for each test. -/
theorem spectralStripConvolution_nuclear {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    IsNuclearOperator (E := H) (F := H) (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  obtain ⟨_, x, Λ, hb, hj⟩ := spectralStripMarkushevichBasis (a := a) χ hχ hα hs₀(hs)
  obtain ⟨r, e, he⟩ := spectralLineConvolution_nuclear_indices χ
    (fun z : Z(χ, α) ↦ z.val.1) (fun z ↦ shift(a + z.val.2.1, z.val.2.2)) (by
      intro i j h
      have hrow := congrArg Prod.fst h
      have hre := congrArg (fun p ↦ (p.2 : ℂ).re) h
      have him := congrArg (fun p ↦ (p.2 : ℂ).im) h
      exact Subtype.ext (Prod.ext hrow
        (Prod.ext (by simpa using hre) (by simpa using him)))) (fun z ↦ z.property.2)
  obtain ⟨hA, _⟩ := spectralStripConvolution_schatten_tendsto (F := F) a χ hχ hα hs φ
    r e he x Λ hb hj 1 le_rfl
  exact (mem_traceClassOperators_iff_isNuclearOperator _).mp hA

-- TODO(paper-gap): (10.3.2.2), p. 454 asks for continuity of the strip convolution action in
-- trace norm. The printed proof of Theorem 10.3.2.1 replaces the scalar series (10.3.2.6) by
-- (10.3.2.7) and shows the latter converges for p > 1; but the constants C_{N,I,s}(phi) of
-- (10.3.2.11) carry the derivatives of the test itself, so this is an estimate at a fixed test
-- and yields no seminorm bound uniform in the test. The per-zero bounds (10.3.1.19)-(10.3.1.22),
-- which the proof says carry over, rest on the single biorthogonality constant C of (10.3.1.18),
-- which is Printed.spectralLineJet_uniformBiorthogonalBound, refuted in Sec3_Printed.lean. On the
-- strip N_{I,s} is unbounded for alpha > 0 (as the proof of 10.3.2.1 notes), so the jets of one
-- character grow with s and alpha as well. What is missing is a bound on the number of strip
-- zeros of L(s, chi w) with |Im s| <= T in the number of jet orders used, together with a
-- trace-norm estimate uniform in the test. A reduction of this statement to that single
-- seminorm estimate is blocked at elaboration: the linear lift into
-- nuclearEndomorphisms (Q a (hStrip hα) (hs₀ hs)) cannot be built by the anonymous constructor
-- of LinearMap (here LinearMap extends AddHom and MulActionHom, so the field literal
-- { toFun := ..., map_add' := ..., map_smul' := ... } is rejected by the parser), and building
-- it from an abstract function via AddHom exhausts the heartbeat budget in isDefEq and whnf on
-- that quotient type; see #5398.

/-- Paper: Theorem 10.3.2.1(2) and (10.3.2.2), p. 454. The convolution
action lifts to a linear map into the trace class, continuous at zero in trace norm. -/
theorem spectralStripConvolution_traceNorm_continuous {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    ∃ T : BruhatCompactSupport C𝔽 →ₗ[ℂ] nuclearEndomorphisms H,
      (∀ φ, (T φ).val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) ∧
      Tendsto (fun φ : BruhatCompactSupport C𝔽 ↦ traceNorm (H := H) (T φ)) (𝓝 0) (𝓝 0) := by
  intro H
  let A : BruhatCompactSupport C𝔽 →ₗ[ℂ] (H →L[ℂ] H) :=
    (spectralConvolution_isLinear (F := F) a hStrip(hα) hs₀(hs)).mk'
      (spectralConvolution (F := F) a hStrip(hα) hs₀(hs))
  exact spectralConvolution_traceNorm_lift bruhatCompactSupport_strictLF A
    (spectralConvolution_opNorm_continuous (F := F) a hStrip(hα) hs₀(hs))
    (spectralStripConvolution_nuclear (F := F) a hα hs)

/-- Paper: Theorem 10.3.2.1(2), p. 454. Taking the trace of convolution gives
a distribution on the Bruhat compactly supported test space. -/
theorem spectralStripConvolution_trace_distribution {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    ∃ D : StrongDual ℂ (BruhatCompactSupport C𝔽),
      ∀ (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms H),
        T.val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ →
        D φ = hilbertTrace (H := H) T := by
  have traceDistribution {X : Type _} {H : Type _} [AddCommGroup X] [Module ℂ X]
      [TopologicalSpace X] [IsTopologicalAddGroup X] [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (A : X → H →L[ℂ] H)
      (h : ∃ T : X →ₗ[ℂ] nuclearEndomorphisms H, (∀ x, (T x).val = A x) ∧
        Tendsto (fun x : X ↦ traceNorm (H := H) (T x)) (𝓝 0) (𝓝 0)) :
      ∃ D : StrongDual ℂ X, ∀ (x : X) (U : nuclearEndomorphisms H),
        U.val = A x → D x = hilbertTrace U := by
    obtain ⟨T, hT, ht⟩ := h
    obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
    let D : X →ₗ[ℂ] ℂ := L.comp T
    have hb (x : X) : ‖D x‖ ≤ traceNorm (T x) :=
      (congrArg (fun c : ℂ ↦ ‖c‖) (hL (T x))).le.trans (norm_hilbertTrace_le (T x))
    have hd : Continuous D := continuous_of_continuousAt_zero D <| by
      change Tendsto D (𝓝 0) (𝓝 (D 0))
      rw [D.map_zero]
      exact squeeze_zero_norm hb ht
    refine ⟨⟨D, hd⟩, fun x U hU ↦ ?_⟩
    have heq : T x = U := Subtype.ext ((hT x).trans hU.symm)
    exact (hL (T x)).trans (congrArg (hilbertTrace (H := H)) heq)
  exact traceDistribution (X := BruhatCompactSupport C𝔽) (H := Q(a, hStrip(hα), hs₀(hs)))
    (spectralConvolution (F := F) a hStrip(hα) hs₀(hs))
    (spectralStripConvolution_traceNorm_continuous (F := F) a hα hs)

/-- Paper: Theorem 10.3.2.1(3), p. 454. The singular values decay faster than every inverse power.
Deviation: Assume trace class for all tests. Factor the homogeneous radial profile into
finite sums of iterated convolutions of smooth compactly supported functions on ℝ.
The approximation-number product inequality then gives arbitrary polynomial decay. -/
theorem spectralStripIsotypeConvolution_rapid_approximationNumbers
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x)
    (_htrace : ∀ ψ : BruhatCompactSupport C𝔽,
      IsNuclearOperator (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) ψ)) :
    let H := Qω(a, hStrip(hα), hs₀(hs), ω)
    let A : H →L[ℂ] H := spectralIsotypeConvolution (F := F) a hStrip(hα) hs₀(hs) ω φ
    ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n) atTop (𝓝 0) := by
  exact spectralApprox_isotype_rapid (F := F) a hStrip(hα) hs₀(hs) ω φ _hφ _htrace

/-- Paper: Theorem 10.3.2.1(3), p. 454. Convolution by a homogeneous
test acts by a strongly nuclear operator on the corresponding quotient isotype.
Deviation: Use the left-translation eigencharacter ω. -/
theorem spectralStripIsotypeConvolution_stronglyNuclear
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    let H := Qω(a, hStrip(hα), hs₀(hs), ω)
    IsStronglyNuclearBanachOperator (E := H) (G := H)
      (spectralIsotypeConvolution (F := F) a hStrip(hα) hs₀(hs) ω φ) := by
  exact isStronglyNuclearBanachOperator_of_rapid_approximationNumbers _
    (spectralStripIsotypeConvolution_rapid_approximationNumbers (F := F) a hα hs ω φ _hφ
      (spectralStripConvolution_nuclear (F := F) a hα hs))

/-- Paper: Theorem 10.3.2.1(3) and (10.3.2.5), p. 454. The isotype
trace is the absolutely convergent zero sum of its base character.
Deviation: Use the strict cutoff and the left-translation eigencharacter ω
as in spectralConvolution_range_isotype. -/
theorem spectralStripIsotypeConvolution_trace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    let H := Qω(a, hStrip(hα), hs₀(hs), ω)
    let term (z : {z : ℝ × ℝ // z.1 ∈ Icc (-α) α ∧ 0 < order(χ ω, shift(a + z.1, z.2))}) :=
      (spectralStripMultiplicity α s z.val.1 (mult(χ ω, shift(a + z.val.1, z.val.2))) : ℂ) *
        M(φ, χ ω, shift(z.val.1, z.val.2))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralIsotypeConvolution (F := F) a hStrip(hα) hs₀(hs) ω φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace (H := H) T) := by
  intro H term D hD
  let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
  have hA : IsNuclearOperator A := spectralStripConvolution_nuclear (F := F) a hα hs φ
  have hfull := spectralStripConvolution_trace (F := F) a χ _hχ hα hs φ ⟨A, hA⟩ rfl
  have ht := spectralIsotype_trace_eq (F := F) a hStrip(hα) hs₀(hs) ω φ _hφ hA D hD
  have sub := spectralIsotype_trace_fiber ω
    (fun η (x : ℝ × ℝ) ↦ x.1 ∈ Icc (-α) α ∧ 0 < order(χ η, shift(a + x.1, x.2)))
    (fun z ↦ (N(χ, α, s, z) : ℂ) * M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))) hfull.1 hfull.2
    (fun z hz ↦ by rw [spectralIsotype_mellin_eq_zero χ _hχ hz φ _hφ, mul_zero])
  exact ⟨sub.1, ht ▸ sub.2⟩

end Strip

end RiemannMasullo
