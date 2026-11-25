module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv

/-! # Frequency windows for the complete zero blocks on the Sobolev line

The finite sections on pp. 448–451 retain all log jets at each selected zero. A kernel whose
frequency derivatives agree with the test at these sites and vanish on the other sites induces
exactly that finite section. Its weighted L¹ norm bounds the operator norm on the quotient.
This statement applies to kernels of unbounded support, including inverse Fourier transforms
of smooth compact frequency windows.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped NNReal

namespace RiemannMasullo.Isolated

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (s : ℝ) (hs : 0 ≤ s)

set_option quotPrecheck false
local notation "logMod" => (fun x : G ↦ Real.log ((m x).val : ℝ))
local notation "W" => CompactIntervalSobolev μ logMod 0 0 s
local notation "τ" => hardySobolevTranslation μ m 0 0 s le_rfl hs
local notation "weight(" g ")" => (1 + |logMod (g)|) ^ (s / 2)

/-- A measurable kernel with finite polynomially weighted L¹ norm gives a bounded
operator on the zero-width Hardy–Sobolev space. All unitary modulations obey the
same weighted Young estimate with constant one. Each operator preserves every
closed translation-invariant subspace and agrees with the project's existing
action whenever the modulated kernel is Schwartz–Bruhat. On a translation eigenfunctional at `γ`
the modulated operator multiplies by the Fourier transform of the original kernel
at `χ⁻¹ * γ`. Every integral taking values in the Sobolev space is on one vector. -/
theorem spectralLine_exists_modulated_window_operators
    (k : G → ℂ) (hk : AEMeasurable k μ)
    (hpoly : Integrable (fun g ↦ ‖k g‖ * weight(g)) μ) :
    ∃ A : PontryaginDual G → W →L[ℂ] W,
      (∀ χ u, Integrable (fun g ↦ (k g * (χ g : ℂ)) • τ g u) μ ∧
        A χ u = ∫ g, (k g * (χ g : ℂ)) • τ g u ∂μ) ∧
      (∀ χ, ‖A χ‖ ≤ ∫ g, ‖k g‖ * ‖τ g‖ ∂μ) ∧
      ((∫ g, ‖k g‖ * ‖τ g‖ ∂μ) ≤ ∫ g, ‖k g‖ * weight(g) ∂μ) ∧
      (∀ (N : Submodule ℂ W), IsClosed (N : Set W) →
        (∀ g u, u ∈ N → τ g u ∈ N) → ∀ χ u, u ∈ N → A χ u ∈ N) ∧
      (∀ (χ : PontryaginDual G) (f : SchwartzBruhat G), (∀ g, f g = k g * (χ g : ℂ)) →
        A χ = (existsUnique_schwartzBruhat_zeroLineAction μ m s hs).exists.choose f) ∧
      ∀ (χ γ : PontryaginDual G) (δ : StrongDual ℂ W),
        (∀ g u, δ (τ g u) = star (γ g : ℂ) * δ u) →
        ∀ u, δ (A χ u) = lcaFourier μ k (χ⁻¹ * γ) * δ u := by
  let K (χ : PontryaginDual G) (g : G) := k g * (χ g : ℂ)
  have hK (χ : PontryaginDual G) : AEStronglyMeasurable (K χ) μ :=
    hk.aestronglyMeasurable.mul (continuous_subtype_val.comp χ.continuous).aestronglyMeasurable
  have hn (χ : PontryaginDual G) (g : G) : ‖K χ g‖ = ‖k g‖ := by simp [K]
  have hτ (g : G) : ‖τ g‖ ≤ weight(g) := by
    simpa only [zero_mul, Real.exp_zero, max_self, one_mul] using
      norm_hardySobolevTranslation_le μ m 0 0 s le_rfl hs g
  have hweight (g : G) : ‖k g‖ * ‖τ g‖ ≤ ‖k g‖ * weight(g) :=
    mul_le_mul_of_nonneg_left (hτ g) (norm_nonneg _)
  have hw : Integrable (fun g ↦ ‖k g‖ * ‖τ g‖) μ := hpoly.mono'
    (hk.aestronglyMeasurable.norm.mul
      (measurable_hardySobolevTranslation_norm μ m 0 0 s le_rfl hs).aestronglyMeasurable)
    (.of_forall fun g ↦
      (Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).le.trans (hweight g))
  have hpoint (χ : PontryaginDual G) (u : W) (g : G) :
      ‖K χ g • τ g u‖ ≤ (‖k g‖ * ‖τ g‖) * ‖u‖ := by
    rw [norm_smul, hn, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((τ g).le_opNorm u) (norm_nonneg _)
  have hI (χ : PontryaginDual G) (u : W) : Integrable (fun g ↦ K χ g • τ g u) μ := by
    have hcont : Continuous (fun g ↦ τ g u) :=
      (exists_hardySobolevTranslation μ m 0 0 s le_rfl hs).choose_spec.2.comp (Continuous.prodMk_left u)
    exact (hw.mul_const ‖u‖).mono' ((hK χ).smul hcont.aestronglyMeasurable) (.of_forall (hpoint χ u))
  let L (χ : PontryaginDual G) : W →ₗ[ℂ] W :=
    { toFun := fun u ↦ ∫ g, K χ g • τ g u ∂μ
      map_add' := fun u v ↦ by
        simp only [map_add, smul_add]
        exact integral_add (hI χ u) (hI χ v)
      map_smul' := fun c u ↦ by simp only [map_smul, smul_comm (K χ _) c, integral_smul, RingHom.id_apply] }
  let B := ∫ g, ‖k g‖ * ‖τ g‖ ∂μ
  have hB (χ : PontryaginDual G) (u : W) : ‖L χ u‖ ≤ B * ‖u‖ :=
    (norm_integral_le_of_norm_le (hw.mul_const ‖u‖) (.of_forall (hpoint χ u))).trans_eq (integral_mul_const _ _)
  let A (χ : PontryaginDual G) := (L χ).mkContinuous B (hB χ)
  refine ⟨A, fun χ u ↦ ⟨hI χ u, rfl⟩, fun χ ↦ (A χ).opNorm_le_bound
    (integral_nonneg fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hB χ),
    integral_mono hw hpoly hweight, ?_, ?_, ?_⟩
  · intro N hclosed hinv χ u hu
    let _ := hclosed
    apply (Submodule.Quotient.mk_eq_zero N).mp
    change N.mkQL (∫ g, K χ g • τ g u ∂μ) = 0
    rw [← N.mkQL.integral_comp_comm (hI χ u)]
    exact integral_eq_zero_of_ae (.of_forall fun g ↦
      (Submodule.Quotient.mk_eq_zero N).mpr (N.smul_mem _ (hinv g u hu)))
  · intro χ f hf
    apply ContinuousLinearMap.ext
    intro u
    have hP := (existsUnique_schwartzBruhat_zeroLineAction μ m s hs).exists.choose_spec f u
    apply (Integrable.hasPettisIntegral (hI χ u)).unique
    simpa only [hf, K] using hP
  · intro χ γ δ he u
    change δ (∫ g, K χ g • τ g u ∂μ) = _
    rw [← δ.integral_comp_comm (hI χ u), lcaFourier, ← integral_mul_const]
    apply integral_congr_ae
    refine .of_forall fun g ↦ ?_
    change δ (K χ g • τ g u) = k g * star ((χ⁻¹ * γ) g : ℂ) * δ u
    rw [map_smul, he, smul_eq_mul]
    change (k g * (χ g : ℂ)) * (star (γ g : ℂ) * δ u) =
      (k g * star (((χ g)⁻¹ * γ g : Circle) : ℂ)) * δ u
    rw [Circle.coe_mul, Circle.coe_inv_eq_conj, ← Complex.star_def, star_mul, star_star]
    ring

/-- If a frequency window of fixed shape is compressed by a factor `ε ≤ 1`, its
inverse Fourier kernel is `ε * k (ε * t)`. Its weighted L¹ cost grows by at most
`ε ^ (-p)`, where the zero-line Young estimate takes `p = s / 2`. -/
theorem radialWindow_dilated_weightedL1 (k : ℝ → ℂ) (hk : Continuous k)
    {p ε : ℝ} (hp : 0 ≤ p) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hint : Integrable (fun t : ℝ ↦ ‖k t‖ * (1 + |t|) ^ p)) :
    let kε (t : ℝ) := (ε : ℂ) * k (ε * t)
    Integrable (fun t : ℝ ↦ ‖kε t‖ * (1 + |t|) ^ p) ∧
      (∫ t : ℝ, ‖kε t‖ * (1 + |t|) ^ p) ≤
        ε ^ (-p) * ∫ t : ℝ, ‖k t‖ * (1 + |t|) ^ p := by
  intro kε
  let f (t : ℝ) := ‖k t‖ * (1 + |t|) ^ p
  have hweight (t : ℝ) : (1 + |t|) ^ p ≤ ε ^ (-p) * (1 + |ε * t|) ^ p := by
    calc
      _ ≤ ((1 + |ε * t|) / ε) ^ p := by
        apply Real.rpow_le_rpow (by positivity) _ hp
        rw [le_div_iff₀ hε, abs_mul, abs_of_pos hε]
        linarith
      _ = _ := by rw [Real.div_rpow (by positivity) hε.le, Real.rpow_neg hε.le, div_eq_inv_mul]
  have hpoint (t : ℝ) : ‖kε t‖ * (1 + |t|) ^ p ≤ (ε ^ (-p) * ε) * f (ε * t) := by
    simp only [kε, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
    refine (mul_le_mul_of_nonneg_left (hweight t) (mul_nonneg hε.le (norm_nonneg _))).trans_eq ?_
    dsimp [f]
    ring
  have hmajor : Integrable (fun t : ℝ ↦ (ε ^ (-p) * ε) * f (ε * t)) :=
    ((integrable_comp_mul_left_iff f hε.ne').mpr hint).const_mul _
  have hm : Continuous (fun t : ℝ ↦ ‖kε t‖ * (1 + |t|) ^ p) :=
    ((continuous_const.mul (hk.comp (continuous_const.mul continuous_id))).norm).mul
      ((continuous_const.add continuous_abs).rpow_const
        (fun t : ℝ ↦ Or.inl (ne_of_gt (by positivity : 0 < 1 + |t|))))
  have hi := hmajor.mono' hm.aestronglyMeasurable (.of_forall fun t ↦
    (Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))).le.trans
      (hpoint t))
  refine ⟨hi, (integral_mono hi hmajor hpoint).trans_eq ?_⟩
  rw [integral_const_mul, Measure.integral_comp_mul_left, smul_eq_mul, abs_inv, abs_of_pos hε]
  change ε ^ (-p) * ε * (ε⁻¹ * ∫ t, f t) = ε ^ (-p) * ∫ t, f t
  rw [mul_assoc, ← mul_assoc ε, mul_inv_cancel₀ hε.ne', one_mul]

end RiemannMasullo.Isolated


namespace RiemannMasullo.Isolated

open NumberField
open scoped BigOperators NumberField.AdeleRing Topology

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

section LineBlocks

variable {F : Type*} [Field F] [NumberField F]
variable {a s : ℝ}

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => logIdeleClassNorm F
local notation "h₀" => le_rfl (a := (0 : ℝ))
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 logNorm 0 0 s
local notation "Θ(" a ", " hs ")" => globalThetaSobolev F a h₀ hs₀(hs)
local notation "Q(" a ", " hs ")" => spectralSobolevQuotient F a h₀ hs₀(hs)
local notation "τ(" s ", " hs ")" => hardySobolevTranslation μ𝔽 m𝔽 0 0 s h₀ hs₀(hs)
local notation "J(" χ ")" => SpectralLineJetIndex (F := F) χ a s
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ // 0 < order(χ z.1, shift(a, z.2))}
local notation "N(" χ ", " z ")" => spectralBoundaryMultiplicity s (order(χ (z).val.1, shift(a, (z).val.2))).untop₀.toNat
local notation "jet(" z ", " m ")" => ⟨((z).val.1, (z).val.2, (m).val), (m).isLt⟩
local notation "raw(" χ ", " j ")" => spectralZeroJet (F := F) (χ (j).val.1) 0 (j).val.2.1 (j).val.2.2
local notation "poly(" k ", " s ")" => (fun g : C𝔽 ↦ ‖(k : C𝔽 → ℂ) g‖ * (1 + |logNorm g|) ^ (s / 2))

private theorem lineWindow_log_continuous : Continuous (logIdeleClassNorm F) :=
  (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).log
    (fun g ↦ NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)

private theorem lineWindow_phase (η : PontryaginDual C𝔽) (t : ℝ) (q : ℕ) (g : C𝔽) :
    spectralZeroJet η 0 t q g =
      ((η g : ℂ) * Complex.exp (((t * logNorm g : ℝ) : ℂ) * Complex.I)) * (logNorm g : ℂ)^q := by
  have hp : (0 : ℝ) < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change ((η g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ ((0 : ℂ) + (t : ℂ) * Complex.I)) * _ = _
  rw [zero_add, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, Complex.ofReal_mul]
  ring_nf

private theorem lineWindow_dot_moment_integrable (k : C𝔽 → ℂ) (hk : AEMeasurable k μ𝔽)
    (hpoly : Integrable poly(k,s) μ𝔽) (η : PontryaginDual C𝔽) (q : ℕ) (hq : (q : ℝ) ≤ s / 2) :
    Integrable (fun g ↦ (k g * (η g : ℂ)) * (logNorm g : ℂ)^q) μ𝔽 := by
  refine hpoly.mono' ((hk.aestronglyMeasurable.mul (continuous_subtype_val.comp
    η.continuous).aestronglyMeasurable).mul ((Complex.continuous_ofReal.comp
    (lineWindow_log_continuous (F := F))).pow q).aestronglyMeasurable) (.of_forall fun g ↦ ?_)
  simp only [norm_mul, Circle.norm_coe, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    |logNorm g| ^ q ≤ (1 + |logNorm g|) ^ q := by gcongr; linarith
    _ = (1 + |logNorm g|) ^ (q : ℝ) := (Real.rpow_natCast ..).symm
    _ ≤ (1 + |logNorm g|) ^ (s / 2) := Real.rpow_le_rpow_of_exponent_le (by simp) hq

private theorem lineWindow_moment_integrable (k : C𝔽 → ℂ) (hk : AEMeasurable k μ𝔽)
    (hpoly : Integrable poly(k,s) μ𝔽) (η : PontryaginDual C𝔽) (t : ℝ) (q : ℕ) (hq : (q : ℝ) ≤ s / 2) :
    Integrable (fun g ↦ k g * spectralZeroJet η 0 t q g) μ𝔽 := by
  have h := lineWindow_dot_moment_integrable k hk hpoly η q hq
  have hphase : Continuous (fun g : C𝔽 ↦ Complex.exp (((t * logNorm g : ℝ) : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul
      (lineWindow_log_continuous (F := F)))).mul continuous_const)
  simp_rw [lineWindow_phase]
  refine h.norm.mono' ((hk.aestronglyMeasurable.mul
    (((continuous_subtype_val.comp η.continuous).mul hphase).mul ((Complex.continuous_ofReal.comp
      (lineWindow_log_continuous (F := F))).pow q)).aestronglyMeasurable)) (.of_forall fun g ↦ ?_)
  change ‖k g * (((η g : ℂ) * Complex.exp (((t * logNorm g : ℝ) : ℂ) * Complex.I)) * (logNorm g : ℂ)^q)‖ ≤
    ‖(k g * (η g : ℂ)) * (logNorm g : ℂ)^q‖
  simp only [norm_mul, Circle.norm_coe, Complex.norm_exp_ofReal_mul_I, one_mul, mul_one, le_rfl]

private theorem lineWindow_eval (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hs : 1 < s)
    (j : J(χ)) (L : StrongDual ℂ Q(a,hs))
    (hL : spectralSobolevDualEmbedding F a h₀ hs₀(hs) L = (spectralLineJet_memLp χ hs j).toLp (raw(χ,j)))
    (v : W(s)) :
    Integrable (fun y ↦ v y * raw(χ,j) y) μ𝔽 ∧
    L ((Θ(a,hs)).mkQL v) = ∫ y, v y * raw(χ,j) y ∂μ𝔽 := by
  let w (g : C𝔽) := intervalSobolevDensity 0 0 s (logNorm g)
  have hw : Measurable w := by
    have hD : Continuous (intervalSobolevDensity 0 0 s) := by unfold intervalSobolevDensity; fun_prop
    exact hD.measurable.comp (lineWindow_log_continuous (F := F)).measurable
  have hbase : μ𝔽 ≪ (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g)⁻¹) := by
    refine withDensity_absolutelyContinuous' hw.inv.ennreal_ofReal.aemeasurable (.of_forall fun g ↦ ?_)
    refine ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ?_)
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  let D := spectralSobolevDualEmbedding F a h₀ hs₀(hs)
  have hae : (D L : C𝔽 → ℂ) =ᵐ[μ𝔽] raw(χ,j) := by
    change (spectralSobolevDualEmbedding F a h₀ hs₀(hs) L : C𝔽 → ℂ) =ᵐ[μ𝔽] _
    rw [hL]
    exact hbase.ae_le (MemLp.coeFn_toLp _)
  have he := spectralSobolevPairing_dual h₀ hs₀(hs) (L.comp (Θ(a,hs)).mkQL) v
  change Integrable (fun y ↦ v y * D L y) μ𝔽 ∧ L ((Θ(a,hs)).mkQL v) = ∫ y, v y * D L y ∂μ𝔽 at he
  have heq := hae.mono fun y hy ↦ congrArg (v y * ·) hy
  exact ⟨he.1.congr heq, he.2.trans (integral_congr_ae heq)⟩

/-- The actual line translation acts on all admitted log jets by the binomial formula. -/
private theorem lineWindow_translate (hs : 1 < s) (η : PontryaginDual C𝔽) (t : ℝ) (m : ℕ) (v : W(s))
    (hint : ∀ i ≤ m, Integrable (fun x ↦ v x * spectralZeroJet (F := F) η 0 t i x) μ𝔽) (g : C𝔽) :
    (∫ y, τ(s,hs) g v y * spectralZeroJet η 0 t m y ∂μ𝔽) =
      ∑ i : Fin (m + 1), ((m.choose i.val : ℂ) * spectralZeroJet η 0 t (m - i.val) g) *
        ∫ y, v y * spectralZeroJet η 0 t i.val y ∂μ𝔽 := by
  let T := ideleClassNormTwist (F := F) η (shift(0, t))
  let L (y : C𝔽) : ℂ := logNorm y
  let c (i : ℕ) := (m.choose i : ℂ) * spectralZeroJet η 0 t (m - i) g
  have hlog (y : C𝔽) : L (g * y) = L y + L g := by
    dsimp only [L, logIdeleClassNorm]
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
      (NNReal.coe_ne_zero.2 (ideleClassNorm F y).ne_zero), Complex.ofReal_add, add_comm]
  have hsum (y : C𝔽) : v y * spectralZeroJet η 0 t m (g * y) =
      ∑ i ∈ Finset.range (m + 1), c i * (v y * spectralZeroJet η 0 t i y) := by
    change v y * (T (g * y) * L (g * y) ^ m) = _
    rw [map_mul, hlog, add_pow]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change v y * (T g * T y * (L y ^ i * L g ^ (m - i) * (m.choose i : ℂ))) =
      ((m.choose i : ℂ) * (T g * L g ^ (m - i))) * (v y * (T y * L y ^ i))
    ring
  let J := spectralZeroJet η 0 t m
  let H (y : C𝔽) := v (g⁻¹ * y) * J y
  calc
    _ = ∫ y, H y ∂μ𝔽 := integral_congr_ae
      ((hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s h₀ hs₀(hs) g v).mono fun y hy ↦ congrArg (· * J y) hy)
    _ = ∫ y, H (g * y) ∂μ𝔽 := (integral_mul_left_eq_self H g).symm
    _ = ∫ y, v y * J (g * y) ∂μ𝔽 := by simp only [H, inv_mul_cancel_left]
    _ = _ := by
      simp_rw [show ∀ y, v y * J (g * y) = _ from hsum]
      rw [integral_finsetSum _ fun i hi ↦ (hint i (Finset.mem_range_succ_iff.mp hi)).const_mul (c i)]
      simp_rw [integral_const_mul]
      exact (Fin.sum_univ_eq_sum_range (fun i ↦ c i * ∫ y, v y * spectralZeroJet η 0 t i y ∂μ𝔽) _).symm

/-- The project's Fourier–Mellin multiplier restricted to the real frequency chart. -/
def spectralLineWindowMultiplier (k : C𝔽 → ℂ) (η : PontryaginDual C𝔽) (t : ℝ) : ℂ :=
  modulatedFourierMellin m𝔽 univ
    (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
    μ𝔽 k (ideleClassNormTwist η (shift(0,t)))

private theorem lineWindow_multiplier_eq_phase (k : C𝔽 → ℂ) (η : PontryaginDual C𝔽) (t : ℝ) :
    spectralLineWindowMultiplier k η t = ∫ g, (k g * (η g : ℂ)) *
      Complex.exp (((t * logNorm g : ℝ) : ℂ) * Complex.I) ∂μ𝔽 := by
  have h : spectralLineWindowMultiplier k η t = ∫ g, k g * ideleClassNormTwist η (shift(0,t)) g ∂μ𝔽 := by
    simp only [spectralLineWindowMultiplier, modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  refine h.trans (integral_congr_ae (.of_forall fun g ↦ ?_))
  have hphase := lineWindow_phase η t 0 g
  simp only [spectralZeroJet, pow_zero, mul_one] at hphase
  exact (congrArg (k g * ·) hphase).trans (mul_assoc _ _ _).symm

/-- Differentiation in the real frequency variable requires absolute log moments only
through the requested order. This is the dominated-integral argument in §10.2. -/
private theorem lineWindow_deriv_oscillatory {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (L : X → ℝ) (hL : Measurable L) (f : X → ℂ) (k : ℕ)
    (hi : ∀ j ≤ k, Integrable (fun x ↦ f x * (L x : ℂ) ^ j) μ) (t : ℝ) :
    iteratedDeriv k (fun u : ℝ ↦ ∫ x, f x * Complex.exp (((u * L x : ℝ) : ℂ) * Complex.I) ∂μ) t =
      Complex.I ^ k * ∫ x, f x * (L x : ℂ) ^ k * Complex.exp (((t * L x : ℝ) : ℂ) * Complex.I) ∂μ := by
  let A (j : ℕ) (u : ℝ) (x : X) :=
    (f x * (L x : ℂ) ^ j) * Complex.I ^ j * Complex.exp (((u * L x : ℝ) : ℂ) * Complex.I)
  have hnorm (j u x) : ‖A j u x‖ = ‖f x * (L x : ℂ) ^ j‖ := by
    simp only [A, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one,
      Complex.norm_exp_ofReal_mul_I]
  have hmeas (j) (hj : j ≤ k) (u : ℝ) : AEStronglyMeasurable (A j u) μ := by
    refine ((hi j hj).aestronglyMeasurable.mul_const _).mul ?_
    exact (Complex.continuous_exp.measurable.comp
      ((Complex.continuous_ofReal.measurable.comp (hL.const_mul u)).mul_const _)).aestronglyMeasurable
  have hint (j) (hj : j ≤ k) (u : ℝ) : Integrable (A j u) μ :=
    (hi j hj).norm.mono' (hmeas j hj u) (.of_forall fun x ↦ (hnorm j u x).le)
  have hder (j) (hj : j+1 ≤ k) (u : ℝ) :
      HasDerivAt (fun v ↦ ∫ x, A j v x ∂μ) (∫ x, A (j+1) u x ∂μ) u := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) univ_mem
      (.of_forall (hmeas j (by omega))) (hint j (by omega) u) (hmeas _ hj u)
      (.of_forall fun x v _ ↦ (hnorm (j+1) v x).le) (hi _ hj).norm ?_).2
    refine .of_forall fun x v _ ↦ ?_
    have hd := (((hasDerivAt_id v).mul_const (L x)).ofReal_comp.mul_const Complex.I).cexp
    convert hd.const_mul ((f x * (L x : ℂ)^j) * Complex.I^j) using 1
    · simp [A]
    · simp [A, pow_succ]
      ring
  have hall (j) (hj : j ≤ k) :
      iteratedDeriv j (fun u : ℝ ↦ ∫ x, f x * Complex.exp (((u * L x : ℝ) : ℂ) * Complex.I) ∂μ) =
        fun u ↦ ∫ x, A j u x ∂μ := by
    induction j with
    | zero => simp [A]
    | succ j ih =>
      rw [iteratedDeriv_succ, ih (by omega)]
      exact funext fun u ↦ (hder j hj u).deriv
  rw [hall k le_rfl, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun x ↦ by dsimp [A]; ring)

/-- Frequency derivatives are the raw log moments of the possibly noncompact kernel. -/
theorem spectralLineWindowMultiplier_iteratedDeriv (k : C𝔽 → ℂ) (hk : AEMeasurable k μ𝔽)
    (hpoly : Integrable poly(k,s) μ𝔽) (η : PontryaginDual C𝔽) (t : ℝ) (q : ℕ) (hq : (q : ℝ) ≤ s / 2) :
    iteratedDeriv q (spectralLineWindowMultiplier k η) t =
      Complex.I ^ q * ∫ g, k g * spectralZeroJet η 0 t q g ∂μ𝔽 := by
  rw [show spectralLineWindowMultiplier k η = _ from funext (lineWindow_multiplier_eq_phase k η)]
  rw [lineWindow_deriv_oscillatory μ𝔽 logNorm (lineWindow_log_continuous (F := F)).measurable
    (fun g ↦ k g * (η g : ℂ)) q (fun j hj ↦
      lineWindow_dot_moment_integrable k hk hpoly η j ((Nat.cast_le.mpr hj).trans hq)) t]
  congr 1
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  rw [lineWindow_phase]
  ring

/-- Every jet of a vectorwise integrated action is the full triangular sum over
the lower jets. The polynomial Young hypothesis supplies all the required moments. -/
theorem spectralLineWindow_all_jet_coefficients
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hs : 1 < s)
    (Λ : J(χ) → StrongDual ℂ Q(a,hs))
    (hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp χ hs j).toLp (raw(χ,j)))
    (k : C𝔽 → ℂ) (hk : AEMeasurable k μ𝔽) (hpoly : Integrable poly(k,s) μ𝔽)
    (A : W(s) →L[ℂ] W(s))
    (hA : ∀ (δ : StrongDual ℂ W(s)) v, δ (A v) = ∫ g, k g * δ (τ(s,hs) g v) ∂μ𝔽)
    (z : Z(χ)) (m : Fin (N(χ,z))) (v : W(s)) :
    Λ (jet(z,m)) ((Θ(a,hs)).mkQ (A v)) =
      ∑ i : Fin (m.val + 1), ((m.val.choose i.val : ℂ) *
        (∫ g, k g * spectralZeroJet (χ z.val.1) 0 z.val.2 (m.val - i.val) g ∂μ𝔽)) *
        Λ (jet(z,(⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ : Fin (N(χ,z))))) ((Θ(a,hs)).mkQ v) := by
  let idx (i : Fin (m.val + 1)) : Fin (N(χ,z)) := ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩
  let J (q : ℕ) := spectralZeroJet (χ z.val.1) 0 z.val.2 q
  let y (i : Fin (m.val + 1)) := Λ (jet(z,idx i)) ((Θ(a,hs)).mkQ v)
  let δ := (Λ (jet(z,m))).comp (Θ(a,hs)).mkQL
  have heval (j : J(χ)) (w : W(s)) := lineWindow_eval χ hs j (Λ j) (hj j) w
  have hm : (m.val : ℝ) < (s - 1) / 2 := ((lt_spectralBoundaryMultiplicity s _ _).mp m.isLt).2
  have hint (i : ℕ) (hi : i ≤ m.val) : Integrable (fun x ↦ v x * J i x) μ𝔽 := by
    let l : Fin (N(χ,z)) := ⟨i, hi.trans_lt m.isLt⟩
    exact (heval (jet(z,l)) v).1
  have hi (i : Fin (m.val + 1)) : (∫ x, v x * J i.val x ∂μ𝔽) = y i := (heval (jet(z,idx i)) v).2.symm
  have ht (g : C𝔽) : δ (τ(s,hs) g v) = ∑ i : Fin (m.val + 1),
      ((m.val.choose i.val : ℂ) * J (m.val - i.val) g) * y i := by
    refine (heval (jet(z,m)) (τ(s,hs) g v)).2.trans
      ((lineWindow_translate hs (χ z.val.1) z.val.2 m.val v hint g).trans ?_)
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (fun b ↦ ((m.val.choose i.val : ℂ) * J (m.val - i.val) g) * b) (hi i)
  have hki (i : Fin (m.val + 1)) : Integrable (fun g ↦ ((m.val.choose i.val : ℂ) *
      (k g * J (m.val - i.val) g)) * y i) μ𝔽 := by
    have hq : ((m.val - i.val : ℕ) : ℝ) ≤ m.val := by exact_mod_cast Nat.sub_le m.val i.val
    exact ((lineWindow_moment_integrable k hk hpoly (χ z.val.1) z.val.2 _ (by linarith)).const_mul _).mul_const _
  calc
    _ = ∫ g, k g * δ (τ(s,hs) g v) ∂μ𝔽 := hA δ v
    _ = ∫ g, ∑ i : Fin (m.val + 1), ((m.val.choose i.val : ℂ) * (k g * J (m.val - i.val) g)) * y i ∂μ𝔽 := by
      refine integral_congr_ae (.of_forall fun g ↦ ?_)
      refine ((congrArg (k g * ·) (ht g)).trans (Finset.mul_sum ..)).trans ?_
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ ↦ hki i)]
      simp_rw [integral_mul_const, integral_const_mul]
      rfl

private theorem lineWindow_operator (hs : 1 < s) (k : C𝔽 → ℂ) (hk : AEMeasurable k μ𝔽)
    (hpoly : Integrable poly(k,s) μ𝔽) :
    ∃ B : W(s) →L[ℂ] W(s),
      (∀ v : W(s), Integrable (fun g ↦ k g • τ(s,hs) g v) μ𝔽 ∧
        B v = ∫ g, k g • τ(s,hs) g v ∂μ𝔽) ∧
      (∀ (δ : StrongDual ℂ W(s)) v, δ (B v) = ∫ g, k g * δ (τ(s,hs) g v) ∂μ𝔽) ∧
      ‖B‖ ≤ ∫ g, poly(k,s) g ∂μ𝔽 := by
  obtain ⟨P,hP,hPN,hW,-⟩ := spectralLine_exists_modulated_window_operators μ𝔽 m𝔽 s hs₀(hs) k hk hpoly
  have hB (v : W(s)) : Integrable (fun g ↦ k g • τ(s,hs) g v) μ𝔽 ∧ P 1 v = ∫ g, k g • τ(s,hs) g v ∂μ𝔽 := by
    simpa only [map_one, PontryaginDual.one_apply, Circle.coe_one, mul_one] using hP 1 v
  refine ⟨P 1, hB, ?_, (hPN 1).trans hW⟩
  intro δ v
  rw [(hB v).2, ← δ.integral_comp_comm (hB v).1]
  exact integral_congr_ae (.of_forall fun g ↦ map_smul δ _ _)

/-- Evaluation of the actual Bochner convolution at every retained logarithmic jet. -/
theorem spectralLineWindow_integral_jet_coefficients
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hs : 1 < s)
    (Λ : J(χ) → StrongDual ℂ Q(a,hs))
    (hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp χ hs j).toLp (raw(χ,j)))
    (k : C𝔽 → ℂ) (hk : AEMeasurable k μ𝔽) (hpoly : Integrable poly(k,s) μ𝔽)
    (z : Z(χ)) (m : Fin (N(χ,z))) (v : W(s)) :
    Λ (jet(z,m)) ((Θ(a,hs)).mkQ (∫ g, k g • τ(s,hs) g v ∂μ𝔽)) =
      ∑ i : Fin (m.val + 1), ((m.val.choose i.val : ℂ) *
        (∫ g, k g * spectralZeroJet (χ z.val.1) 0 z.val.2 (m.val - i.val) g ∂μ𝔽)) *
        Λ (jet(z,(⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ : Fin (N(χ,z))))) ((Θ(a,hs)).mkQ v) := by
  obtain ⟨B,hB,hBC,-⟩ := lineWindow_operator hs k hk hpoly
  exact (congrArg (fun w : W(s) ↦ Λ (jet(z,m)) ((Θ(a,hs)).mkQ w)) (hB v).2.symm).trans
    (spectralLineWindow_all_jet_coefficients χ hs Λ hj k hk hpoly B hBC z m v)

/-- A full set of zero-block coordinates determines the finite convolution sum. -/
private theorem lineWindow_finite_synthesis {I Z E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] E) (x : I → E) (Λ : I → StrongDual ℂ E) (hb : IsSpectralMarkushevichBasis x Λ)
    (K : Finset Z) (N : Z → ℕ) (e : ((z : Z) × Fin (N z)) ≃ I) (u w : E)
    (hon : ∀ z ∈ K, ∀ m : Fin (N z), Λ (e ⟨z,m⟩) w = Λ (e ⟨z,m⟩) (A u))
    (hoff : ∀ z ∉ K, ∀ m : Fin (N z), Λ (e ⟨z,m⟩) w = 0) :
    spectralConvolutionFiniteSum A x Λ K N (fun z m ↦ e ⟨z,m⟩) u = w := by
  classical
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  have he : ContinuousLinearMap.apply ℂ ℂ (spectralConvolutionFiniteSum A x Λ K N (fun z m ↦ e ⟨z,m⟩) u) =
      ContinuousLinearMap.apply ℂ ℂ w := by
    apply ContinuousLinearMap.ext_on hb.2.2.2
    rintro _ ⟨j,rfl⟩
    obtain ⟨⟨z,m⟩,rfl⟩ := e.surjective j
    change Λ (e ⟨z,m⟩) (spectralConvolutionFiniteSum A x Λ K N (fun p q ↦ e ⟨p,q⟩) u) = _
    simp only [spectralConvolutionFiniteSum, sum_apply, map_sum, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul, ContinuousLinearMap.apply_apply]
    have hother (p : Z) (hp : p ≠ z) (q : Fin (N p)) : Λ (e ⟨z,m⟩) (x (e ⟨p,q⟩)) = 0 :=
      hb.2.1 _ _ (fun h ↦ hp (congrArg Sigma.fst (e.injective h)))
    by_cases hz : z ∈ K
    · rw [Finset.sum_eq_single_of_mem z hz]
      · rw [Finset.sum_eq_single m]
        · rw [hb.1, mul_one]
          exact (hon z hz m).symm
        · intro q _ hq
          rw [hb.2.1 _ _ (fun h ↦ hq (eq_of_heq (Sigma.mk.inj_iff.mp (e.injective h)).2)), mul_zero]
        · simp
      · intro p _ hp
        exact Finset.sum_eq_zero fun q _ ↦ by rw [hother p hp q, mul_zero]
    · rw [hoff z hz m]
      exact Finset.sum_eq_zero fun p hp ↦ Finset.sum_eq_zero fun q _ ↦ by
        rw [hother p (fun h ↦ hz (h ▸ hp)) q, mul_zero]
  exact fun δ ↦ DFunLike.congr_fun he δ

private theorem lineWindow_test_weight (s : ℝ) (φ : BruhatCompactSupport C𝔽) :
    AEMeasurable φ.val μ𝔽 ∧ Integrable poly(φ.val,s) μ𝔽 := by
  have hφ := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hw : Continuous (fun g : C𝔽 ↦ (1 + |logNorm g|) ^ (s / 2)) :=
    (continuous_const.add (lineWindow_log_continuous (F := F)).abs).rpow_const
      (fun g : C𝔽 ↦ Or.inl (ne_of_gt (by positivity : 0 < 1 + |logNorm g|)))
  exact ⟨hφ.aemeasurable, (hφ.norm.mul hw).integrable_of_hasCompactSupport
    ((show HasCompactSupport φ.val from φ.property.2).norm.mul_right)⟩

private theorem lineWindow_test_scalar (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (δ : StrongDual ℂ W(s)) (v : W(s)) :
    δ (hardySobolevTestAction μ𝔽 m𝔽 0 0 s h₀ hs₀(hs) φ v) = ∫ g, φ.val g * δ (τ(s,hs) g v) ∂μ𝔽 := by
  have hP := bruhatRegularizedAction_apply μ𝔽 τ(s,hs)
    (exists_hardySobolevTranslation μ𝔽 m𝔽 0 0 s h₀ hs₀(hs)).choose_spec.2 φ v
  have he := congrArg (fun p : PettisWeakCompletion W(s) ↦
    (show Module.Dual ℂ (StrongDual ℂ W(s)) from p) δ) hP.2
  exact he.trans (integral_congr_ae (.of_forall fun g ↦ map_smul δ _ _))

/-- Paper: Theorem 10.3.1.1(1), pp. 448–451. A possibly noncompact window whose
Fourier–Mellin derivatives agree with a test
on a finite set of line zeros and vanish elsewhere descends to that exact finite
convolution sum. Its operator norm on the actual quotient obeys weighted Young
with constant one, uniformly over the finite set and its jet multiplicities.
Reconstruction: matching the complete jets gives a frequency-window criterion for the
manuscript's finite sections in (10.3.1.1). -/
theorem spectralLineWindow_finiteSum_of_matching_derivatives
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hs : 1 < s)
    (x : J(χ) → Q(a,hs)) (Λ : J(χ) → StrongDual ℂ Q(a,hs)) (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp χ hs j).toLp (raw(χ,j)))
    (φ : BruhatCompactSupport C𝔽) (K : Finset (Z(χ))) (k : C𝔽 → ℂ)
    (hk : AEMeasurable k μ𝔽) (hpoly : Integrable poly(k,s) μ𝔽)
    (hon : ∀ z ∈ K, ∀ q : Fin (N(χ,z)), iteratedDeriv q.val (spectralLineWindowMultiplier k (χ z.val.1)) z.val.2 =
      iteratedDeriv q.val (spectralLineWindowMultiplier φ.val (χ z.val.1)) z.val.2)
    (hoff : ∀ z ∉ K, ∀ q : Fin (N(χ,z)), iteratedDeriv q.val (spectralLineWindowMultiplier k (χ z.val.1)) z.val.2 = 0) :
    let S := spectralConvolutionFiniteSum (spectralConvolution (F := F) a h₀ hs₀(hs) φ) x Λ K
      (fun z ↦ N(χ,z)) (fun z m ↦ jet(z,m))
    (∀ v : W(s), S ((Θ(a,hs)).mkQ v) = (Θ(a,hs)).mkQ (∫ g, k g • τ(s,hs) g v ∂μ𝔽)) ∧
      ‖S‖ ≤ ∫ g, poly(k,s) g ∂μ𝔽 := by
  intro S
  classical
  let θ : Submodule ℂ W(s) := Θ(a,hs)
  let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
  let Pφ : W(s) →L[ℂ] W(s) := hardySobolevTestAction μ𝔽 m𝔽 0 0 s h₀ hs₀(hs) φ
  obtain ⟨B,hB,hBC,hn⟩ := lineWindow_operator hs k hk hpoly
  have hφ := lineWindow_test_weight s φ
  let Fφ (z : Z(χ)) (q : ℕ) := ∫ g, φ.val g * spectralZeroJet (χ z.val.1) 0 z.val.2 q g ∂μ𝔽
  let Fk (z : Z(χ)) (q : ℕ) := ∫ g, k g * spectralZeroJet (χ z.val.1) 0 z.val.2 q g ∂μ𝔽
  have hq (z : Z(χ)) (q : Fin (N(χ,z))) : (q.val : ℝ) ≤ s / 2 := by
    have := ((lt_spectralBoundaryMultiplicity s _ _).mp q.isLt).2
    linarith
  have hmoment_on (z : Z(χ)) (hz : z ∈ K) (q : Fin (N(χ,z))) : Fk z q.val = Fφ z q.val := by
    apply mul_left_cancel₀ (pow_ne_zero q.val Complex.I_ne_zero)
    exact (spectralLineWindowMultiplier_iteratedDeriv k hk hpoly _ _ q.val (hq z q)).symm.trans
      ((hon z hz q).trans (spectralLineWindowMultiplier_iteratedDeriv φ.val hφ.1 hφ.2 _ _ q.val (hq z q)))
  have hmoment_off (z : Z(χ)) (hz : z ∉ K) (q : Fin (N(χ,z))) : Fk z q.val = 0 := by
    apply (mul_eq_zero.mp ((spectralLineWindowMultiplier_iteratedDeriv k hk hpoly _ _ q.val (hq z q)).symm.trans
      (hoff z hz q))).resolve_left (pow_ne_zero _ Complex.I_ne_zero)
  let e : ((z : Z(χ)) × Fin (N(χ,z))) ≃ J(χ) :=
    { toFun := fun p ↦ jet(p.1,p.2)
      invFun := fun j ↦ ⟨⟨(j.val.1,j.val.2.1), SpectralLineJetIndex.order_pos j⟩, ⟨j.val.2.2,j.property⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have heq (v : W(s)) : S (θ.mkQ v) = θ.mkQ (B v) := by
    apply lineWindow_finite_synthesis A x Λ hb K (fun z ↦ N(χ,z)) e (θ.mkQ v) (θ.mkQ (B v))
    · intro z hz m
      change Λ (jet(z,m)) (θ.mkQ (B v)) = Λ (jet(z,m)) (A (θ.mkQ v))
      have ha := spectralConvolution_mkQ (F := F) a h₀ hs₀(hs) φ v
      change A (θ.mkQ v) = θ.mkQ (Pφ v) at ha
      rw [ha]
      refine (spectralLineWindow_all_jet_coefficients χ hs Λ hj k hk hpoly B hBC z m v).trans ?_
      refine Eq.trans ?_ (spectralLineWindow_all_jet_coefficients χ hs Λ hj φ.val hφ.1 hφ.2 Pφ
        (lineWindow_test_scalar hs φ) z m v).symm
      apply Finset.sum_congr rfl
      intro i _
      let q : Fin (N(χ,z)) := ⟨m.val - i.val, (Nat.sub_le ..).trans_lt m.isLt⟩
      exact congrArg (fun c : ℂ ↦ ((m.val.choose i.val : ℂ) * c) * _) (hmoment_on z hz q)
    · intro z hz m
      refine (spectralLineWindow_all_jet_coefficients χ hs Λ hj k hk hpoly B hBC z m v).trans ?_
      apply Finset.sum_eq_zero
      intro i _
      let q : Fin (N(χ,z)) := ⟨m.val - i.val, (Nat.sub_le ..).trans_lt m.isLt⟩
      change ((m.val.choose i.val : ℂ) * Fk z q.val) * _ = 0
      rw [hmoment_off z hz q, mul_zero, zero_mul]
  refine ⟨fun v ↦ (heq v).trans (congrArg θ.mkQ (hB v).2), ?_⟩
  apply S.opNorm_le_bound ((norm_nonneg B).trans hn)
  intro u
  let v := θ.quotientEquivOrthogonal u
  have hv : θ.mkQ v.val = u := (θ.quotientEquivOrthogonal_symm_eq_mk v.val v.property).symm.trans
    (θ.quotientEquivOrthogonal.symm_apply_apply u)
  have hnorm : ‖v.val‖ = ‖u‖ := θ.quotientEquivOrthogonal.norm_map u
  calc
    ‖S u‖ = ‖θ.mkQ (B v.val)‖ := congrArg norm ((congrArg S hv.symm).trans (heq v.val))
    _ ≤ ‖B v.val‖ := Submodule.Quotient.norm_mk_le θ _
    _ ≤ ‖B‖ * ‖v.val‖ := B.le_opNorm _
    _ ≤ (∫ g, poly(k,s) g ∂μ𝔽) * ‖u‖ := by rw [hnorm]; exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)

end LineBlocks

end RiemannMasullo.Isolated
