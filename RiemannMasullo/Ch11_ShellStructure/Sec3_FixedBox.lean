module

public import RiemannMasullo.Ch11_ShellStructure.Sec3
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # Fixed Fourier boxes in the divisorial filtration

Masullo, (11.3.1.3)–(11.3.1.4), pp. 494–496. Take the intersection with a
fixed Fourier box before closing the smooth denominator in the half-twisted
strip norm. A uniform lower bound on the support distinguishes this construction
from taking the closure of the entire next stage.

`primaryDivisorialAbsolutePW_quotient_bounds` compares the single-packet and
successive-stage quotient seminorms. `primaryDivisorialAbsolutePW_stage_noncollapse`
gives one strictly positive class for each stage in all sufficiently large finite
boxes. `primaryDivisorialAbsolutePW_recoveredOrbitalJet_le` controls the undepleted
orbital integrals by the depleted strip norm.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F

/-- Paper: (11.3.1.3), p. 494, and Proposition 7.3.2.2(2), p. 352.
Before depletion, all polar representatives at the same absolute Fourier level
have homogeneous theta supported above one positive idelic norm. -/
theorem primaryDivisorialAbsolutePW_support (S : Finset V)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) {X : ℝ} (hX : 0 < X) :
    ∃ B > (0 : ℝ), ∀ f ∈ primaryDivisorialAbsolutePWTests (F := F) S X,
      tsupport (homogeneousAdelicTheta ω f.val) ⊆
        {g | B⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} := by
  classical
  obtain ⟨B, hB, hsupp⟩ := sLocalAbsolutePW_globalSupport (F := F) (S := S) (T := S)
    le_rfl (Finset.union_empty S).symm (Finset.disjoint_empty_right S)
    isSaturatedPlaceSet_empty hPic ω hω X hX
  refine ⟨B, hB, fun f hf ↦ ?_⟩
  obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hf)
  change sAdeleSchwartzToGlobal F S g = f.val at hgf
  have hp : sAdeleSchwartzToGlobal F S g ∈ adelePolarSubspace F := by
    rw [hgf]
    exact f.property
  have hg₀ := (mem_sAdelePolarSubspace g).mpr
    ((sAdeleSchwartzToGlobal_mem_polarSubspace_iff S g).mp hp)
  rw [← hgf]
  exact hsupp g ⟨hg, hg₀⟩

/-! ### Orbital jet estimates -/

section

open scoped Classical

local notation "L" => logIdeleClassNorm F
local notation "m𝔽" => continuousIdeleClassNorm F

private theorem fixedBoxRow_radial (B : ℝ) (k : ℕ) :
    Integrable ((Ici B).indicator fun x : ℝ ↦ Real.exp (-x) * x ^ (2*k)) := by
  apply (integrable_indicator_iff measurableSet_Ici).2
  have hp : IntegrableOn (fun x : ℝ ↦ Real.exp (-x) * x ^ (2*k)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_rpow (s := ((2*k : ℕ) : ℝ)) (p := 1)
      (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _)) one_pos
    simpa only [Real.rpow_one, Real.rpow_natCast, mul_comm] using h
  have hc : Continuous (fun x : ℝ ↦ Real.exp (-x) * x ^ (2*k)) := by fun_prop
  apply ((hc.integrableOn_Icc (a := B) (b := 0)).union hp).mono_set
  intro x hx
  by_cases hx' : x ≤ 0
  · exact Or.inl ⟨hx, hx'⟩
  · exact Or.inr (lt_of_not_ge hx')

private theorem fixedBoxRow_norm (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (g : C𝔽) :
    ‖spectralZeroJet χ b t k g‖ ^ 2 = Real.exp (2 * b * L g) * (L g) ^ (2 * k) := by
  have hpos : 0 < ((ideleClassNorm F g).val : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have htwist : ‖ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) g‖ =
      Real.exp (b * L g) := by
    change ‖(χ g : ℂ) *
      (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Real.rpow_def_of_pos hpos,
      mul_comm]
  change ‖ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) g *
    (L g : ℂ) ^ k‖ ^ 2 = _
  rw [norm_mul, htwist, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hexp : Real.exp (b * L g) ^ 2 = Real.exp (2 * b * L g) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hpow : (|L g| ^ k) ^ 2 = (L g) ^ (2 * k) := by
    calc
      (|L g| ^ k) ^ 2 = (|L g| ^ 2) ^ k := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
      _ = ((L g) ^ 2) ^ k := congrArg (fun y : ℝ ↦ y ^ k) (sq_abs (L g))
      _ = (L g) ^ (2 * k) := (pow_mul _ _ _).symm
  rw [hexp, hpow]

private theorem fixedBoxRow_memLp (B : ℝ) (χ : PontryaginDual C𝔽) (t : ℝ) (k : ℕ) :
    MemLp ((L ⁻¹' Ici B).indicator (spectralZeroJet χ (-(1/2)) t k)) 2 μ𝔽 := by
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let ν := canonicalModulatedHaar m𝔽 hm
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm).exists.choose_spec.1
  let w := (Ici B).indicator (fun x : ℝ ↦ Real.exp (-x) * x ^ (2*k))
  have hν : Integrable (fun g : C𝔽 ↦ w (L g)) ν :=
    orbitalJet_logNorm_measurePreserving.integrable_comp_of_integrable (fixedBoxRow_radial B k)
  have hμ : Integrable (fun g : C𝔽 ↦ w (L g)) μ𝔽 := by
    rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    exact hν.smul_measure_nnreal
  have hc : Continuous (spectralZeroJet χ (-(1/2)) t k) :=
    (ideleClassNormTwist χ _).continuous.mul
      ((Complex.continuous_ofReal.comp orbitalJet_logNorm_continuous).pow k)
  apply (memLp_two_iff_integrable_sq_norm
    (hc.measurable.indicator (orbitalJet_logNorm_continuous.measurable measurableSet_Ici)).aestronglyMeasurable).2
  refine hμ.congr (.of_forall fun g ↦ ?_)
  change w (L g) = ‖(L ⁻¹' Ici B).indicator (spectralZeroJet χ (-(1/2)) t k) g‖ ^ 2
  by_cases hg : L g ∈ Ici B
  · rw [Set.indicator_of_mem (show g ∈ L ⁻¹' Ici B from hg), fixedBoxRow_norm, show 2 * (-(1/2) : ℝ) = -1 by norm_num, neg_one_mul]
    exact indicator_of_mem hg _
  · rw [Set.indicator_of_notMem (show g ∉ L ⁻¹' Ici B from hg)]
    simp [w, hg]

/-- Paper: (11.3.1.3)–(11.3.1.4), p. 494. On vectors supported above a fixed
log norm, the half-twisted orbital coordinates of each jet order extend to the
strip space, uniformly in character and ordinate.
Reconstruction: use a hard lower cutoff on the representing dual vector. -/
theorem primaryDivisorial_cutoffOrbitalJet (B : ℝ) (k : ℕ) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ C : ℝ, ∀ (χ : PontryaginDual C𝔽) (t : ℝ),
      ∃ Λ : StrongDual ℂ (CompactIntervalSobolev μ𝔽 L (-α) α s),
        ‖Λ‖ ≤ C ∧ ∀ f, Λ f = ∫ g in L ⁻¹' Ici B,
          f g * spectralZeroJet χ (-(1/2)) t k g ∂μ𝔽 := by
  let E := L ⁻¹' Ici B
  let d := fun g : C𝔽 ↦ (intervalSobolevDensity (-α) α s (L g))⁻¹
  let ν := (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (d g))
  have hE : MeasurableSet E := orbitalJet_logNorm_continuous.measurable measurableSet_Ici
  have hd (g : C𝔽) : 1 ≤ intervalSobolevDensity (-α) α s (L g) := by
    have hx : 1 ≤ max (Real.exp (2 * -α * L g)) (Real.exp (2 * α * L g)) := by
      rcases le_total (0 : ℝ) (L g) with hg | hg
      · exact (Real.one_le_exp (by positivity)).trans (le_max_right _ _)
      · exact (Real.one_le_exp (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hg])).trans
          (le_max_left _ _)
    exact one_le_mul_of_one_le_of_one_le hx
      (Real.one_le_rpow (by nlinarith [sq_nonneg (L g)]) (by positivity))
  have hmeas : Measurable d := by
    unfold d intervalSobolevDensity
    have := orbitalJet_logNorm_continuous (F := F) |>.measurable
    fun_prop
  have hle : ν ≤ μ𝔽 := by
    conv_rhs => rw [← withDensity_one (μ := μ𝔽)]
    apply withDensity_mono (.of_forall fun g ↦ ?_)
    change ENNReal.ofReal (d g) ≤ 1
    exact ENNReal.ofReal_le_one.mpr (inv_le_one_of_one_le₀ (hd g))
  have habs : μ𝔽 ≪ ν := withDensity_absolutelyContinuous' hmeas.ennreal_ofReal.aemeasurable
    (.of_forall fun g ↦ (ENNReal.ofReal_pos.mpr (inv_pos.mpr (zero_lt_one.trans_le (hd g)))).ne')
  let u (χ : PontryaginDual C𝔽) (t : ℝ) := E.indicator (spectralZeroJet χ (-(1/2)) t k)
  have hu (χ : PontryaginDual C𝔽) (t : ℝ) : MemLp (u χ t) 2 ν :=
    (fixedBoxRow_memLp B χ t k).mono_measure hle
  let v (χ : PontryaginDual C𝔽) (t : ℝ) := (hu χ t).toLp (u χ t)
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  obtain ⟨T, hT, -⟩ := modulatedIntervalSobolev_dual m𝔽 hm μ𝔽 (-α) α s (neg_le_self hα) hs
  refine ⟨‖v 1 0‖, fun χ t ↦ ⟨T.symm (v χ t), ?_, ?_⟩⟩
  · rw [T.symm.norm_map]
    apply le_of_eq
    simp only [v, Lp.norm_toLp]
    congr 1
    apply eLpNorm_congr_norm_ae (hu χ t).aestronglyMeasurable (hu 1 0).aestronglyMeasurable (.of_forall fun g ↦ ?_)
    by_cases hg : g ∈ E
    · simp only [u, indicator_of_mem hg]
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        ((fixedBoxRow_norm χ _ t k g).trans (fixedBoxRow_norm 1 _ 0 k g).symm)
    · simp [u, hg]
  · intro f
    have ht := (hT (T.symm (v χ t)) f).2
    rw [T.apply_symm_apply] at ht
    refine ht.trans ?_
    rw [← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards [habs.ae_eq (MemLp.coeFn_toLp (hu χ t))] with g hg
    rw [show v χ t g = u χ t g from hg]
    by_cases hg' : g ∈ E
    · simp [u, E, hg']
    · simp [u, E, hg']

end

/-! ### Nonvanishing after closure at a fixed bound -/

section

private theorem pwFloorDensity (L d α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ C > (0 : ℝ), ∀ x ≥ L, intervalSobolevDensity 0 0 d x ≤
      C * intervalSobolevDensity (1 / 2 - α) (1 / 2 + α) s x := by
  let n := ⌈d / 2⌉₊
  let k := 2 * n
  refine ⟨(k.factorial : ℝ) * Real.exp (1 + 2 * |L|), by positivity, ?_⟩
  intro x hx
  have hbase : (1 : ℝ) ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hpoly : (1 + x ^ 2) ^ (d / 2) ≤ (1 + |x|) ^ k := calc
    _ ≤ (1 + x ^ 2) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase (Nat.le_ceil _)
    _ ≤ ((1 + |x|) ^ 2) ^ n := by
      rw [Real.rpow_natCast]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith [sq_abs x, abs_nonneg x]) _
    _ = _ := (pow_mul _ _ _).symm
  have hx' : 1 + |x| ≤ (1 + 2 * |L|) + x := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; linarith [abs_nonneg L]
    · rw [abs_of_nonpos h]; linarith [neg_abs_le L]
  have hexp : Real.exp x ≤ intervalSobolevDensity (1/2-α) (1/2+α) s x := by
    have hb : Real.exp x ≤ max (Real.exp (2*(1/2-α)*x)) (Real.exp (2*(1/2+α)*x)) := by
      rcases le_total 0 x with h | h
      · exact (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hα h])).trans (le_max_right _ _)
      · exact (Real.exp_le_exp.mpr (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα h])).trans (le_max_left _ _)
    exact hb.trans (le_mul_of_one_le_right ((Real.exp_pos _).le.trans (le_max_left _ _))
      (Real.one_le_rpow hbase (by linarith : 0 ≤ s/2)))
  simp only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
  calc (1 + x^2) ^ (d/2) ≤ (1+|x|)^k := hpoly
    _ ≤ (k.factorial : ℝ) * Real.exp (1 + |x|) := by
      have h := Real.pow_div_factorial_le_exp (1 + |x|) (by positivity : 0 ≤ 1 + |x|) k
      simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0:ℝ) < k.factorial)).mp h
    _ ≤ ((k.factorial : ℝ) * Real.exp (1 + 2 * |L|)) * Real.exp x := by
      rw [mul_assoc, ← Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx') (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

/-- Paper: (11.3.1.3), p. 494. On a common lower support bound the half-twisted
strip norm controls every untwisted zero-line Sobolev norm. The constant is
independent of the representative. -/
theorem primaryDivisorialAbsolutePW_untwist_bound {G : Type*} [MeasurableSpace G]
    (μ : Measure G) (r : G → ℝ) (hr : ∀ g, 0 < r g) (hrm : Measurable r)
    (L α s d : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ C > (0 : ℝ), ∀ (φ : G → ℂ)
      (u : CompactIntervalSobolev μ (fun g ↦ Real.log (r g)) 0 0 d)
      (v : CompactIntervalSobolev μ (fun g ↦ Real.log (r g)) (-α) α s),
      (∀ g, Real.log (r g) < L → φ g = 0) →
      ((u : G → ℂ) =ᵐ[μ] φ) →
      ((v : G → ℂ) =ᵐ[μ] fun g ↦ ((r g ^ (1/2 : ℝ) : ℝ) : ℂ) * φ g) →
      ‖u‖ ≤ C * ‖v‖ := by
  obtain ⟨C,hC,hbound⟩ := pwFloorDensity L d α s hα hs
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro φ u v hsupport hu hv
  obtain ⟨hi, hnorm⟩ := globalThetaSobolev_norm_aux μ r hr hrm 0 0 0 d φ u (by simpa using hu)
  obtain ⟨hi', hnorm'⟩ := globalThetaSobolev_norm_aux μ r hr hrm (1/2) (-α) α s φ v hv
  simp only [zero_add] at hi hnorm
  rw [hnorm, hnorm', ← Real.sqrt_mul hC.le, ← integral_const_mul]
  apply Real.sqrt_le_sqrt
  apply integral_mono hi (hi'.const_mul C)
  intro g
  by_cases h : L ≤ Real.log (r g)
  · dsimp only
    rw [mul_left_comm C]
    simpa only [sub_eq_add_neg] using mul_le_mul_of_nonneg_left (hbound _ h) (sq_nonneg ‖φ g‖)
  · simp [hsupport g (lt_of_not_ge h)]

private theorem primaryDivisorialAbsolutePW_detect {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (I K : Submodule ℂ E) (hK : IsClosed (K : Set E))
    (L : ℝ → Submodule ℂ E) (hL : ∀ X, L X ≤ K) (v : I)
    (hv : v ∈ (⨆ X, (L X).comap I.subtype).topologicalClosure) : v.val ∈ K := by
  change v ∈ K.comap I.subtype
  exact Submodule.topologicalClosure_minimal _ (iSup_le fun X ↦ Submodule.comap_mono (hL X))
    (hK.preimage continuous_subtype_val) hv

private theorem primaryDivisorialAbsolutePW_exists_outside_uncut {S T : Finset V}
    (ω : PontryaginDual C₁) (hω : NormOneCharacterUnramifiedOutside ω S)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    {d : ℝ} (hd : 0 ≤ d)
    (hlt : sLocalUncutCarving d ω T < sLocalUncutCarving d ω ∅) :
    ∃ X > (0 : ℝ), ∃ f : sAdelePolarSubspace F S,
      f.val ∈ sLocalPWTests (S := S) le_rfl (sLocalPWBox S X) ∧
      let g : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f.val,
        sAdeleSchwartzToGlobal_mem_polarSubspace f⟩
      (memLp_homogeneousTheta_zeroLine d ω g).toLp _ ∉ sLocalUncutCarving d ω T := by
  classical
  by_contra! h
  apply hlt.not_ge
  rw [sLocalUncutCarving_empty_eq_globalThetaSobolev d hd ω]
  let K := sLocalUncutCarving d ω T
  have hK : IsClosed (K : Set (IdeleClassZeroLineSobolev F d)) := by
    unfold K sLocalUncutCarving
    exact Submodule.isClosed_topologicalClosure _
  have hD := globalThetaSobolev_isotype_le_closure_absLevel (F := F) (S := S) hd 0 ω hω hPic
  unfold globalAbsolutePWSobolev globalPWThetaSobolevMap at hD
  simp only [modulationWeight_zero] at hD
  let W (l : ℝ) := CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) l 0 d
  let Iso (l : ℝ) (hl : l ≤ 0) : Submodule ℂ (W l) := actionIsotype
    ((hardySobolevTranslation μ𝔽 (continuousIdeleClassNorm F) l 0 d hl hd).comp
      (ideleClassNorm F).ker.subtype) ω
  let barrier (l : ℝ) := ∀ (hl : l ≤ 0) (D : Submodule ℂ (W l)), IsClosed (D : Set (W l)) →
    (∀ (X : ℝ) (f : sAdelePolarSubspace F S), f.val ∈ sLocalPWTests (S := S) le_rfl
      (sLocalPWBox S X) → ∀ hf : MemLp (homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F S f.val))
        2 (intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) l 0 d false), hf.toLp _ ∈ D) →
    globalThetaSobolev F 0 hl hd ⊓ Iso l hl ≤ D
  have hbar : barrier (-0) := by
    intro hl D hc hg u hu
    let I := Iso (-0) hl
    let v : I := ⟨u, hu.2⟩
    have hv := hD (show v ∈ (globalThetaSobolev F 0 hl hd).comap I.subtype from hu.1)
    refine primaryDivisorialAbsolutePW_detect I D hc _ ?_ v hv
    intro X
    exact Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr (by
      rintro _ ⟨f, rfl⟩
      exact hg X f.val f.property _)) hc
  have hbar₀ : barrier 0 := Eq.mp (congrArg barrier (neg_zero : -(0 : ℝ) = 0)) hbar
  apply hbar₀ le_rfl K hK
  intro X f hf _
  let Y := max X 1
  have hXY : X ≤ Y := le_max_left _ _
  have hbox : sLocalPWBox S X ⊆ sLocalPWBox S Y :=
      fun _ hx ↦ ⟨fun w ↦ (hx.1 w).trans hXY, fun v ↦ (hx.2 v).trans hXY⟩
  obtain ⟨g, hg, hgc, hgs⟩ := (mem_sLocalPWTests le_rfl _ _).mp hf
  have hY := (mem_sLocalPWTests le_rfl (sLocalPWBox S Y) f.val).mpr
      ⟨g, hg, hgc, hgs.trans (Set.preimage_mono hbox)⟩
  exact Classical.not_not.mp (h Y (zero_lt_one.trans_le (le_max_right _ _)) f hY)

/-- A comparison of norms on a common test space transfers separation from the closure
of a family of tests to the stronger norm. -/
private theorem primaryDivisorial_nonmem_closure_of_norm_le
    {E H K : Type*} [AddCommGroup E] [Module ℂ E] [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K] (u : E →ₗ[ℂ] H) (v : E →ₗ[ℂ] K)
    {C : ℝ} (hC : ∀ x, ‖u x‖ ≤ C * ‖v x‖) (D : Set E) (f : E)
    (hf : u f ∉ closure (u '' D)) : v f ∉ closure (v '' D) := by
  intro hv
  apply hf
  rw [Metric.mem_closure_iff] at hv ⊢
  intro ε hε
  let c := max C 1
  have hc : 0 < c := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨_, ⟨g, hg, rfl⟩, hdist⟩ := hv (ε / c) (div_pos hε hc)
  refine ⟨u g, ⟨g, hg, rfl⟩, ?_⟩
  rw [dist_eq_norm, ← map_sub] at hdist ⊢
  exact (hC _).trans_lt ((mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg _)).trans_lt
    (by change c * _ < ε; rw [mul_comm c]; exact (lt_div_iff₀ hc).mp hdist))
local notation "P₀" => adelePolarSubspace F
local notation "r𝔽" => (fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ))
local notation "PWstrip(" l "," r "," s ")" =>
  CompactIntervalSobolev μ𝔽 (fun g ↦ Real.log (r𝔽 g)) l r s

/-- The polar homogeneous theta map as a linear map into the weighted strip space. -/
private theorem primaryDivisorialAbsolutePW_stripMap (ω : PontryaginDual C₁)
    (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    ∃ j : P₀ →ₗ[ℂ] PWstrip(l,r,s), ∀ f : P₀, ((j f) : C𝔽 → ℂ) =ᵐ[μ𝔽]
      fun g ↦ ((r𝔽 g ^ a : ℝ) : ℂ) * homogeneousAdelicTheta ω f.val g := by
  let q := (homogeneousAdelicThetaLinearMap F ω).ker.mkQ
  let Q := (q.comp (P₀).subtype).codRestrict (globalPolarFreeThetaSubmodule (F := F) ω)
    fun f ↦ ⟨f.val, f.property, rfl⟩
  obtain ⟨j, -, -, hj⟩ := exists_globalHomogeneousThetaSobolevInclusion (F := F) (a := a) hI hs ω
  let intoAmbient (U : Submodule ℂ PWstrip(l,r,s)) (A : Submodule ℂ U) :=
    U.subtype.comp A.subtype
  exact ⟨(intoAmbient _ _).comp (j.toLinearMap.comp Q), fun f ↦ (hj f (Q f) rfl).2⟩

private theorem primaryDivisorialAbsolutePW_stripMap_zero {d : ℝ} (ω : PontryaginDual C₁)
    (u : P₀ →ₗ[ℂ] PWstrip(0,0,d)) (hu : ∀ f : P₀,
      ((u f) : C𝔽 → ℂ) =ᵐ[μ𝔽] homogeneousAdelicTheta ω f.val) (f : P₀) :
    u f = (memLp_homogeneousTheta_zeroLine d ω f).toLp _ := by
  apply Lp.ext
  exact ((hu f).filter_mono (withDensity_absolutelyContinuous _ _).ae_le).trans
    (MemLp.coeFn_toLp (memLp_homogeneousTheta_zeroLine d ω f)).symm

/-- A test in the smooth principal-value denominator maps into the closed zero-line
stage. Taking an intersection with a fixed Fourier level therefore preserves this inclusion. -/
private theorem primaryDivisorialAbsolutePW_stripMap_mem {d : ℝ} (ω : PontryaginDual C₁)
    (u : P₀ →ₗ[ℂ] PWstrip(0,0,d)) (hu : ∀ f : P₀,
      ((u f) : C𝔽 → ℂ) =ᵐ[μ𝔽] homogeneousAdelicTheta ω f.val)
    (T : Finset V) (f : P₀) (hf : (Submodule.Quotient.mk f :
      P₀ ⧸ ((homogeneousAdelicThetaLinearMap F ω).domRestrict P₀).ker) ∈ divisorialThetaStage ω T) :
    u f ∈ sLocalUncutCarving d ω T := by
  have hr : divisorialThetaStage ω T = (divisorialThetaRepresentative ω T).range :=
    Submodule.span_eq (divisorialThetaRepresentative ω T).range
  obtain ⟨p, hp⟩ := hr ▸ hf
  let g := adelePolarPrincipalValue (F := F) T p
  have hg : homogeneousAdelicTheta ω g.val = homogeneousAdelicTheta ω f.val := by
    have he := (Submodule.Quotient.eq _).mp hp
    change (homogeneousAdelicThetaLinearMap F ω) (g.val - f.val) = 0 at he
    exact sub_eq_zero.mp ((map_sub (homogeneousAdelicThetaLinearMap F ω) _ _).symm.trans he)
  have he : u f = u g := Lp.ext (((hu f).trans ((hg ▸ hu g).symm)).filter_mono
    (withDensity_absolutelyContinuous _ _).ae_le)
  rw [he, primaryDivisorialAbsolutePW_stripMap_zero ω u hu g]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨p, rfl⟩)
/-- Paper: (11.3.1.3), p. 494. One polar representative survives in the first-stage
quotient in each sufficiently large fixed Fourier box, on every half-twisted strip.
Reconstruction: intersect the smooth principal-value denominator with the Fourier
level before taking its strip-norm closure. -/
def PrimaryDivisorialAbsolutePWSeparated (S T : Finset V) (ω : PontryaginDual C₁) : Prop :=
  ∃ X₀ > (0 : ℝ), ∃ f : primaryDivisorialAbsolutePWTests (F := F) S X₀,
    ∀ (α s : ℝ), 0 ≤ α → 0 ≤ s →
      ∃ j : P₀ →ₗ[ℂ] PWstrip(-α,α,s),
        (∀ g : P₀, ((j g) : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦
          ((r𝔽 x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * homogeneousAdelicTheta ω g.val x) ∧
        ∀ X ≥ X₀, let W := primaryDivisorialAbsolutePWTests (F := F) S X
          let q := ((homogeneousAdelicThetaLinearMap F ω).domRestrict P₀).ker.mkQ
          f.val ∈ W ∧ j f.val ∉ ((W ⊓ (divisorialThetaStage ω T).comap q).map j).topologicalClosure

/-- Paper: (11.3.1.3), p. 494. Properness on an untwisted zero line gives
a single witness to separation for every larger finite box and every half-twisted strip. -/
theorem primaryDivisorialAbsolutePW_noncollapse {S T : Finset V}
    (ω : PontryaginDual C₁) (hω : NormOneCharacterUnramifiedOutside ω S)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    {d : ℝ} (hd : 0 ≤ d) (hlt : sLocalUncutCarving d ω T < sLocalUncutCarving d ω ∅) :
    PrimaryDivisorialAbsolutePWSeparated S T ω := by
  classical
  obtain ⟨u, hU⟩ := primaryDivisorialAbsolutePW_stripMap (F := F) ω 0 (l := 0) le_rfl hd
  have hu (f : P₀) : ((u f) : C𝔽 → ℂ) =ᵐ[μ𝔽] homogeneousAdelicTheta ω f.val := by
    simpa only [Real.rpow_zero, Complex.ofReal_one, one_mul] using hU f
  obtain ⟨X₀, hX₀, fS, hfS, hf⟩ := primaryDivisorialAbsolutePW_exists_outside_uncut ω hω hPic hd hlt
  let f : P₀ := ⟨sAdeleSchwartzToGlobal F S fS.val, sAdeleSchwartzToGlobal_mem_polarSubspace fS⟩
  have hf₀ : f ∈ primaryDivisorialAbsolutePWTests (F := F) S X₀ :=
    Submodule.mem_map.mpr ⟨_, hfS, rfl⟩
  have hnon : u f ∉ sLocalUncutCarving d ω T := by
    rw [primaryDivisorialAbsolutePW_stripMap_zero ω u hu f]
    exact hf
  refine ⟨X₀, hX₀, ⟨f, hf₀⟩, fun α s hα hs ↦ ?_⟩
  obtain ⟨j, hj⟩ := primaryDivisorialAbsolutePW_stripMap (F := F) ω (1/2) (neg_le_self hα) hs
  refine ⟨j, hj, fun X hX₀X ↦ ?_⟩
  let W := primaryDivisorialAbsolutePWTests (F := F) S X
  have hX : 0 < X := hX₀.trans_le hX₀X
  have hbox : sLocalPWBox S X₀ ⊆ sLocalPWBox S X :=
    fun _ h ↦ ⟨fun v ↦ (h.1 v).trans hX₀X, fun v ↦ (h.2 v).trans hX₀X⟩
  obtain ⟨b, hb, hbc, hbs⟩ := (mem_sLocalPWTests le_rfl _ _).mp hfS
  have hmem : fS.val ∈ sLocalPWTests (S := S) le_rfl (sLocalPWBox S X) :=
    (mem_sLocalPWTests le_rfl _ _).mpr ⟨b, hb, hbc, hbs.trans (Set.preimage_mono hbox)⟩
  let f' : W := ⟨f, Submodule.mem_map.mpr ⟨_, hmem, rfl⟩⟩
  refine ⟨f'.property, ?_⟩
  let q := ((homogeneousAdelicThetaLinearMap F ω).domRestrict P₀).ker.mkQ
  let D := (divisorialThetaStage ω T).comap (q.comp W.subtype)
  have hclosed : IsClosed (sLocalUncutCarving d ω T : Set (PWstrip(0,0,d))) :=
    Submodule.isClosed_topologicalClosure _
  have huD : (u.domRestrict W) f' ∉ closure (u.domRestrict W '' (D : Set W)) := by
    have hsub : u.domRestrict W '' (D : Set W) ⊆ sLocalUncutCarving d ω T := by
      rintro _ ⟨g, hg, rfl⟩
      exact primaryDivisorialAbsolutePW_stripMap_mem ω u hu T g.val hg
    exact fun h ↦ hnon (closure_minimal hsub hclosed h)
  obtain ⟨B, hB, hsupport⟩ := primaryDivisorialAbsolutePW_support S hPic ω hω hX
  have hpos (g : C𝔽) : 0 < r𝔽 g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hcont : Continuous r𝔽 := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  obtain ⟨C, -, hC⟩ := primaryDivisorialAbsolutePW_untwist_bound μ𝔽 r𝔽 hpos hcont.measurable
    (Real.log B⁻¹) α s d hα hs
  have hbound (g : W) : ‖u g.val‖ ≤ C * ‖j g.val‖ := by
    apply hC (homogeneousAdelicTheta ω g.val.val) _ _ _ (hu g.val) (hj g.val)
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hx.not_ge (Real.log_le_log (inv_pos.mpr hB) (hsupport g.val g.property h))
  have hjD := primaryDivisorial_nonmem_closure_of_norm_le (u.domRestrict W) (j.domRestrict W)
    hbound (D : Set W) f' huD
  intro h
  apply hjD
  have hsub : ((W ⊓ (divisorialThetaStage ω T).comap q).map j : Set _) ⊆
      j.domRestrict W '' (D : Set W) := by
    rintro _ ⟨g, ⟨hg, hgD⟩, rfl⟩
    exact ⟨⟨g, hg⟩, hgD, rfl⟩
  exact closure_mono hsub h

end

/-! ### Comparison of the strip norms under finite depletion -/

section

open scoped Classical

local notation "ℬ₀" => ↥(adelePolarSubspace F)
local notation "pvTest(" S ", " f ")" =>
  (⟨adelePrincipalValue F S (f : ℬ₀).val, adelePrincipalValue_mem_polarSubspace S f⟩ : ℬ₀)
local notation "theta(" f ")" => (Submodule.Quotient.mk (f : ℬ₀) : GlobalPolarFreeThetaSpace F)
local notation "j(" a ", " hI ", " hs ")" => globalThetaSobolevInclusion F a hI hs

local notation "A(" twist ", " hI ", " hs ", " ω ")" =>
  (existsUnique_globalThetaSobolevAverage (F := F) (a := twist) hI hs ω).exists.choose
local notation "u(" a ", " hI ", " hs ", " ω ", " f ")" =>
  (A(a, hI, hs, ω) (j(a, hI, hs) (theta(f)))).val
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)

private theorem primaryPW_homogeneous_norm (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s) (ω : PontryaginDual C₁) (f : ℬ₀) :
    let w := fun g : C𝔽 ↦ ‖homogeneousAdelicTheta ω f.val g‖ ^ 2 *
      intervalSobolevDensity (a+l) (a+r) s (logIdeleClassNorm F g)
    Integrable w μ𝔽 ∧ ‖u(a, hI, hs, ω, f)‖ = Real.sqrt (∫ g, w g ∂μ𝔽) := by
  let x : globalPolarFreeThetaSubmodule (F := F) ω :=
    ⟨Submodule.Quotient.mk f.val, Submodule.mem_map.mpr ⟨f.val, f.property, rfl⟩⟩
  have hx := (exists_globalHomogeneousThetaSobolevInclusion
    (F := F) (a := a) hI hs ω).choose_spec.2.2 f x rfl
  have hrep := hx.2
  rw [hx.1] at hrep
  exact globalThetaSobolev_norm_aux μ𝔽 (fun g ↦ ((m𝔽 g).val : ℝ))
    (fun g ↦ NNReal.coe_pos.mpr (Units.zero_lt _))
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).measurable
    a l r s (homogeneousAdelicTheta ω f.val) (u(a, hI, hs, ω, f)).val hrep

/-- Paper: (10.1.1.6), p. 435. The homogeneous strip test norm with effective endpoints. -/
def primaryDivisorialStripNorm (l r s : ℝ) (ω : PontryaginDual C₁) (f : ℬ₀) : ℝ :=
  Real.sqrt (∫ g : C𝔽, ‖homogeneousAdelicTheta ω f.val g‖ ^ 2 *
    intervalSobolevDensity l r s (logIdeleClassNorm F g) ∂μ𝔽)

private theorem primaryPW_energy_compare {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (φ : G → ℂ) (v w : G → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hv : Integrable (fun g ↦ ‖φ g‖^2 * v g) μ)
    (hw : Integrable (fun g ↦ ‖φ g‖^2 * w g) μ)
    (h : ∀ g, φ g ≠ 0 → v g ≤ K * w g) :
    Real.sqrt (∫ g, ‖φ g‖^2 * v g ∂μ) ≤ Real.sqrt K * Real.sqrt (∫ g, ‖φ g‖^2 * w g ∂μ) := by
  rw [← Real.sqrt_mul hK, ← integral_const_mul]
  apply Real.sqrt_le_sqrt
  apply integral_mono hv (hw.const_mul K)
  intro g
  by_cases hz : φ g = 0
  · simp [hz]
  · dsimp only
    rw [mul_left_comm K]
    exact mul_le_mul_of_nonneg_left (h g hz) (sq_nonneg _)

private theorem primaryPW_integrable {l r s : ℝ} (hlr : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (f : ℬ₀) :
    Integrable (fun g : C𝔽 ↦ ‖homogeneousAdelicTheta ω f.val g‖ ^ 2 *
      intervalSobolevDensity l r s (logIdeleClassNorm F g)) μ𝔽 := by
  simpa only [zero_add] using (primaryPW_homogeneous_norm (F := F) 0 hlr hs ω f).1

private theorem primaryPW_endpoint_eq (b : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (f : ℬ₀) :
    primaryDivisorialStripNorm b b s ω f = ‖u(b, le_refl (0 : ℝ), hs, ω, f)‖ := by
  simpa only [primaryDivisorialStripNorm, add_zero] using
    (primaryPW_homogeneous_norm (F := F) b (le_refl (0 : ℝ)) hs ω f).2.symm

private theorem primaryPW_clm_inverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (M : E →L[ℂ] E) (hM : Bijective M) :
    ∃ c ≥ (0 : ℝ), ∀ x, ‖x‖ ≤ c * ‖M x‖ := by
  let e := ContinuousLinearEquiv.ofBijective M (LinearMap.ker_eq_bot.mpr hM.1)
    (LinearMap.range_eq_top.mpr hM.2)
  refine ⟨‖e.symm.toContinuousLinearMap‖, norm_nonneg _, fun x ↦ ?_⟩
  exact (congrArg norm (e.symm_apply_apply x).symm).le.trans
    (e.symm.toContinuousLinearMap.le_opNorm (e x))

private theorem primaryPW_endpoint_transport {D E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (N : D → ℝ) (q : D → E) (P : D → D) (M : E →L[ℂ] E)
    (hN : ∀ f, N f = ‖q f‖) (hP : ∀ f, M (q f) = q (P f)) :
    (∀ f, N (P f) ≤ ‖M‖ * N f) ∧
      ∀ c : ℝ, (∀ x, ‖x‖ ≤ c * ‖M x‖) → ∀ f, N f ≤ c * N (P f) := by
  constructor
  · intro f
    rw [hN, hN, ← hP]
    exact M.le_opNorm _
  · intro c hc f
    rw [hN, hN, ← hP]
    exact hc _

private theorem primaryPW_endpoint_both (T : Finset V) (b : ℝ) {s : ℝ}
    (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    let M := globalThetaSobolevPrincipalValue F T b hs
    let N := primaryDivisorialStripNorm b b s ω
    (∀ f : ℬ₀, N (pvTest(T, f)) ≤ ‖M‖ * N f) ∧
      ∀ c : ℝ, (∀ x, ‖x‖ ≤ c * ‖M x‖) → ∀ f : ℬ₀, N f ≤ c * N (pvTest(T, f)) :=
  primaryPW_endpoint_transport _ (fun f : ℬ₀ ↦ u(b, le_refl (0 : ℝ), hs, ω, f))
    (fun f : ℬ₀ ↦ pvTest(T, f)) (globalThetaSobolevPrincipalValue F T b hs)
    (primaryPW_endpoint_eq b hs ω) (globalThetaSobolevPrincipalValue_homogeneous_apply T b hs ω)

private theorem primaryPW_endpoint_inverse (T : Finset V) {b s : ℝ}
    (hb : 0 < b) (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    ∃ c ≥ (0 : ℝ), ∀ f : ℬ₀, primaryDivisorialStripNorm b b s ω f ≤
      c * primaryDivisorialStripNorm b b s ω (pvTest(T, f)) := by
  have : CompleteSpace (globalThetaSobolev F b (le_refl (0 : ℝ)) hs) :=
    (globalThetaSobolev_closed_complete_separable (F := F) b (le_refl (0 : ℝ)) hs).2.1
  obtain ⟨c, hc, h⟩ := primaryPW_clm_inverse (globalThetaSobolevPrincipalValue F T b hs)
    (globalThetaSobolevPrincipalValue_bijective_of_pos (F := F) T hb hs)
  exact ⟨c, hc, (primaryPW_endpoint_both T b hs ω).2 c h⟩

private theorem primaryPW_strip_density_le_endpoint {α L x : ℝ} (s : ℝ)
    (hα : 0 ≤ α) (hx : L ≤ x) :
    intervalSobolevDensity (1/2 + -α) (1/2+α) s x ≤
      Real.exp (4*α*|L|) * intervalSobolevDensity (1/2+α) (1/2+α) s x := by
  unfold intervalSobolevDensity
  rw [max_self, ← mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply max_le
  · apply Real.exp_le_exp.mpr
    have h := mul_nonneg hα (show 0 ≤ |L| + x by linarith [neg_abs_le L])
    nlinarith
  · apply Real.exp_le_exp.mpr
    linarith [mul_nonneg hα (abs_nonneg L)]

private theorem primaryPW_endpoint_under_strip {l r s : ℝ} (hlr : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (f : ℬ₀) {b : ℝ} (hb : b = l ∨ b = r) :
    primaryDivisorialStripNorm b b s ω f ≤ primaryDivisorialStripNorm l r s ω f := by
  have h := primaryPW_energy_compare μ𝔽 (homogeneousAdelicTheta ω f.val)
    (fun g ↦ intervalSobolevDensity b b s (logIdeleClassNorm F g))
    (fun g ↦ intervalSobolevDensity l r s (logIdeleClassNorm F g)) 1 zero_le_one
    (primaryPW_integrable (le_refl b) hs ω f) (primaryPW_integrable hlr hs ω f) (fun g _ ↦ by
      simp only [one_mul, intervalSobolevDensity, max_self]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rcases hb with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _)
  simpa only [primaryDivisorialStripNorm, Real.sqrt_one, one_mul] using h

private theorem primaryPW_sqrt_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x+y) ≤ Real.sqrt x + Real.sqrt y := by
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

private theorem primaryPW_strip_under_endpoints {l r s : ℝ} (hlr : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (f : ℬ₀) :
    primaryDivisorialStripNorm l r s ω f ≤
      primaryDivisorialStripNorm l l s ω f + primaryDivisorialStripNorm r r s ω f := by
  let W (a b : ℝ) := fun g : C𝔽 ↦ ‖homogeneousAdelicTheta ω f.val g‖^2 *
    intervalSobolevDensity a b s (logIdeleClassNorm F g)
  have hpos (a b : ℝ) (g : C𝔽) : 0 ≤ W a b g := by
    dsimp [W, intervalSobolevDensity]
    positivity
  have hpoint (g : C𝔽) : W l r g ≤ W l l g + W r r g := by
    dsimp [W, intervalSobolevDensity]
    simp only [max_self, ← mul_add, ← add_mul]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact max_le (le_add_of_nonneg_right (Real.exp_pos _).le) (le_add_of_nonneg_left (Real.exp_pos _).le)
  have h₁ := primaryPW_integrable (le_refl l) hs ω f
  have h₂ := primaryPW_integrable (le_refl r) hs ω f
  change Real.sqrt (∫ g, W l r g ∂μ𝔽) ≤ Real.sqrt (∫ g, W l l g ∂μ𝔽) + Real.sqrt (∫ g, W r r g ∂μ𝔽)
  apply (Real.sqrt_le_sqrt (integral_mono (primaryPW_integrable hlr hs ω f) (h₁.add h₂) hpoint)).trans
  simp only [Pi.add_apply]
  rw [integral_add h₁ h₂]
  exact primaryPW_sqrt_add (integral_nonneg (hpos l l)) (integral_nonneg (hpos r r))

/-- Paper: (11.3.1.3)–(11.3.1.4), p. 494. On a fixed box, applying a fixed finite
set of principal values gives equivalent half-twisted strip norms on homogeneous
polar tests. Both bounds are uniform in the representative.
Reconstruction: this is a norm estimate on the fixed-box test images. -/
theorem primaryDivisorialAbsolutePW_principalValue_bounds (S T : Finset V)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) {X α s : ℝ} (hX : 0 < X)
    (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let l := 1/2 + -α
    let r := 1/2 + α
    ∃ C ≥ (0 : ℝ), ∀ f ∈ primaryDivisorialAbsolutePWTests (F := F) S X,
      primaryDivisorialStripNorm l r s ω f ≤ C * primaryDivisorialStripNorm l r s ω (pvTest(T, f)) ∧
      primaryDivisorialStripNorm l r s ω (pvTest(T, f)) ≤ C * primaryDivisorialStripNorm l r s ω f := by
  intro l r
  have hlr : l ≤ r := by dsimp [l, r]; linarith
  have hr : 0 < r := by dsimp [r]; linarith
  obtain ⟨B, hB, hbox⟩ := primaryDivisorialAbsolutePW_support S hPic ω hω hX
  let L := Real.log B⁻¹
  let K := Real.exp (4*α*|L|)
  obtain ⟨c, hc, hinv⟩ := primaryPW_endpoint_inverse T hr hs ω
  let U := ‖globalThetaSobolevPrincipalValue F T l hs‖ + ‖globalThetaSobolevPrincipalValue F T r hs‖
  refine ⟨max (Real.sqrt K * c) U, le_max_of_le_left (mul_nonneg (Real.sqrt_nonneg _) hc), ?_⟩
  intro f hf
  let y := pvTest(T, f)
  let N := fun (a b : ℝ) (g : ℬ₀) ↦ primaryDivisorialStripNorm a b s ω g
  have hn (a b : ℝ) (g : ℬ₀) : 0 ≤ N a b g := Real.sqrt_nonneg _
  have hstrip : N l r f ≤ Real.sqrt K * N r r f :=
    primaryPW_energy_compare μ𝔽 (homogeneousAdelicTheta ω f.val)
      (fun g ↦ intervalSobolevDensity l r s (logIdeleClassNorm F g))
      (fun g ↦ intervalSobolevDensity r r s (logIdeleClassNorm F g)) K (Real.exp_pos _).le
      (primaryPW_integrable hlr hs ω f) (primaryPW_integrable (le_refl r) hs ω f) (fun g hg ↦ by
        have hx := hbox f hf (subset_tsupport _ hg)
        exact primaryPW_strip_density_le_endpoint s hα (Real.log_le_log (inv_pos.mpr hB) hx))
  have hleft (g : ℬ₀) : N l l g ≤ N l r g := primaryPW_endpoint_under_strip hlr hs ω g (Or.inl rfl)
  have hright (g : ℬ₀) : N r r g ≤ N l r g := primaryPW_endpoint_under_strip hlr hs ω g (Or.inr rfl)
  constructor
  · calc
      _ ≤ Real.sqrt K * (c * N r r y) := hstrip.trans (mul_le_mul_of_nonneg_left (hinv f) (Real.sqrt_nonneg _))
      _ ≤ (Real.sqrt K * c) * N l r y := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (hright y) (mul_nonneg (Real.sqrt_nonneg _) hc)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (hn _ _ _)
  · calc
      _ ≤ N l l y + N r r y := primaryPW_strip_under_endpoints hlr hs ω y
      _ ≤ ‖globalThetaSobolevPrincipalValue F T l hs‖ * N l r f +
          ‖globalThetaSobolevPrincipalValue F T r hs‖ * N l r f := add_le_add
        (((primaryPW_endpoint_both T l hs ω).1 f).trans (mul_le_mul_of_nonneg_left (hleft f) (norm_nonneg _)))
        (((primaryPW_endpoint_both T r hs ω).1 f).trans (mul_le_mul_of_nonneg_left (hright f) (norm_nonneg _)))
      _ = U * N l r f := (add_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (hn _ _ _)

local notation "L" => logIdeleClassNorm F

private theorem fixedBoxRow_cancel (χ : PontryaginDual C𝔽) (t : ℝ) (k : ℕ)
    (θ : C𝔽 → ℂ) (g : C𝔽) :
    modulationWeight m𝔽 (1/2) θ g * spectralZeroJet χ (-(1/2)) t k g =
      θ g * spectralZeroJet χ 0 t k g := by
  let q : ℝ := ((ideleClassNorm F g).val : ℝ)
  have hpos : 0 < q := NNReal.coe_pos.mpr (Units.zero_lt _)
  change ((q ^ (1/2 : ℝ) : ℝ) : ℂ) * θ g *
    ((χ g : ℂ) * (q : ℂ) ^ (((-(1/2) : ℝ) : ℂ) + (t : ℂ) * Complex.I) * _) =
    θ g * ((χ g : ℂ) * (q : ℂ) ^ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) * _)
  have hq : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  rw [Complex.ofReal_cpow hpos.le]
  have he : ((q : ℂ) ^ ((1/2 : ℝ) : ℂ)) *
      (q : ℂ) ^ (((-(1/2) : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      (q : ℂ) ^ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    rw [← Complex.cpow_add _ _ hq]
    congr 1
    push_cast
    ring
  rw [← he]
  ring

/-- Paper: (11.3.1.3)–(11.3.1.4), p. 494, and the half twist on p. 496.
At a fixed Fourier bound, the half-twisted strip norm after any fixed finite
depletion controls all ordinary orbital jets of the undepleted representative.
The bound is uniform in the evaluating character and ordinate.
Reconstruction: these are the coordinates transported from the single-prime model
in the algebraic comparison, before multiplying by the earlier Euler factors. -/
theorem primaryDivisorialAbsolutePW_recoveredOrbitalJet_le (S T : Finset V)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) {X α s : ℝ} (hX : 0 < X)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (k : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ (χ : PontryaginDual C𝔽) (t : ℝ),
      ∀ f ∈ primaryDivisorialAbsolutePWTests (F := F) S X,
      ‖∫ g, homogeneousAdelicTheta ω f.val g * spectralZeroJet χ 0 t k g ∂μ𝔽‖ ≤
        C * primaryDivisorialStripNorm (1/2 + -α) (1/2 + α) s ω (pvTest(T, f)) := by
  obtain ⟨B, hB, hbox⟩ := primaryDivisorialAbsolutePW_support S hPic ω hω hX
  let b := Real.log B⁻¹
  let E := L ⁻¹' Ici b
  have hE : MeasurableSet E := orbitalJet_logNorm_continuous.measurable measurableSet_Ici
  obtain ⟨c, hrow⟩ := primaryDivisorial_cutoffOrbitalJet (F := F) b k hα hs
  obtain ⟨D, hD, hbound⟩ := primaryDivisorialAbsolutePW_principalValue_bounds S T hPic ω hω hX hα hs
  refine ⟨max c 0 * D, mul_nonneg (le_max_right _ _) hD, fun χ t f hf ↦ ?_⟩
  obtain ⟨Λ, hΛ, hpair⟩ := hrow χ t
  let x : globalPolarFreeThetaSubmodule (F := F) ω :=
    ⟨Submodule.Quotient.mk f.val, ⟨f.val, f.property, rfl⟩⟩
  have hx := (exists_globalHomogeneousThetaSobolevInclusion (F := F)
    (a := (1/2)) (neg_le_self hα) hs ω).choose_spec.2.2 f x rfl
  have hu := hx.2
  rw [hx.1] at hu
  let u₀ := u((1/2), neg_le_self hα, hs, ω, f)
  have he : Λ u₀.val = ∫ g, homogeneousAdelicTheta ω f.val g * spectralZeroJet χ 0 t k g ∂μ𝔽 := by
    rw [hpair, ← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards [hu] with g hg
    by_cases h : g ∈ E
    · rw [indicator_of_mem h, show u₀.val g = _ from hg]
      exact fixedBoxRow_cancel χ t k _ g
    · rw [indicator_of_notMem h]
      have hz : homogeneousAdelicTheta ω f.val g = 0 := not_not.mp fun hn ↦ h
        (Real.log_le_log (inv_pos.mpr hB) (hbox f hf (subset_tsupport _ hn)))
      rw [hz, zero_mul]
  rw [← he]
  calc
    ‖Λ u₀.val‖ ≤ max c 0 * ‖u₀‖ :=
      (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_right (hΛ.trans (le_max_left _ _)) (norm_nonneg _))
    _ = max c 0 * primaryDivisorialStripNorm (1/2 + -α) (1/2 + α) s ω f := by
      rw [(primaryPW_homogeneous_norm (1/2) (neg_le_self hα) hs ω f).2]
      rfl
    _ ≤ _ := (mul_le_mul_of_nonneg_left (hbound f hf).1 (le_max_right _ _)).trans_eq
      (mul_assoc _ _ _).symm

end

/-! ### The quotient seminorms -/

section

local notation "P₀" => adelePolarSubspace F
local notation "above(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset

private theorem primaryPW_quotient_cost {ι : Type*} [Nonempty ι]
    {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {C : ℝ} (hC : 0 ≤ C) (hab : ∀ i, a i ≤ C * b i) :
    (⨅ i, a i) ≤ C * ⨅ i, b i := by
  rw [Real.mul_iInf_of_nonneg hC]
  exact le_ciInf fun i ↦ (ciInf_le ⟨0, fun _ ⟨j, hj⟩ ↦ hj ▸ ha j⟩ i).trans (hab i)

/-- Paper: (11.3.1.3), p. 494. The comparison using the same representatives is
bounded in both directions for the quotient seminorms on a fixed Fourier box.
Each seminorm takes the infimum of the half-twisted strip norm over the indicated
smooth denominator in that box. Thus the comparison extends to the separated
completions. The constants may depend on the box and on the earlier packet.
Reconstruction: take the fixed-box intersection before either closure. -/
theorem primaryDivisorialAbsolutePW_quotient_bounds (S : Finset V) (ω : PontryaginDual C₁)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hω : NormOneCharacterUnramifiedOutside ω S) (k : ℕ)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let W := primaryDivisorialAbsolutePWTests (F := F) S X
    let T := primaryDivisorialPlaces F S k
    let U := above(primaryDivisorialPrime (F := F) S k)
    let q := ((homogeneousAdelicThetaLinearMap F ω).domRestrict P₀).ker.mkQ
    let D := (divisorialThetaStage ω U).comap (q.domRestrict W)
    let D' := (divisorialThetaStage ω (primaryDivisorialPlaces F S (k+1))).comap
      ((divisorialThetaRepresentative ω T).domRestrict W)
    let N := primaryDivisorialStripNorm (1/2 - α) (1/2 + α) s ω
    let orbital := fun f : W ↦ ⨅ g : D, N (f - g.val).val
    let stage := fun f : W ↦ ⨅ g : D', N (adelePolarPrincipalValue T (f - g.val).val)
    ∃ C ≥ (0 : ℝ), ∀ f : W,
      orbital f ≤ C * stage f ∧ stage f ≤ C * orbital f := by
  intro W T U q D D' N orbital stage
  have hD : D' = D := by
    apply Submodule.ext
    intro f
    change divisorialThetaRepresentative ω T f.val ∈
      divisorialThetaStage ω (primaryDivisorialPlaces F S (k+1)) ↔
      q f.val ∈ divisorialThetaStage ω U
    dsimp only [T, U, q, Submodule.mkQ_apply]
    exact divisorialThetaRepresentative_mem_next_iff S ω k f.val
  obtain ⟨C, hC, he⟩ := primaryDivisorialAbsolutePW_principalValue_bounds S T hPic ω hω hX hα hs
  refine ⟨C, hC, fun f ↦ ?_⟩
  dsimp only [orbital, stage]
  rw [hD]
  have hpv (v : ↥P₀) : adelePolarPrincipalValue T v =
      ⟨adelePrincipalValue F T v.val, adelePrincipalValue_mem_polarSubspace T v⟩ := rfl
  have hcost (g : D) :
      N (f - g.val).val ≤ C * N (adelePolarPrincipalValue T (f - g.val).val) ∧
      N (adelePolarPrincipalValue T (f - g.val).val) ≤ C * N (f - g.val).val := by
    simpa only [N, sub_eq_add_neg, hpv] using he (f - g.val).val (f - g.val).property
  exact ⟨primaryPW_quotient_cost (fun _ ↦ Real.sqrt_nonneg _) hC (fun g ↦ (hcost g).1),
    primaryPW_quotient_cost (fun _ ↦ Real.sqrt_nonneg _) hC (fun g ↦ (hcost g).2)⟩

/-- The strip quotient seminorm is bounded away from zero when a representative
is outside the norm closure of the denominator. -/
private theorem primaryPW_quotient_pos_of_nonmem {E H Q : Type*} [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup E] [Module ℂ E] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (j : E →ₗ[ℂ] H) (W : Submodule ℂ E) (q : E →ₗ[ℂ] Q) (D : Submodule ℂ Q) (f : W)
    (hf : j f.val ∉ ((W ⊓ D.comap q).map j).topologicalClosure) :
    0 < ⨅ g : D.comap (q.domRestrict W), ‖j (f - g.val).val‖ := by
  change j f.val ∉ closure (((W ⊓ D.comap q).map j : Submodule ℂ H) : Set H) at hf
  rw [Metric.mem_closure_iff] at hf
  push Not at hf
  obtain ⟨δ, hδ, h⟩ := hf
  apply hδ.trans_le (le_ciInf _)
  intro g
  have hg : j g.val.val ∈ (W ⊓ D.comap q).map j :=
    ⟨g.val.val, ⟨g.val.property, g.property⟩, rfl⟩
  simpa only [dist_eq_norm, Submodule.coe_sub, map_sub] using h (j g.val.val) hg

/-- Paper: (11.3.1.3), p. 494. A single polar representative, independent of
strip and degree, has strictly positive quotient seminorm in the kth successive
stage at every sufficiently large finite Fourier bound.
Reconstruction: take the fixed Fourier box on the input before applying the
earlier principal values, then intersect the image with the next smooth stage
before the strip-norm closure. -/
def PrimaryDivisorialAbsolutePWStageSeparated (S : Finset V) (k : ℕ) (ω : PontryaginDual C₁) : Prop :=
  ∃ X₀ > (0 : ℝ), ∃ f : primaryDivisorialAbsolutePWTests (F := F) S X₀,
    ∀ α s : ℝ, 0 ≤ α → 0 ≤ s → ∀ X ≥ X₀,
      let W := primaryDivisorialAbsolutePWTests (F := F) S X
      let T := primaryDivisorialPlaces F S k
      let D := (divisorialThetaStage ω (primaryDivisorialPlaces F S (k+1))).comap
        ((divisorialThetaRepresentative ω T).domRestrict W)
      f.val ∈ W ∧ 0 < ⨅ g : D, primaryDivisorialStripNorm (1/2 - α) (1/2 + α) s ω
        (adelePolarPrincipalValue T (f.val - g.val.val))

/-- Paper: (11.3.1.3), p. 494. Separation for the single new prime packet
survives all preceding principal values in each fixed-box successive quotient. -/
theorem primaryDivisorialAbsolutePW_stage_noncollapse_of_separated (S : Finset V) (k : ℕ)
    (ω : PontryaginDual C₁) (hω : NormOneCharacterUnramifiedOutside ω S)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (h : PrimaryDivisorialAbsolutePWSeparated S above(primaryDivisorialPrime (F := F) S k) ω) :
    PrimaryDivisorialAbsolutePWStageSeparated S k ω := by
  obtain ⟨X₀, hX₀, f, hf⟩ := h
  refine ⟨X₀, hX₀, f, fun α s hα hs X hX ↦ ?_⟩
  let W := primaryDivisorialAbsolutePWTests (F := F) S X
  let q := ((homogeneousAdelicThetaLinearMap F ω).domRestrict P₀).ker.mkQ
  let U := above(primaryDivisorialPrime (F := F) S k)
  let D := (divisorialThetaStage ω U).comap (q.domRestrict W)
  obtain ⟨j, hj, hf'⟩ := hf α s hα hs
  obtain ⟨hW, hnon⟩ := hf' X hX
  let x : W := ⟨f.val, hW⟩
  have hpos : 0 < ⨅ g : D, ‖j (x - g.val).val‖ := by
    with_reducible_and_instances
      exact primaryPW_quotient_pos_of_nonmem (E := ↥P₀)
        (H := CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s)
        (Q := ↥P₀ ⧸ ((homogeneousAdelicThetaLinearMap F ω).domRestrict P₀).ker)
        j W q (divisorialThetaStage ω U) x hnon
  let r := fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)
  have hnorm (g : P₀) : ‖j g‖ = primaryDivisorialStripNorm (1/2 - α) (1/2 + α) s ω g := by
    have hz := (globalThetaSobolev_norm_aux μ𝔽 r (fun t ↦ NNReal.coe_pos.mpr (Units.zero_lt _))
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable
      (1/2) (-α) α s (homogeneousAdelicTheta ω g.val) (j g) (hj g)).2
    simpa only [primaryDivisorialStripNorm, logIdeleClassNorm, r, sub_eq_add_neg] using hz
  simp only [hnorm] at hpos
  obtain ⟨C, hC, hcomp⟩ := primaryDivisorialAbsolutePW_quotient_bounds S ω hPic hω k
    (hX₀.trans_le hX) hα hs
  refine ⟨hW, ?_⟩
  have ho := (hcomp x).1
  simp only [Submodule.coe_sub, x] at hpos ho
  with_reducible_and_instances
    exact pos_of_mul_pos_right (lt_of_lt_of_le hpos ho) hC

end

/-! ### Nonvanishing of every successive quotient -/

section

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "ωOf(" χ ")" => (χ : PontryaginDual C𝔽).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "resChar(" v ")" => Rat.HeightOneSpectrum.natGenerator ((v).under (𝓞 ℚ))
private theorem primaryDivisorialAbsolutePW_new_disjoint (S : Finset V) (k : ℕ) :
    Disjoint S (finite_nuclearityPlacesAbove (F := F) (primaryDivisorialPrime S k)).toFinset := by
  classical
  let p := primaryDivisorialPrime S k
  let q := Rat.HeightOneSpectrum.natGenerator p
  let N := S.image (fun v ↦ resChar(v))
  have hn : (Set.ofPred fun n : ℕ ↦ n.Prime ∧ n ∉ N).Infinite :=
    Nat.infinite_setOfPred_prime.sdiff N.finite_toSet
  have hqN : q ∉ N := by
    have hw := (Nat.nth_mem_of_infinite hn k).2
    have hq : q = Nat.nth (fun n : ℕ ↦ n.Prime ∧ n ∉ N) k :=
      congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply
        ⟨_, primaryDivisorialPrime_isPrime S k⟩)
    rwa [hq]
  refine Finset.disjoint_left.mpr fun v hv hv' ↦ ?_
  apply hqN
  have he : v.under (𝓞 ℚ) = p := (finite_nuclearityPlacesAbove p).mem_toFinset.mp hv'
  exact Finset.mem_image.mpr ⟨v, hv, congrArg Rat.HeightOneSpectrum.natGenerator he⟩

private theorem primaryDivisorialAbsolutePW_primePlace (p : Vℚ) :
    ∃ v ∈ (finite_nuclearityPlacesAbove (F := F) p).toFinset,
      ((Rat.HeightOneSpectrum.natGenerator p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  classical
  let q := Rat.HeightOneSpectrum.natGenerator p
  let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
  have := p.isMaximal
  obtain ⟨P, hP, hOver⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) p.asIdeal
  let v : V := ⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩
  have hv : v ∈ T := (finite_nuclearityPlacesAbove p).mem_toFinset.mpr
    (HeightOneSpectrum.ext hOver.over.symm)
  have hqmem : (q : 𝓞 ℚ) ∈ p.asIdeal := by
    let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
    apply (Ideal.apply_mem_of_equiv_iff (f := e)).mp
    rw [map_natCast]
    exact (Rat.HeightOneSpectrum.natGenerator_dvd_iff p).mp (dvd_refl q)
  have hqP : (q : 𝓞 F) ∈ v.asIdeal := by
    rw [hOver.over] at hqmem
    change algebraMap (𝓞 ℚ) (𝓞 F) (q : 𝓞 ℚ) ∈ P at hqmem
    simpa only [map_natCast] using hqmem
  exact ⟨v, hv, hqP⟩

private theorem primaryDivisorialAbsolutePW_new_uncut_lt (S : Finset V) (k : ℕ) (χ : PontryaginDual C𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (d : ℝ) (hd : 2 * (Module.finrank ℚ F : ℝ) ≤ d) :
    sLocalUncutCarving d (ωOf(χ)) (finite_nuclearityPlacesAbove (F := F) (primaryDivisorialPrime S k)).toFinset <
      sLocalUncutCarving d (ωOf(χ)) ∅ := by
  classical
  let p := primaryDivisorialPrime S k
  let q := Rat.HeightOneSpectrum.natGenerator p
  let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
  have hp : q.Prime := Rat.HeightOneSpectrum.prime_natGenerator p
  have hdis : Disjoint S T := primaryDivisorialAbsolutePW_new_disjoint S k
  obtain ⟨v, hv, hqP⟩ := primaryDivisorialAbsolutePW_primePlace (F := F) p
  let i : SLocalCarvingIndex (F := F) S := ⟨∅, Finset.disjoint_empty_right S⟩
  let j : SLocalCarvingIndex (F := F) S := ⟨T, hdis⟩
  have hij : i < j := Finset.empty_ssubset.mpr ⟨v, hv⟩
  have hnew : ∃ n : ℕ, n.Prime ∧ (∀ w ∈ i.val, (n : 𝓞 F) ∉ w.asIdeal) ∧
      ∃ w ∈ j.val, (n : 𝓞 F) ∈ w.asIdeal := ⟨q, hp, fun w hw ↦ (Finset.notMem_empty w hw).elim,
        v, hv, hqP⟩
  have ht := sLocalUncutCarving_lt (F := F) (S := S) χ hχ hPic d hd i j hij hnew
  simp only [i, j] at ht
  with_reducible exact ht

/-- Paper: (11.3.1.3), p. 494. At each successive prime packet, a single polar test has
strictly positive quotient seminorm in every half-twisted symmetric strip, at every
nonnegative degree, and in every sufficiently large finite Fourier box. -/
theorem primaryDivisorialAbsolutePW_stage_noncollapse (S : Finset V) (k : ℕ) (χ : PontryaginDual C𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) :
    PrimaryDivisorialAbsolutePWStageSeparated S k (ωOf(χ)) := by
  let d := 2 * (Module.finrank ℚ F : ℝ)
  have hd : 0 ≤ d := mul_nonneg zero_le_two (Nat.cast_nonneg _)
  have hω : NormOneCharacterUnramifiedOutside (ωOf(χ)) S := by
    refine ⟨⟨_, hχ⟩, fun g ↦ ?_⟩
    change (χ g.val : ℂ) * _ ^ (0 : ℂ) = (χ g.val : ℂ)
    simp
  apply primaryDivisorialAbsolutePW_stage_noncollapse_of_separated S k _ hω hPic
  exact primaryDivisorialAbsolutePW_noncollapse (ωOf(χ)) hω hPic hd
    (primaryDivisorialAbsolutePW_new_uncut_lt S k χ hχ hPic d le_rfl)

end

end RiemannMasullo
