module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch09_HardySobolev.Sec2

/-! # Interior Mellin evaluations in the reciprocal strip space -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set RiemannMasullo
open scoped Classical NumberField.AdeleRing InnerProductSpace ComplexConjugate

namespace MasulloResearch.StripRadial

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} (x : X → ℝ)

/-- The exponential jet in logarithmic coordinates. -/
def expJet (w : ℂ) (k : ℕ) (g : X) : ℂ := Complex.exp (w * x g) * (x g : ℂ)^k

/-- The physical Hilbert pairing with the zonal exponential jet is holomorphic
throughout the interior. All derivatives are the corresponding jet pairings. -/
theorem inner_expJet_mellin (hx : Measurable x)
    (hLp : ∀ w : ℂ, |w.re| < 1 → ∀ k, MemLp (expJet x w k) 2 μ)
    (q : Lp ℂ 2 μ) :
    let G (w : ℂ) := ∫ g, conj (q g) * Complex.exp (w * x g) ∂μ
    ∀ (w : ℂ) (hw : |w.re| < 1) (k : ℕ), AnalyticAt ℂ G w ∧
      iteratedDeriv k G w = ⟪q, (hLp w hw k).toLp (expJet x w k)⟫_ℂ := by
  intro G w hw k
  have hm (v : ℂ) (hv : |v.re| < 1) (n : ℕ) :
      Integrable (fun g ↦ conj (q g) * (x g : ℂ)^n * Complex.exp (v*x g)) μ := by
    have hi := L2.integrable_inner (𝕜 := ℂ) q ((hLp v hv n).toLp _)
    refine hi.congr ?_
    filter_upwards [(hLp v hv n).coeFn_toLp] with g hg
    rw [hg,RCLike.inner_apply']
    dsimp [expJet]; ring
  obtain ⟨ha,_,hd⟩ := iteratedDeriv_exp_moment_of_measurable (h := fun g ↦ conj (q g)) hx
    (α := -1) (β := 1) (fun σ hσ n ↦ hm (σ : ℂ) (by simpa [abs_lt] using hσ) n) k (abs_lt.mp hw)
  refine ⟨ha, hd.trans ?_⟩
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hLp w hw k).coeFn_toLp] with g hg
  rw [hg,RCLike.inner_apply']
  dsimp [expJet]; ring

/-- In the ordinary zeta coordinate the shift by one half places every
quarter-disk about the critical strip inside the three-quarter strip. -/
theorem exists_translated_mellin_cardinal_data (hx : Measurable x)
    (hLp : ∀ w : ℂ, |w.re| < 1 → ∀ k, MemLp (expJet x w k) 2 μ)
    (q : Lp ℂ 2 μ) {D : ℝ} (hupper : ∀ (w : ℂ) (hw : |w.re| ≤ 3/4),
      ‖(hLp w (hw.trans_lt (by norm_num)) 0).toLp _‖ ≤ D)
    (ρ : ℂ) (hρ : ρ.re ∈ Ioo (0:ℝ) 1) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.closedBall ρ (1/4)) ∧
      (∀ z ∈ Metric.closedBall ρ (1/4), ‖g z‖ ≤ D*‖q‖) ∧
      ∀ (v : ℂ) (hv : |v.re| < 1) (k : ℕ), iteratedDeriv k g (v+1/2) =
        ⟪q,(hLp v hv k).toLp _⟫_ℂ := by
  let G (v : ℂ) := ∫ y, conj (q y) * Complex.exp (v * x y) ∂μ
  let g (z : ℂ) := G (z-1/2)
  have hder := inner_expJet_mellin x hx hLp q
  have hbnd (z : ℂ) (hz : z ∈ Metric.closedBall ρ (1/4)) : |(z-1/2).re| ≤ 3/4 := by
    have h₂ := (Complex.abs_re_le_norm (z-ρ)).trans (mem_closedBall_iff_norm.mp hz)
    rw [Complex.sub_re] at h₂
    obtain ⟨hl,hr⟩ := abs_le.mp h₂
    simp only [Complex.sub_re,Complex.div_ofNat_re,Complex.one_re]
    exact abs_le.mpr ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  refine ⟨g,fun z hz ↦ ((hder _ ((hbnd z hz).trans_lt (by norm_num)) 0).1).comp (f := fun v : ℂ ↦ v - 1/2) (x := z)
    (show AnalyticAt ℂ (fun v : ℂ ↦ v - 1/2) z by fun_prop),?_,?_⟩
  · intro z hz
    have hb := hbnd z hz
    have he := (hder _ (hb.trans_lt (by norm_num)) 0).2
    change ‖G (z-1/2)‖ ≤ _
    rw [iteratedDeriv_zero] at he
    rw [show G (z-1/2) = _ from he]
    exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
      ((mul_le_mul_of_nonneg_left (hupper _ hb) (norm_nonneg _)).trans_eq (mul_comm ..))
  · intro v hv k
    change iteratedDeriv _ (fun z : ℂ ↦ G (z-1/2)) (v+1/2) = _
    rw [iteratedDeriv_comp_sub_const]
    simpa only [add_sub_cancel_right] using (hder _ hv k).2

/-- On the three-quarter strip, the two real endpoint exponentials dominate
every complex evaluation. The upper bound is uniform in the ordinate. -/
theorem expJet_uniform_norm (hLp : ∀ w : ℂ, |w.re| < 1 → ∀ k, MemLp (expJet x w k) 2 μ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (w : ℂ) (hw : |w.re| ≤ 3/4),
      ‖(hLp w (hw.trans_lt (by norm_num)) 0).toLp _‖ ≤ D := by
  let b : ℝ := 3/4
  have hp : |((b : ℂ)).re| < 1 := by norm_num [b]
  have hn : |((-b : ℂ)).re| < 1 := by norm_num [b]
  let p := (hLp b hp 0).toLp _
  let n := (hLp (-b) hn 0).toLp _
  refine ⟨1+‖p‖+‖n‖, by positivity, fun w hw ↦ ?_⟩
  let v := (hLp w (hw.trans_lt (by norm_num)) 0).toLp _
  have h : ‖v‖ ≤ ‖p+n‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hLp w (hw.trans_lt (by norm_num)) 0).coeFn_toLp,
      (hLp b hp 0).coeFn_toLp,(hLp (-b) hn 0).coeFn_toLp,Lp.coeFn_add p n] with g hv hp' hn' hsum
    change ‖v g‖ ≤ ‖(p+n) g‖
    rw [hsum]
    change p g = _ at hp'
    change n g = _ at hn'
    simp only [Pi.add_apply]
    rw [hp',hn',show v g = _ from hv]
    simp only [expJet,pow_zero,mul_one,← Complex.ofReal_mul,← Complex.ofReal_neg,
      ← Complex.ofReal_exp,← Complex.ofReal_add,Complex.norm_exp,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    rcases le_total 0 (x g) with ht | ht
    · apply le_add_of_le_of_nonneg _ (Real.exp_pos _).le
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (abs_le.mp hw).2 ht)
    · apply le_add_of_nonneg_of_le (Real.exp_pos _).le
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (abs_le.mp hw).1 ht)
  linarith [h, norm_add_le p n]

/-- A fixed positive function lies below every zeroth evaluation in the inner
strip. Its norm gives a lower bound independent of height and of the center. -/
theorem expJet_uniform_lower (hx : Measurable x) (hμ : μ ≠ 0)
    (hLp : ∀ w : ℂ, |w.re| < 1 → ∀ k, MemLp (expJet x w k) 2 μ) :
    ∃ d : ℝ, 0 < d ∧ ∀ (w : ℂ) (hw : |w.re| < 1), d ≤ ‖(hLp w hw 0).toLp _‖ := by
  let f (g : X) : ℝ := Real.exp (-|x g|)
  have hf : MemLp f 2 μ := by
    refine (hLp 0 (by norm_num) 0).of_le (by dsimp [f]; fun_prop) (.of_forall fun g ↦ ?_)
    simp [f, expJet, Real.norm_of_nonneg (Real.exp_pos _).le]
  let v := hf.toLp f
  have := ae_neBot.mpr hμ
  have hv : v ≠ 0 := by
    intro he
    obtain ⟨g,hg⟩ := (hf.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp he)).exists
    exact (Real.exp_pos _).ne' hg
  refine ⟨‖v‖,norm_pos_iff.mpr hv,fun w hw ↦ ?_⟩
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hf.coeFn_toLp,(hLp w hw 0).coeFn_toLp] with g hg h'
  change v g = _ at hg
  rw [hg,h']
  simp only [f,expJet,pow_zero,mul_one,Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hw.le (abs_nonneg (x g))
  rw [← abs_mul,one_mul] at h
  exact (abs_le.mp h).1

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "ℓ" => logIdeleClassNorm F
local notation "ν" s => intervalSobolevMeasure (ideleClassTamagawaMeasure F) ℓ (-1) 1 s true

/-- The exponential jets at every interior point belong to the physical dual
space, including the off-spectrum points used on the Jensen contour. -/
theorem interior_expJet_memLp {s : ℝ} (hs : 0 ≤ s) (w : ℂ) (hw : |w.re| < 1) (k : ℕ) :
    MemLp (expJet ℓ w k) 2 (ν s) := by
  let m := continuousIdeleClassNorm F
  have hm : IsModulation m := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let μ := canonicalModulatedHaar m hm
  let : μ.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m hm).exists.choose_spec.1
  have hlog := sobolev_log_preserving m hm (ideleGroup_quotient.{_,0} F).2.2.2.2.2.2.2.2.2.1
  have hint := hlog.integrable_comp_of_integrable (spectralStripJet_integrable (α := 1) (s := s)
    (k := k) (by norm_num) hs (Or.inl (abs_lt.mp hw)))
  have hμ : Integrable (fun g : C𝔽 ↦ Real.exp (2*w.re*ℓ g - 2*1*|ℓ g|) *
      (ℓ g)^(2*k) * ((1+(ℓ g)^2)^(s/2))⁻¹) (ideleClassTamagawaMeasure F) := by
    rw [Measure.isMulLeftInvariant_eq_smul (ideleClassTamagawaMeasure F) μ]
    exact hint.smul_measure_nnreal
  have he (g : C𝔽) : expJet ℓ w k g = spectralZeroJet (1 : PontryaginDual C𝔽) w.re w.im k g := by
    rw [stripProfile_jet, Complex.re_add_im]; simp [expJet]
  rw [funext he]
  apply (memLp_two_iff_integrable_sq_norm (spectralZeroJet_continuous _ _ _ _).aestronglyMeasurable).mpr
  apply (integrable_withDensity_iff (symmIntervalSobolevDensity_inv_continuous (by norm_num : (0:ℝ) ≤ 1) s).measurable.ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mpr
  refine hμ.congr (.of_forall fun g ↦ ?_)
  dsimp only
  rw [spectralZeroJet_norm_sq, ENNReal.toReal_ofReal (inv_nonneg.mpr (symmIntervalSobolevDensity_pos
    (by norm_num : (0:ℝ) ≤ 1) s (ℓ g)).le), stripJet_integrand_eq (by norm_num : (0:ℝ) ≤ 1)]

/-- The reciprocal strip weight is strictly positive on the idele class group. -/
theorem reciprocal_strip_measure_ne_zero (s : ℝ) : (ν s) ≠ 0 := by
  have hm := (symmIntervalSobolevDensity_inv_continuous (F := F) (by norm_num : (0:ℝ) ≤ 1) s).measurable.ennreal_ofReal
  intro he
  obtain ⟨g,hg⟩ := ((withDensity_eq_zero_iff hm.aemeasurable).mp he).exists
  exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (symmIntervalSobolevDensity_pos
    (by norm_num : (0:ℝ) ≤ 1) s (ℓ g)))).ne' hg

/-- The ordinary rational spectral jet has precisely the Mellin normalization
used by the reciprocal-space pairing. -/
theorem trivial_spectralZeroJet_eq_expJet (b t : ℝ) (k : ℕ) :
    spectralZeroJet (1 : PontryaginDual C𝔽) b t k =
      expJet ℓ ((b:ℂ) + t*Complex.I) k := by
  funext g
  rw [stripProfile_jet]
  simp [expJet]

end MasulloResearch.StripRadial
