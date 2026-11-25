import research.StripRationalChart
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Data.Nat.Choose.Bounds

/-!
# A conditional polynomial bound for the rational finite Gram coordinates

The even exponential moment bounds the physical jet norm on the inner half
of the width-one strip. Its factorial cancels that in the physical witness.
The resulting estimate is uniform in the finite block, even when that block
contains other angular characters.
-/

noncomputable section
open MeasureTheory NumberField Set RiemannMasullo
open scoped NumberField.AdeleRing Classical
open MasulloResearch.StripJets

namespace MasulloResearch.StripRadial

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁" => (ideleClassNorm ℚ).ker
local notation "site(" j ")" => (((j).val.2.1 : ℝ) : ℂ) + ((j).val.2.2.1 : ℂ) * Complex.I
local notation "point(" j ")" => site(j) + 1/2
local notation "jet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2

private theorem abs_exp_moment (k : ℕ) :
    ∫ x : ℝ, |x| ^ (2*k) * Real.exp (-|x|) = 2 * (2*k).factorial := by
  rw [integral_comp_abs (f := fun x : ℝ ↦ x^(2*k) * Real.exp (-x))]
  congr 1
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (↑(2*k) : ℝ) + 1)
    (r := 1) (by positivity) (by norm_num)
  simpa only [add_sub_cancel_right, Real.rpow_natCast, one_mul, div_one, Real.one_rpow,
    Real.Gamma_nat_eq_factorial] using h

/-- The squared radial moment at an interior offset is bounded by the
even exponential moment, uniformly in the ordinate and Sobolev exponent. -/
private theorem inner_strip_moment_le {s b : ℝ} (hs : 0 ≤ s) (hb : |b| ≤ 1/2) (k : ℕ) :
    (∫ x : ℝ, Real.exp (2*b*x - 2*1*|x|) * x ^ (2*k) * ((1+x^2)^(s/2))⁻¹) ≤
      2 * ((2:ℝ)^k * k.factorial)^2 := by
  have hi : Integrable (fun x : ℝ ↦ |x|^(2*k) * Real.exp (-|x|)) := by
    by_contra h
    have hz := integral_undef h
    rw [abs_exp_moment] at hz
    exact (ne_of_gt (by positivity : (0:ℝ) < 2 * (2*k).factorial)) hz
  have hbin := Nat.choose_le_two_pow (k+k) k
  have hn : (2*k).factorial ≤ (2^k * k.factorial)^2 := by
    rw [two_mul, ← Nat.add_choose_mul_factorial_mul_factorial]
    calc (k+k).choose k * k.factorial * k.factorial ≤
          2^(k+k) * k.factorial * k.factorial := by gcongr
         _ = _ := by rw [pow_add]; ring
  calc
    _ ≤ ∫ x : ℝ, |x|^(2*k) * Real.exp (-|x|) := by
      refine integral_mono_of_nonneg ?_ hi ?_
      · exact .of_forall fun x ↦ mul_nonneg
          (mul_nonneg (Real.exp_pos _).le ((even_two_mul k).pow_nonneg x))
          (inv_nonneg.mpr (Real.rpow_pos_of_pos (by nlinarith [sq_nonneg x] : 0 < 1+x^2) _).le)
      · refine .of_forall fun x ↦ ?_
        have hx : b*x ≤ (1/2)*|x| := (le_abs_self _).trans <| (abs_mul b x).le.trans
          (mul_le_mul_of_nonneg_right hb (abs_nonneg x))
        have he := Real.exp_le_exp.mpr (show 2*b*x - 2*1*|x| ≤ -|x| by linarith)
        have hw : ((1+x^2)^(s/2))⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀
          (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith))
        dsimp only
        rw [mul_comm (|x| ^ (2*k)), (even_two_mul k).pow_abs]
        exact (mul_le_mul_of_nonneg_left hw
          (mul_nonneg (Real.exp_pos _).le ((even_two_mul k).pow_nonneg x))).trans
          (by rw [mul_one]; exact mul_le_mul_of_nonneg_right he ((even_two_mul k).pow_nonneg x))
    _ = 2 * (2*k).factorial := abs_exp_moment k
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul_left 2 hn

/-- A fixed Haar constant times the factorial and a power of two bounds every jet
in the inner half of the width-one strip, uniformly in the Sobolev exponent. -/
theorem inner_strip_jet_norm_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (a s : ℝ)
      (hs : 0 ≤ s) (i : SpectralStripJetIndex χ a 1 s), |i.val.2.1| ≤ 1/2 →
      ‖(spectralStripJet_memLp χ (by norm_num : (0 : ℝ) ≤ 1) hs i).toLp (jet(χ, i))‖ ≤
        D * (2 ^ i.val.2.2.2 * i.val.2.2.2.factorial) := by
  let m := continuousIdeleClassNorm ℚ
  have hm : IsModulation m := ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  let ν := canonicalModulatedHaar m hm
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m hm).exists.choose_spec.1
  let c : ℝ := Measure.haarScalarFactor (ideleClassTamagawaMeasure ℚ) ν
  have hc : 0 < c := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure (ideleClassTamagawaMeasure ℚ) ν)
  refine ⟨Real.sqrt (2*c), Real.sqrt_pos.mpr (by positivity), fun χ a s hs i hb ↦ ?_⟩
  have he := spectralStripJet_norm_sq χ (by norm_num : (0 : ℝ) ≤ 1) hs i ν rfl
  have h := mul_le_mul_of_nonneg_left (inner_strip_moment_le hs hb i.val.2.2.2) hc.le
  have hsq := he.le.trans h
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  linarith

set_option maxHeartbeats 800000 in
/-- The normalized finite Gram coordinate is bounded by the product of the
physical jet norm and the norm of any physical cardinal witness. -/
private theorem gram_le_jet_mul_witness (χ : PontryaginDual C₁ → PontryaginDual Cℚ)
    (hχ : IsSpectralBasepointChoice χ) {s : ℝ} (hs : 0 ≤ s)
    (i : SpectralStripJetIndex χ (1/2) 1 s) (S : Finset (SpectralStripJetIndex χ (1/2) 1 s))
    (y : CompactIntervalSobolev (ideleClassTamagawaMeasure ℚ) (logIdeleClassNorm ℚ) (-1) 1 s) :
    let u := fun j : SpectralStripJetIndex χ (1/2) 1 s ↦
      (spectralStripJet_memLp χ (by norm_num : (0 : ℝ) ≤ 1) hs j).toLp (jet(χ, j))
    (∀ j, spectralSobolevPairing y (u j) = if j = i then 1 else 0) →
      ‖u i‖ * finiteGramCoordinate u i S ≤ ‖u i‖ * ‖y‖ := by
  intro u hy
  let m := continuousIdeleClassNorm ℚ
  have hm : IsModulation m := ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  let T := (modulatedIntervalSobolev_dual m hm (ideleClassTamagawaMeasure ℚ) (-1) 1 s
    (by norm_num) hs).exists.choose
  let L := ((ContinuousLinearMap.apply ℂ ℂ) y).comp T.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hL (j) : L (u j) = if j = i then 1 else 0 := by
    change (T.symm (u j)) y = _
    exact ((spectralSobolevPairing_dual (by norm_num : (-1:ℝ) ≤ 1) hs (T.symm (u j)) y).2.trans
      (congrArg (spectralSobolevPairing y) (T.apply_symm_apply (u j)))).trans (hy j)
  have hnorm : ‖L‖ ≤ ‖y‖ := L.opNorm_le_bound (norm_nonneg _) fun v ↦ by
    change ‖(T.symm v) y‖ ≤ ‖y‖ * ‖v‖
    calc _ ≤ ‖T.symm v‖ * ‖y‖ := (T.symm v).le_opNorm y
         _ = _ := by rw [T.symm.norm_map, mul_comm]
  have hInd := spectralStripJet_toLp_linearIndependent χ hχ (1/2) (by norm_num : (0:ℝ) ≤ 1) hs
  have hg := norm_mul_finiteGramCoordinate_le_of_pairings (u := u) i S
    (hInd.comp _ Subtype.val_injective) L one_ne_zero (fun _ ↦ (hL i).trans (ite_eq_left rfl))
    (fun j _ hj ↦ (hL j).trans (ite_eq_right hj))
  exact (by simpa only [norm_one, div_one] using hg : _ ≤ ‖u i‖ * ‖L‖).trans
    (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))

/-- Under the polynomial lower bound for the first nonzero ordinary zeta
coefficient, the normalized inverse Gram diagonal grows polynomially in
the ordinate, uniformly over finite blocks of the full ambient family. The
selected jet lies on the rational trivial component and has height at least two. -/
theorem rational_finiteGram_polynomial_high {b : ℝ} (hb : 0 < b) (A : ℕ)
    (hζ : ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b / (2 + |w.im|) ^ A ≤ ‖taylorCoeff riemannZeta w n‖)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : PontryaginDual C₁ → PontryaginDual Cℚ),
      IsSpectralBasepointChoice χ → χ 1 = 1 → ∀ i : SpectralStripJetIndex χ (1/2) 1 s,
      i.val.1 = 1 → 2 ≤ |i.val.2.2.1| → ∀ S : Finset (SpectralStripJetIndex χ (1/2) 1 s),
      let u := fun j : SpectralStripJetIndex χ (1/2) 1 s ↦
        (spectralStripJet_memLp χ (by norm_num : (0 : ℝ) ≤ 1) hs j).toLp (jet(χ, j))
      ‖u i‖ * finiteGramCoordinate u i S ≤ C * (10 + |i.val.2.2.1|)^(6*A+30) := by
  obtain ⟨D, hD, hjet⟩ := inner_strip_jet_norm_bound
  obtain ⟨K, hK, hwit⟩ := exists_rational_physical_zeta_witnesses hb A hζ
  obtain ⟨R, hR, hrad⟩ := zeta_radius_of_polynomial_coefficients hb A hζ
  let μ := (normOneIdeleClassTamagawaMeasure ℚ).real univ
  let : CompactSpace C₁ := (ideleClassGroup_finiteness ℚ).2.1
  let : (normOneIdeleClassTamagawaMeasure ℚ).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  have hμ : 0 < μ := measureReal_univ_pos
  let I := ∫ t, sobolevKernel s t
  have hI : 0 ≤ I := integral_nonneg fun x ↦ by unfold sobolevKernel; positivity
  let B := Real.sqrt (I / μ) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨D*R*K*B, by positivity, fun χ hχ hχ1 i hi ht S ↦ ?_⟩
  intro u
  let H := 10 + |i.val.2.2.1|
  let k := i.val.2.2.2
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨hstrip, hz, m, hm, hk⟩ := rational_strip_jet_order hχ1 i hi
  have him : (point(i)).im = i.val.2.2.1 := by simp
  obtain ⟨r, hr, hr2, hcost, -⟩ := hrad (point(i)) ⟨hstrip.1.le, hstrip.2.le⟩
    (by rwa [him]) hz m hm
  rw [him] at hcost
  have htwo : (2 : ℝ)^k ≤ R*H^(A+5) := calc
    (2 : ℝ)^k ≤ 2^m := pow_le_pow_right₀ (by norm_num) hk.le
    _ ≤ (r^m)⁻¹ := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by norm_num) ((le_inv_comm₀ (by norm_num) hr).2 (by linarith)) _
    _ = _ := hcost
  have hbnd : |i.val.2.1| ≤ 1/2 := by
    simp at hstrip
    rw [abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
  have hu : ‖u i‖ ≤ D*(2^k * k.factorial) := hjet χ (1/2) s hs i hbnd
  obtain ⟨y, hy, hyn, -⟩ := hwit χ hχ hχ1 s hs i hi ht
  let E := K * H^(5*A+25) / (2 * k.factorial)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hy2 : ‖y‖^2 ≤ E^2 * (I / μ) := by
    rw [← mul_div_assoc, le_div_iff₀ hμ, mul_comm (‖y‖^2)]
    exact hyn
  have hyroot : ‖y‖ ≤ E * Real.sqrt (I/μ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hE (Real.sqrt_nonneg _))).mp
    rwa [mul_pow, Real.sq_sqrt (div_nonneg hI hμ.le)]
  have hy' : ‖y‖ ≤ K * H^(5*A+25) / k.factorial * B := by
    refine hyroot.trans (mul_le_mul ?_ (by dsimp [B]; linarith) (Real.sqrt_nonneg _) (by positivity))
    dsimp [E]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith [Nat.cast_nonneg k.factorial (α := ℝ)])
  calc ‖u i‖ * finiteGramCoordinate u i S ≤ ‖u i‖ * ‖y‖ :=
        gram_le_jet_mul_witness χ hχ hs i S y hy
       _ ≤ (D * (2^k * k.factorial)) * (K * H^(5*A+25) / k.factorial * B) :=
        mul_le_mul hu hy' (norm_nonneg _) (by positivity)
       _ = (D * K * B) * 2^k * H^(5*A+25) := by
        field_simp
       _ ≤ (D*K*B) * (R*H^(A+5)) * H^(5*A+25) := by gcongr
       _ = _ := by
        change _ = _ * H^_
        rw [show 6*A+30 = (A+5)+(5*A+25) by omega, pow_add]
        ring

/-- Only finitely many retained indices on the rational trivial component lie
below height two. A compact divisor bounds both the sites and the jet orders. -/
private theorem rational_low_jets_finite {s : ℝ}
    {χ : PontryaginDual C₁ → PontryaginDual Cℚ} (hχ1 : χ 1 = 1) :
    {i : SpectralStripJetIndex χ (1/2) 1 s | i.val.1 = 1 ∧ |i.val.2.2.1| < 2}.Finite := by
  let T := {i : SpectralStripJetIndex χ (1/2) 1 s | i.val.1 = 1 ∧ |i.val.2.2.1| < 2}
  let D := Metric.closedBall (0 : ℂ) 4
  let d := MeromorphicOn.divisor riemannZeta D
  have hmer : MeromorphicOn riemannZeta D := by
    have h : MeromorphicOn riemannZeta univ := by
      simpa only [DirichletCharacter.LFunction_modOne_eq] using
        meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
    exact fun w _ ↦ h w (mem_univ _)
  have hdata (j : T) : let i := j.val; d (point(i)) ≠ 0 ∧ i.val.2.2.2 < (d (point(i))).toNat := by
    intro i
    obtain ⟨hstrip, -, n, hn, hk⟩ := rational_strip_jet_order hχ1 i j.property.1
    have him : |(point(i)).im| < 2 := by simpa using j.property.2
    have hD : point(i) ∈ D := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h := Complex.norm_le_abs_re_add_abs_im (point(i))
      rw [abs_of_pos hstrip.1] at h
      linarith [hstrip.2]
    have h1 : point(i) ≠ 1 := fun e ↦ hstrip.2.ne ((congrArg Complex.re e).trans Complex.one_re)
    have hd : d (point(i)) = n := by
      rw [show d (point(i)) = _ from hmer.divisor_apply hD,
        (analyticOn_riemannZeta _ h1).meromorphicOrderAt_eq, hn, ENat.map_natCast]
      simp
    rw [hd]
    exact ⟨by exact_mod_cast (Nat.ne_of_gt (Nat.zero_le _ |>.trans_lt hk)), by simpa using hk⟩
  let : Finite (Function.support d) := (d.finiteSupport (isCompact_closedBall _ _)).to_subtype
  let enc (j : T) : (z : Function.support d) × Fin (d z.val).toNat :=
    ⟨⟨point(j.val), (hdata j).1⟩, ⟨j.val.val.2.2.2, (hdata j).2⟩⟩
  change Finite T
  apply Finite.of_injective enc
  intro i j he
  have hz := congrArg (fun v : (z : Function.support d) × Fin (d z.val).toNat ↦ v.1.val) he
  have hk := congrArg (fun v : (z : Function.support d) × Fin (d z.val).toNat ↦ v.2.val) he
  change point(i.val) = point(j.val) at hz
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (i.property.1.trans j.property.1.symm) (Prod.ext
    (by simpa using congrArg Complex.re hz) (Prod.ext (by simpa using congrArg Complex.im hz) hk))

/-- For a fixed basepoint choice, the conditional polynomial Gram bound covers
every ordinate. The constant absorbs the finitely many low jets. -/
theorem rational_finiteGram_polynomial {b : ℝ} (hb : 0 < b) (A : ℕ)
    (hζ : ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b / (2 + |w.im|) ^ A ≤ ‖taylorCoeff riemannZeta w n‖)
    {s : ℝ} (hs : 0 ≤ s) (χ : PontryaginDual C₁ → PontryaginDual Cℚ)
    (hχ : IsSpectralBasepointChoice χ) (hχ1 : χ 1 = 1) :
    let u := fun j : SpectralStripJetIndex χ (1/2) 1 s ↦
      (spectralStripJet_memLp χ (by norm_num : (0 : ℝ) ≤ 1) hs j).toLp (jet(χ, j))
    ∃ C : ℝ, 0 < C ∧ ∀ i : SpectralStripJetIndex χ (1/2) 1 s, i.val.1 = 1 →
      ∀ S : Finset (SpectralStripJetIndex χ (1/2) 1 s),
        ‖u i‖ * finiteGramCoordinate u i S ≤ C * (10 + |i.val.2.2.1|)^(6*A+30) := by
  intro u
  obtain ⟨C, hC, hhigh⟩ := rational_finiteGram_polynomial_high hb A hζ hs
  choose y hy using fun i : SpectralStripJetIndex χ (1/2) 1 s ↦
    spectralStripJet_singleInterpolant χ hχ (by norm_num : (0:ℝ) ≤ 1) hs i
  let T := {i : SpectralStripJetIndex χ (1/2) 1 s | i.val.1 = 1 ∧ |i.val.2.2.1| < 2}
  obtain ⟨B, hB⟩ := ((rational_low_jets_finite hχ1 (s := s)).image
    (fun i ↦ ‖u i‖ * ‖y i‖)).bddAbove
  refine ⟨max C B, hC.trans_le (le_max_left ..), fun i hi S ↦ ?_⟩
  have hpow : 1 ≤ (10 + |i.val.2.2.1|)^(6*A+30) :=
    one_le_pow₀ (by linarith [abs_nonneg i.val.2.2.1])
  by_cases ht : 2 ≤ |i.val.2.2.1|
  · exact (hhigh χ hχ hχ1 i hi ht S).trans (mul_le_mul_of_nonneg_right (le_max_left ..)
      (zero_le_one.trans hpow))
  · have hlo := hB (mem_image_of_mem (fun j ↦ ‖u j‖ * ‖y j‖)
        (show i ∈ T from ⟨hi, lt_of_not_ge ht⟩))
    exact (gram_le_jet_mul_witness χ hχ hs i S _ (hy i)).trans
      (hlo.trans ((le_max_right ..).trans (le_mul_of_one_le_right
        (hC.le.trans (le_max_left ..)) hpow)))

end MasulloResearch.StripRadial
