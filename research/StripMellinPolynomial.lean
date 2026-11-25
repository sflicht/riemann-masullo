module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch12_TraceGeometric.Sec5
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete

/-!
# Polynomial bounds from homogeneous Mellin tests

The modulation and uniform boundedness proof below is adapted from the mlyle fork's
`research/I314PositiveCoordinates.lean`, lines 295–515, at
commit `5127c420c58c42dddacb86d87d941f88aea922e4` (Apache-2.0).
This extraction exposes the test lemma for a family indexed by both a site and a finite
Gram block. The analytic proof and its constants are unchanged.
-/

@[expose] public noncomputable section

open Function Set Filter MeasureTheory Topology IsDedekindDomain NumberField
open scoped NNReal ENNReal NumberField.AdeleRing
namespace RiemannMasullo
set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
open scoped ContDiff
namespace LineModulation
local notation "S" => SchwartzMap ℝ ℂ
private def phase (t x : ℝ) : ℂ := Complex.exp (((t : ℂ) * Complex.I) * x)
private theorem phase_smooth (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phase t) :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
private theorem phase_norm (t x : ℝ) : ‖phase t x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]
private theorem phase_iters (t : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (phase t) x = ((t : ℂ) * Complex.I)^n * phase t x := by
  induction n generalizing x with
  | zero => simp
  | succ n h =>
    rw [iteratedDeriv_succ, funext h]
    let c := (t : ℂ) * Complex.I
    have h1 : HasDerivAt (phase t) (c * phase t x) x := by
      have h := (((Complex.hasDerivAt_exp (c * (x : ℂ))).comp (x : ℂ)
        ((hasDerivAt_id (x : ℂ)).const_mul c)).comp_ofReal)
      change HasDerivAt (fun y : ℝ ↦ Complex.exp (c * (y : ℂ))) (c * Complex.exp (c * (x : ℂ))) x
      simpa [mul_comm] using h
    change deriv (fun y ↦ c^n * phase t y) x = c^(n+1) * phase t x
    rw [(h1.const_mul _).deriv, pow_succ]; ring
private def atom (b : S) (hc : HasCompactSupport (b : ℝ → ℂ)) (t : ℝ) : S :=
  (hc.mul_right (f' := phase (-t))).toSchwartzMap (b.smooth'.mul (phase_smooth (-t)))
private theorem atom_seminorm (b : S) (hc : HasCompactSupport (b : ℝ → ℂ)) (k n : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, (SchwartzMap.seminorm ℂ k n) (atom b hc t) ≤ C*(1+|t|)^n := by
  classical
  let B (i : ℕ) := (n.choose i : ℝ) * (SchwartzMap.seminorm ℂ k i) b
  have hB (i) : 0 ≤ B i := mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  refine ⟨∑ i ∈ Finset.range (n+1), B i, Finset.sum_nonneg (fun i _ ↦ hB i), fun t ↦ ?_⟩
  apply SchwartzMap.seminorm_le_bound ℂ _ _ _ (by positivity)
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖x‖^k * ‖iteratedDeriv n ((b : ℝ → ℂ) * phase (-t)) x‖ ≤ _
  rw [iteratedDeriv_mul (b.smooth n).contDiffAt ((phase_smooth (-t)).of_le (by simp)).contDiffAt]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity)).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [phase_iters, norm_mul, norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one,
    phase_norm, mul_one, Complex.norm_real, norm_neg, Complex.norm_natCast, Real.norm_eq_abs t]
  have hx := SchwartzMap.le_seminorm ℂ k i b x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hx
  have htp : |t|^(n-i) ≤ (1+|t|)^n :=
    (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |t| ≤ 1+|t|) _).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg _)) (Nat.sub_le _ _))
  calc
    _ = ((n.choose i : ℝ)*(‖x‖^k*‖iteratedDeriv i (b : ℝ → ℂ) x‖))*|t|^(n-i) := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hx (by positivity)) htp (by positivity) (hB i)
private theorem orbitBound (b : S) (hc : HasCompactSupport (b : ℝ → ℂ)) (q : Seminorm ℂ S)
    (hq : Continuous q) : ∃ C ≥ (0 : ℝ), ∃ k : ℕ, ∀ t : ℝ, q (atom b hc t) ≤ C*(1+|t|)^k := by
  classical
  let P := schwartzSeminormFamily ℂ ℝ ℂ
  obtain ⟨s,D,_,hD⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hq
  choose K hK hbound using atom_seminorm b hc
  let k := s.sup Prod.snd
  let C := ∑ i ∈ s, K i.1 i.2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ ↦ hK i.1 i.2)
  refine ⟨(D:ℝ)*C, by positivity, k, fun t ↦ ?_⟩
  refine (hD (atom b hc t)).trans ?_
  change (D:ℝ)*(s.sup P) (atom b hc t) ≤ _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ D.coe_nonneg
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro i hi
  exact (hbound i.1 i.2 t).trans (mul_le_mul (Finset.single_le_sum (f := fun j : ℕ × ℕ ↦ K j.1 j.2)
    (fun j _ ↦ hK j.1 j.2) hi)
    (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg _)) (Finset.le_sup hi)) (by positivity) hC)
private def cutBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
private def inletBump : ContDiffBump (0 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
private def bumpS (b : ContDiffBump (0 : ℝ)) : S :=
  (b.hasCompactSupport.comp_left (by simp : ((0:ℝ):ℂ) = 0)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)
private theorem bumpS_compact (b : ContDiffBump (0 : ℝ)) : HasCompactSupport (bumpS b : ℝ → ℂ) :=
  b.hasCompactSupport.comp_left (by simp : ((0:ℝ):ℂ) = 0)
variable (F) in
private def radScale : ℝ := ((normOneIdeleClassTamagawaMeasure F) univ).toReal
private theorem radScale_pos : 0 < radScale F := by
  let ν := normOneIdeleClassTamagawaMeasure F
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  exact ENNReal.toReal_pos (NeZero.ne (ν univ)) (measure_ne_top ν _)
private def tilt (b x : ℝ) : ℂ := (Real.exp (b*x):ℂ)
private theorem tilt_smooth (b : ℝ) : ContDiff ℝ (⊤:ℕ∞) (tilt b) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
private def stripEval (b t : ℝ) : S →L[ℂ] ℂ :=
  (SchwartzMap.integralCLM ℂ volume).comp (SchwartzMap.smulLeftCLM ℂ
    (fun x ↦ bumpS cutBump x * (tilt b x * phase t x)))
private theorem stripEval_eq (b t : ℝ) (f : S) : stripEval b t f =
    ∫ x : ℝ, bumpS cutBump x * f x * (tilt b x * phase t x) := by
  rw [stripEval,ContinuousLinearMap.comp_apply,SchwartzMap.integralCLM_apply]
  have hh : (fun x ↦ bumpS cutBump x * (tilt b x * phase t x)).HasTemperateGrowth :=
    ((bumpS_compact cutBump).mul_right).hasTemperateGrowth
      ((bumpS cutBump).smooth'.mul ((tilt_smooth b).mul (phase_smooth t)))
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  rw [SchwartzMap.smulLeftCLM_apply_apply hh, smul_eq_mul]; ring
private theorem stripEval_atom_lower {α b : ℝ} (hα : 0≤α) (hb : |b|≤α) (t : ℝ) :
    Real.exp (-α) * (∫ x : ℝ, inletBump x) ≤
      ‖stripEval b t (atom (bumpS inletBump) (bumpS_compact _) t)‖ := by
  let v (x : ℝ) := inletBump x * Real.exp (b*x)
  have he : stripEval b t (atom (bumpS inletBump) (bumpS_compact _) t) = ((∫ x : ℝ,v x : ℝ):ℂ) := by
    rw [stripEval_eq]
    refine Eq.trans ?_ (show (∫ x : ℝ, (v x:ℂ)) = _ from integral_ofReal)
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    change (cutBump x : ℂ) * ((inletBump x : ℂ) * phase (-t) x) * (tilt b x * phase t x) = _
    by_cases hx : inletBump x = 0
    · simp [v,hx]
    have hm := subset_tsupport _ (show x ∈ support inletBump from hx)
    rw [inletBump.tsupport_eq,Metric.mem_closedBall] at hm
    have cut : cutBump x = 1 := cutBump.one_of_mem_closedBall (hm.trans (by norm_num [cutBump,inletBump]))
    have hp : phase (-t) x * phase t x = 1 := by simp [phase,← Complex.exp_add]
    rw [cut,Complex.ofReal_one,one_mul]
    change _ = ((inletBump x * Real.exp (b*x):ℝ):ℂ)
    rw [Complex.ofReal_mul]
    unfold tilt
    linear_combination (inletBump x : ℂ) * (Real.exp (b*x) : ℂ) * hp
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun x ↦
    mul_nonneg inletBump.nonneg (Real.exp_pos _).le),← integral_const_mul]
  have hv : Integrable v := (inletBump.continuous.mul (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport inletBump.hasCompactSupport.mul_right
  apply integral_mono (inletBump.integrable.const_mul _) hv
  intro x
  by_cases hx : inletBump x = 0
  · simp [v,hx]
  have hm := subset_tsupport _ (show x ∈ support inletBump from hx)
  rw [inletBump.tsupport_eq,Metric.mem_closedBall,Real.dist_eq,sub_zero] at hm
  have hx₁ : |x| ≤ 1 := hm.trans (by norm_num [inletBump])
  have hbx : -α ≤ b*x := (abs_le.mp ((abs_mul _ _).le.trans
    ((mul_le_mul hb hx₁ (abs_nonneg x) hα).trans_eq (mul_one α)))).1
  exact (mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbx) inletBump.nonneg)
private theorem strip_polynomial_bound {Z : Type*} {α : ℝ} (hα : 0≤α) (b t w : Z → ℝ) (hb : ∀ z, |b z|≤α) (hw : ∀ z, 0 ≤ w z)
    (h : ∀ f : S, BddAbove (range (fun z ↦ (radScale F * ‖stripEval (b z) (t z) f‖) * w z))) :
    ∃ C ≥ (0 : ℝ), ∃ k : ℕ, ∀ z, w z ≤ C*(1+|t z|)^k := by
  have : CompleteSpace S := completeSpace_schwartzMap
  have : (uniformity S).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero S]; infer_instance
  let P (z : Z) := (normSeminorm ℂ ℂ).comp
    ((((w z : ℂ) * (radScale F : ℂ)) • stripEval (b z) (t z)).toLinearMap)
  have he (z : Z) (f : S) : P z f = w z * (radScale F * ‖stripEval (b z) (t z) f‖) := by
    change ‖((w z : ℂ)*(radScale F:ℂ)) • stripEval (b z) (t z) f‖ = _
    rw [norm_smul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (hw _),Real.norm_of_nonneg (radScale_pos (F := F)).le,mul_assoc]
  have hbd : BddAbove (range P) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro f
    obtain ⟨B,hB⟩ := h f
    refine ⟨B, forall_mem_range.mpr (fun z ↦ ?_)⟩
    have hz := hB (mem_range_self z)
    rw [he,mul_comm]
    exact hz
  have hcont : Continuous (⨆ z, P z : Seminorm ℂ S) := by
    rw [Seminorm.coe_iSup_eq hbd]
    exact Seminorm.continuous_iSup P (fun z ↦ (((w z:ℂ)*(radScale F:ℂ)) • stripEval (b z) (t z)).continuous.norm) hbd
  obtain ⟨A,hA,k,hk⟩ := orbitBound (bumpS inletBump) (bumpS_compact _) _ hcont
  let c : ℝ := Real.exp (-α) * ∫ x : ℝ, inletBump x
  have hc : 0 < c := mul_pos (Real.exp_pos _) inletBump.integral_pos
  refine ⟨A / (radScale F*c), div_nonneg hA (mul_nonneg (radScale_pos (F := F)).le hc.le), k, fun z ↦ ?_⟩
  have h₁ := (le_ciSup hbd z) (atom (bumpS inletBump) (bumpS_compact _) (t z))
  rw [he] at h₁
  have h₂ : w z * (radScale F*c) ≤ A*(1+|t z|)^k :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (stripEval_atom_lower hα (hb z) (t z))
      (radScale_pos (F := F)).le) (hw z)).trans (h₁.trans (hk (t z)))
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (mul_pos (radScale_pos (F := F)) hc)).2 h₂

private theorem homogeneous_strip_profile (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (η : PontryaginDual C₁) (f : S) :
    ∃ φ : BruhatCompactSupport C𝔽,
      (∀ (k : C₁) (g : C𝔽), φ.val (k.val⁻¹*g) = (η k : ℂ)*φ.val g) ∧
      ∀ σ t : ℝ, nuclearityTestMellin (χ η) φ ((σ:ℂ)+(t:ℂ)*Complex.I) = (radScale F:ℂ)*stripEval σ t f := by
  let b (x : ℝ) := bumpS cutBump x * f x
  obtain ⟨φ,hφ⟩ := exists_characterNormTest (F := F) (χ η)⁻¹ b
    ((bumpS cutBump).smooth'.mul f.smooth') (bumpS_compact cutBump).mul_right
  let l := logIdeleClassNorm F
  have form (g : C𝔽) : φ.val g = (χ η g : ℂ)⁻¹ * b (l g) := by
    rw [hφ]; change (↑((χ η g)⁻¹) : ℂ) * _ = _; rw [Circle.coe_inv]
  refine ⟨φ, fun k g ↦ ?_, fun σ t ↦ ?_⟩
  · have he := DFunLike.congr_fun (hχ η) k
    change χ η k.val = η k at he
    have hl : l (k.val⁻¹ * g) = l g := by
      change Real.log ((ideleClassNorm F (k.val⁻¹ * g)).val:ℝ) = _
      rw [map_mul,map_inv,k.property,inv_one,one_mul]
    rw [form,form,hl,map_mul,map_inv,he,Circle.coe_mul,Circle.coe_inv,mul_inv_rev,inv_inv]
    ring
  · let U (x : ℝ) := b x * (tilt σ x * phase t x)
    have hl : Continuous l := ((NNReal.continuous_coe.comp Units.continuous_val).comp
      (isProperMap_ideleClassNorm F).continuous).log fun g ↦
        (show 0 < ((ideleClassNorm F g).val : ℝ) from NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    have hU : Continuous U := ((bumpS cutBump).continuous.mul f.continuous).mul ((tilt_smooth σ).continuous.mul (phase_smooth t).continuous)
    have he (g : C𝔽) : ideleClassNormTwist (χ η) ((σ:ℂ)+(t:ℂ)*Complex.I) g = (χ η g : ℂ)*(tilt σ (l g)*phase t (l g)) := by
      change (χ η g : ℂ) * ((((ideleClassNorm F g).val : ℝ):ℂ) ^ ((σ:ℂ)+(t:ℂ)*Complex.I)) = _
      have hp : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]
      unfold tilt phase
      rw [Complex.ofReal_exp,←Complex.exp_add,Complex.ofReal_mul]
      congr 2
      change (l g:ℂ)*_ = _
      ring
    have eqI (g : C𝔽) : φ.val g * ideleClassNormTwist (χ η) ((σ:ℂ)+(t:ℂ)*Complex.I) g = U (l g) := by
      rw [he,form]
      dsimp only [U]
      calc
        _ = ((χ η g : ℂ)⁻¹*(χ η g : ℂ)) * (b (l g)*(tilt σ (l g)*phase t (l g))) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (Circle.coe_ne_zero _),one_mul]
    unfold nuclearityTestMellin
    simp_rw [eqI]
    rw [← integral_map hl.aemeasurable hU.aestronglyMeasurable,
      show (ideleClassTamagawaMeasure F).map l = _ from ideleClassTamagawaMeasure_map_logNorm (F := F),
      integral_smul_nnreal_measure,NNReal.smul_def,Complex.real_smul,stripEval_eq]
    rfl
/-- Uniform boundedness for Mellin tests turns the heights into a polynomial majorant. -/
theorem homogeneous_strip_mellin_polynomial {Z : Type*} {α : ℝ} (hα : 0≤α) (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (η : PontryaginDual C₁) (b t w : Z → ℝ) (hb : ∀ z, |b z|≤α) (hw : ∀ z, 0 ≤ w z)
    (h : ∀ φ : BruhatCompactSupport C𝔽,
      (∀ (k : C₁) (g : C𝔽), φ.val (k.val⁻¹*g) = (η k : ℂ)*φ.val g) →
      BddAbove (range (fun z ↦ ‖nuclearityTestMellin (χ η) φ ((b z:ℂ)+(t z:ℂ)*Complex.I)‖ * w z))) :
    ∃ C ≥ (0 : ℝ), ∃ n : ℕ, ∀ z, w z ≤ C*(1+|t z|)^n := by
  apply strip_polynomial_bound (F := F) hα b t w hb hw
  intro f
  obtain ⟨φ,hη,hφ⟩ := homogeneous_strip_profile χ hχ η f
  simpa only [hφ,norm_mul,Complex.norm_real,Real.norm_of_nonneg (radScale_pos (F := F)).le] using h φ hη
end LineModulation

end RiemannMasullo
