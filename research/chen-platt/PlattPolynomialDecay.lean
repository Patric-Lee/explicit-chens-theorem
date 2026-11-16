import PlattPolynomialSmoothing
import TernaryGoldbach.Explicit.XiPartial
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

noncomputable section
namespace ChenEffective.PlattWindow.ContourDecay
open Complex MeasureTheory Set Filter Metric TernaryGoldbach.Explicit
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt
set_option autoImplicit false
set_option maxHeartbeats 2400000

def polynomialEnvelope (K t : ℝ) : ℝ := K/(1+t)^2

theorem polynomialEnvelope_nonneg {K : ℝ} (hK : 0 ≤ K) (t : ℝ) :
    0 ≤ polynomialEnvelope K t := div_nonneg hK (sq_nonneg _)

theorem polynomialEnvelope_antitone {K : ℝ} (hK : 0 ≤ K) :
    AntitoneOn (polynomialEnvelope K) (Ici 0) := by
  intro a ha b hb hab
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  dsimp [polynomialEnvelope]
  apply div_le_div_of_nonneg_left hK (by nlinarith only [ha])
  nlinarith only [ha,hb,hab]

/-- A coarse square-root majorant is sufficient for vertical integrability. -/
theorem log_BPz2_sqrt (t : ℝ) : Real.log (BPz2 t/0.355) ≤ 100*Real.sqrt (1+|t|) := by
  have hu : 0 ≤ |t| := abs_nonneg t
  have hr : 1 ≤ Real.sqrt (1+|t|) := Real.le_sqrt_of_sq_le (by nlinarith only [hu])
  have hsq := Real.sq_sqrt (by nlinarith only [hu] : 0 ≤ 1+|t|)
  have h22 : Real.sqrt (|t|+22) ≤ 5*Real.sqrt (1+|t|) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hsq,hu]
  have h11 : Real.sqrt (1.25*(|t|+11)) ≤ 4*Real.sqrt (1+|t|) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hsq,hu]
  have h1 := Real.log_le_rpow_div (ε:=(1/2:ℝ)) (by positivity : 0 ≤ |t|+22) (by norm_num)
  have h2 := Real.log_le_rpow_div (ε:=(1/2:ℝ)) (by positivity : 0 ≤ 1.25*(|t|+11)) (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h1 h2
  have h := log_BPz2_le' t
  nlinarith only [h,h1,h2,h22,h11,hr]

theorem HkD_linear (k : ℕ) : HkD BPz2 (k+1) ≤ 200000*((k:ℝ)+1) := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hu : (1:ℝ) ≤ (k:ℝ)+1 := by linarith only [hk]
  have hr : 1 ≤ Real.sqrt ((k:ℝ)+1) := Real.le_sqrt_of_sq_le (by nlinarith only [hu])
  have hsq := Real.sq_sqrt (by linarith only [hu] : (0:ℝ) ≤ (k:ℝ)+1)
  have hz : 1 ≤ (1.25:ℝ)*((k:ℝ)+24) := by nlinarith only [hk]
  have hs : Real.sqrt (1.25*((k:ℝ)+24)) ≤ 6*Real.sqrt ((k:ℝ)+1) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hsq,hk]
  have hl := Real.log_le_rpow_div (ε:=(1/2:ℝ)) (zero_le_one.trans hz) (by norm_num)
  rw [← Real.sqrt_eq_rpow] at hl
  let P : ℝ := 10.24+10*Real.log (1.25*((k:ℝ)+24))
  have hP0 : 0 ≤ P := by
    have hlog := Real.log_nonneg hz
    dsimp [P]
    linarith only [hlog]
  have hP : P ≤ 131*Real.sqrt ((k:ℝ)+1) := by dsimp [P]; nlinarith only [hl,hs,hr]
  have hp2 := pow_le_pow_left₀ hP0 hP 2
  have hself : Real.sqrt ((k:ℝ)+1) ≤ (k:ℝ)+1 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith only [hu]
  have h := HkD_BPz2_le (k+1)
  push_cast at h
  have he : (k:ℝ)+1+23=(k:ℝ)+24 := by ring
  rw [he] at h
  change HkD BPz2 (k+1) ≤ 11.4*P^2+7.7*P at h
  nlinarith only [h,hp2,hP,hself,hsq,hu]

theorem polynomialEnvelope_decay {K : ℝ} (hK : 0 ≤ K) :
    Tendsto (fun k : ℕ => HkD BPz2 (k+1)*polynomialEnvelope K ((k:ℝ)+1)) atTop (𝓝 0) := by
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (200000*K)
  simp only [mul_zero] at hlim
  apply squeeze_zero (fun k => mul_nonneg (HkD_BPz2_nonneg _) (polynomialEnvelope_nonneg hK _)) ?_ hlim
  intro k
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have h := HkD_linear k
  dsimp [polynomialEnvelope]
  calc
    _ ≤ (200000*((k:ℝ)+1))*(K/(1+((k:ℝ)+1))^2) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ ≤ (200000*((k:ℝ)+1))*(K/((k:ℝ)+1)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_left hK (by positivity)
      nlinarith only [hk]
    _ = _ := by
      field_simp
      <;> ring

theorem PolynomialSmoothing.integrable_hIntD_of_sqrt_bound
    {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR K A x σ : ℝ} {φ : ℝ → ℂ}
    (hd : LDatum f B D CR) (hφ : PolynomialSmoothing φ K) (hx : 0 < x)
    (hσ1 : -1/2 ≤ σ) (hσ2 : σ ≤ 3/2)
    (hne : ∀ t : ℝ, f ((σ:ℂ)+t*I) ≠ 0) (hA : 0 ≤ A)
    (hbound : ∀ t : ℝ, ‖logDeriv f ((σ:ℂ)+t*I)‖ ≤ A*Real.sqrt (1+|t|)) :
    Integrable fun t : ℝ => hIntD f φ x ((σ:ℂ)+t*I) := by
  have hK := hφ.K_nonneg
  have hp : Integrable (fun t : ℝ => (1+|t|)^(-3/2:ℝ)) := by
    have h := integrable_one_add_norm (E:=ℝ) (r:=(3/2:ℝ)) (μ:=volume) (by norm_num)
    norm_num only [Real.norm_eq_abs] at h ⊢
    exact h
  have hc : Continuous fun t : ℝ => hIntD f φ x ((σ:ℂ)+t*I) := by
    unfold hIntD
    exact (continuous_logDeriv_lineD hd σ hne).mul
      ((hφ.continuous_line (by linarith only [hσ1])).mul
        (continuous_iff_continuousAt.mpr fun t =>
          (continuousAt_const_cpow (Complex.ofReal_ne_zero.mpr hx.ne')).comp (by fun_prop)))
  refine (hp.const_mul (A*K*x^σ)).mono' hc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hm := hφ.strip ((σ:ℂ)+t*I) (by simpa using hσ1) (by simpa using hσ2)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hm
  have hu : 0 < 1+|t| := by positivity
  have he : Real.sqrt (1+|t|)/(1+|t|)^2=(1+|t|)^(-3/2:ℝ) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_two,← Real.rpow_sub hu]
    norm_num
  rw [hIntD,norm_mul,norm_mul,norm_cpow_x hx]
  simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero]
  calc
    _ ≤ (A*Real.sqrt (1+|t|))*((K/(1+|t|)^2)*x^σ) := by gcongr; exact hbound t
    _ = (A*K*x^σ)*(Real.sqrt (1+|t|)/(1+|t|)^2) := by ring
    _ = _ := by rw [he]

#print axioms polynomialEnvelope_decay
#print axioms PolynomialSmoothing.integrable_hIntD_of_sqrt_bound
end ChenEffective.PlattWindow.ContourDecay
