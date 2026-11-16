import PlattPolynomialDecay
import TernaryGoldbach.Explicit.ZetaExplicit

/-! Polynomial-decay version of the zeta explicit formula. The zeta residue
argument is adapted from the pinned calr3 ZetaExplicit proof. The polynomial
zeta growth datum avoids the exponentially growing original growth envelope.
No finite-RH or numerical zero estimate is assumed in this identity. -/
noncomputable section
namespace ChenEffective.PlattWindow.ContourDecay
open Complex MeasureTheory Set Filter Metric TernaryGoldbach.Explicit
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt
set_option autoImplicit false
set_option maxHeartbeats 2600000

theorem PolynomialSmoothing.integrable_hIntD_right
    {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR K x : ℝ} {φ : ℝ → ℂ}
    (hφ : PolynomialSmoothing φ K) (hd : LDatum f B D CR) (hx : 0 < x) :
    Integrable fun t : ℝ => hIntD f φ x (((3/2:ℝ):ℂ)+t*I) := by
  have hCR : 0 ≤ CR := (norm_nonneg _).trans (hd.right_bound 0)
  apply hφ.integrable_hIntD_of_sqrt_bound hd hx (by norm_num) le_rfl
    (fun t => hd.nz_right _ (by simp; norm_num)) hCR
  intro t
  have hs : 1 ≤ Real.sqrt (1+|t|) := Real.le_sqrt_of_sq_le (by nlinarith only [abs_nonneg t])
  exact (hd.right_bound t).trans (le_mul_of_one_le_right hCR hs)

theorem PolynomialSmoothing.integrable_hIntD_zeta_left {φ : ℝ → ℂ} {K x : ℝ}
    (hφ : PolynomialSmoothing φ K) (hx : 0 < x) :
    Integrable fun t : ℝ => hIntD zetaF φ x (((-1/2:ℝ):ℂ)+t*I) := by
  apply hφ.integrable_hIntD_of_sqrt_bound ldatum_zeta2 hx le_rfl (by norm_num)
    (fun t => zetaF_ne_zero_strip (by simp; norm_num) (by simp; norm_num))
    (by norm_num : (0:ℝ) ≤ 800)
  intro t
  have h := norm_logDeriv_leftD ldatum_zeta2 t
  have hl := log_BPz2_sqrt t
  have hl2 : (0.69:ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hc0 : 0 ≤ 2/Real.log 2+4.8 := by positivity
  have hc : 2/Real.log 2+4.8 ≤ (8:ℝ) := by
    have hd := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 0.69) hl2
    linarith only [hd]
  calc
    _ ≤ Real.log (BPz2 t/0.355)/Real.log 2/(1/2)+4.8*Real.log (BPz2 t/0.355) := h
    _ = (2/Real.log 2+4.8)*Real.log (BPz2 t/0.355) := by ring
    _ ≤ (2/Real.log 2+4.8)*(100*Real.sqrt (1+|t|)) := mul_le_mul_of_nonneg_left hl hc0
    _ ≤ 8*(100*Real.sqrt (1+|t|)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem PolynomialSmoothing.integrable_hIntD_subone_left {φ : ℝ → ℂ} {K x : ℝ}
    (hφ : PolynomialSmoothing φ K) (hx : 0 < x) :
    Integrable fun t : ℝ => hIntD (fun s : ℂ => s-1) φ x (((-1/2:ℝ):ℂ)+t*I) := by
  apply hφ.integrable_hIntD_of_sqrt_bound ldatum_sub_one hx le_rfl (by norm_num)
    (fun t => ldatum_sub_one.nz_strip _ (by simp; norm_num) (by simp; norm_num))
    (by norm_num : (0:ℝ) ≤ 2)
  intro t
  have hr : (3/2:ℝ) ≤ ‖((-1/2:ℝ):ℂ)+t*I-1‖ := by
    calc
      _ = |(((-1/2:ℝ):ℂ)+t*I-1).re| := by norm_num
      _ ≤ _ := Complex.abs_re_le_norm _
  have hs : 1 ≤ Real.sqrt (1+|t|) := Real.le_sqrt_of_sq_le (by nlinarith only [abs_nonneg t])
  rw [logDeriv_sub_one,norm_div,norm_one]
  have hn : 0 < ‖((-1/2:ℝ):ℂ)+t*I-1‖ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 3/2) hr
  apply ((div_le_iff₀ hn).mpr (by linarith only [hr] : (1:ℝ) ≤ 2*‖((-1/2:ℝ):ℂ)+t*I-1‖)).trans
  nlinarith only [hs]

theorem B1_le_BPz2 (t : ℝ) : B1 t ≤ BPz2 t := by
  have ht := abs_nonneg t
  have hbase : (1:ℝ) ≤ 1.25*(|t|+11) := by linarith only [ht]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hbase 9
  norm_num only [one_pow] at hp
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 9200*(|t|+22))
  have hn : 0 ≤ 20*(|t|+22)^3*(1.25*(|t|+11))^2 := by positivity
  unfold B1 BPz2
  nlinarith only [hm,hn,ht]

theorem HkD_subone_nonneg (k : ℕ) : 0 ≤ HkD B1 k := by
  have hb := ldatum_sub_one.B_ge ((k:ℝ)+1)
  have hl : 0 ≤ Real.log (B1 ((k:ℝ)+1)/0.355) := Real.log_nonneg
    ((le_div_iff₀ (by norm_num : (0:ℝ) < 0.355)).mpr (by linarith only [hb]))
  unfold HkD
  positivity

theorem HkD_subone_le (k : ℕ) : HkD B1 k ≤ HkD BPz2 k := by
  have hb := ldatum_sub_one.B_ge ((k:ℝ)+1)
  have h1 : 0 ≤ Real.log (B1 ((k:ℝ)+1)/0.355) := Real.log_nonneg
    ((le_div_iff₀ (by norm_num : (0:ℝ) < 0.355)).mpr (by linarith only [hb]))
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < B1 ((k:ℝ)+1)/0.355)
    (div_le_div_of_nonneg_right (B1_le_BPz2 ((k:ℝ)+1)) (by norm_num : (0:ℝ) ≤ 0.355))
  have h2 : 0 ≤ Real.log (BPz2 ((k:ℝ)+1)/0.355) := h1.trans hlog
  unfold HkD
  gcongr

theorem polynomialEnvelope_subone_decay {K : ℝ} (hK : 0 ≤ K) :
    Tendsto (fun k : ℕ => HkD B1 (k+1)*polynomialEnvelope K ((k:ℝ)+1)) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun k => mul_nonneg (HkD_subone_nonneg _) (polynomialEnvelope_nonneg hK _))
    (fun k => mul_le_mul_of_nonneg_right (HkD_subone_le _) (polynomialEnvelope_nonneg hK _))
    (polynomialEnvelope_decay hK)

theorem explicit_formula_zeta_polynomial {φ : ℝ → ℂ} {K : ℝ} (hφ : PolynomialSmoothing φ K) {x : ℝ} (hx : 0 < x) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
          (mellin φ u * (x : ℂ) ^ u)) atTop
        (𝓝 (mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x -
          (1 / (2 * π) : ℂ) * ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I))) := by
  obtain ⟨T, hT, hlim⟩ := explicit_formula_of_decay ldatum_zeta2 hx hφ.diff (polynomialEnvelope K)
    (polynomialEnvelope_nonneg hφ.K_nonneg) (polynomialEnvelope_antitone hφ.K_nonneg)
    hφ.strip (polynomialEnvelope_decay hφ.K_nonneg)
    (hφ.integrable_hIntD_right ldatum_zeta2 hx) (hφ.integrable_hIntD_zeta_left hx)
  obtain ⟨T', hT', hlim1⟩ := explicit_formula_of_decay ldatum_sub_one hx hφ.diff (polynomialEnvelope K)
    (polynomialEnvelope_nonneg hφ.K_nonneg) (polynomialEnvelope_antitone hφ.K_nonneg)
    hφ.strip (polynomialEnvelope_subone_decay hφ.K_nonneg)
    (hφ.integrable_hIntD_right ldatum_sub_one hx) (hφ.integrable_hIntD_subone_left hx)
  refine ⟨T, hT, ?_⟩
  -- the main term from `s − 1`
  have hconst : ∀ k, ∑ u ∈ zerosRectD (fun s : ℂ => s - 1) (T' k),
      (multRectD (fun s : ℂ => s - 1) (T' k) u : ℂ) * (mellin φ u * (x : ℂ) ^ u) = mellin φ 1 * x := by
    intro k
    have hpos : 0 < T' k := by linarith [(hT' k).1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    rw [sum_zerosRect_sub_one hpos, Complex.cpow_one]
  simp_rw [hconst] at hlim1
  have hM1 := tendsto_nhds_unique tendsto_const_nhds hlim1
  have hR1 : ∀ y : ℝ, ((3 / 2 : ℝ) : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h; simp at this; norm_num at this
  have hL1 : ∀ y : ℝ, ((-1 / 2 : ℝ) : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h; simp at this; norm_num at this
  have hRz : ∀ y : ℝ, riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := fun y =>
    riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)
  have hLz : ∀ y : ℝ, riemannZeta (((-1 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := fun y =>
    zeta_ne_zero_of_zetaF (hL1 y) (zetaF_ne_zero_strip (by simp; norm_num) (by simp; norm_num))
  have iR := hφ.integrable_hIntD_right ldatum_zeta2 hx
  have iL := hφ.integrable_hIntD_zeta_left hx
  have iR1 := hφ.integrable_hIntD_right ldatum_sub_one hx
  have iL1 := hφ.integrable_hIntD_subone_left hx
  set A := ∫ y : ℝ, hIntD zetaF φ x (((3 / 2 : ℝ) : ℂ) + y * I) with hA
  set A1 := ∫ y : ℝ, hIntD (fun s : ℂ => s - 1) φ x (((3 / 2 : ℝ) : ℂ) + y * I) with hA1
  set Bv := ∫ y : ℝ, hIntD zetaF φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hBv
  set B1v := ∫ y : ℝ, hIntD (fun s : ℂ => s - 1) φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hB1v
  have IR : ∫ y : ℝ, hZeta φ x (((3 / 2 : ℝ) : ℂ) + y * I) = A - A1 := by
    rw [hA, hA1, ← integral_sub iR iR1]
    congr 1; ext y; rw [hIntD_zetaF_eq φ x (hR1 y) (hRz y)]; ring
  have IL : ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I) = Bv - B1v := by
    rw [hBv, hB1v, ← integral_sub iL iL1]
    congr 1; ext y; rw [hIntD_zetaF_eq φ x (hL1 y) (hLz y)]; ring
  -- the Dirichlet series on `ℜs = 3/2`
  have hS := SsumG_eq_line (1 : DirichletCharacter ℂ 1) hφ hx
  have hF : ∀ t : ℝ, Fline (1 : DirichletCharacter ℂ 1) φ x (((3 / 2 : ℝ) : ℂ) + t * I) =
      -hZeta φ x (((3 / 2 : ℝ) : ℂ) + t * I) := by
    intro t
    rw [Fline, hZeta, LFunction_one_mod_one, logDeriv_apply]; ring
  simp_rw [hF, integral_neg, IR] at hS
  convert hlim using 2
  rw [hM1, hS, IL]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring


#print axioms explicit_formula_zeta_polynomial
end ChenEffective.PlattWindow.ContourDecay
