import BJSH30PrimeIntervals
import NumericalPrimePairGrid

noncomputable section
namespace ChenEffective.H30
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open LiuWeight PrimeReciprocalLogScale PrimeReciprocalLogRectangle
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

def primePairGrid : ℕ := 10000000
theorem primePairGrid_eq : primePairGrid=10000000 := rfl
theorem primePairGrid_pos : 0<primePairGrid := by decide

def primePairIntervalError (N : ℕ) : ℝ := 100/Real.log (N : ℝ)^2

theorem numerical_prime_pair_rectangle {N : ℕ} (hN : (10^12:ℝ) ≤ Real.log (N:ℝ)) {a₀ a₁ b₀ b₁ : ℝ}
    (ha : 1/10 ≤ a₀) (haa : a₀ ≤ a₁) (ha1 : a₁ ≤ 1)
    (hb : 1/10 ≤ b₀) (hbb : b₀ ≤ b₁) (hb1 : b₁ ≤ 1) :
    primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ ≤
      logarithmicRectangleMass a₀ a₁ b₀ b₁+21*primePairIntervalError N := by
  obtain ⟨_,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have hL0 : 0 < Real.log (N : ℝ) := by nlinarith only [hlog,sq_nonneg (Real.log (N:ℝ)-10^12)]
  have hd0 : 0 ≤ primePairIntervalError N := by unfold primePairIntervalError; positivity
  have hd1 : primePairIntervalError N ≤ 1 := by
    unfold primePairIntervalError
    apply (div_le_one (sq_pos_of_pos hL0)).mpr
    nlinarith only [hlog,sq_nonneg (Real.log (N:ℝ)-10^12)]
  have haMass := numerical_prime_pair_log_mass ha haa ha1
  have hbMass := numerical_prime_pair_log_mass hb hbb hb1
  have hA := numerical_prime_pair_interval hN ha haa ha1
  have hB := numerical_prime_pair_interval hN hb hbb hb1
  have hAn : 0 ≤ primeReciprocalLogInterval N a₀ a₁ := sum_nonneg fun _ _ => by positivity
  have hBn : 0 ≤ primeReciprocalLogInterval N b₀ b₁ := sum_nonneg fun _ _ => by positivity
  change _ ≤ Real.log (b₁/b₀)+primePairIntervalError N at hB
  change _ ≤ Real.log (a₁/a₀)+primePairIntervalError N at hA
  rw [primeReciprocalLogRectangle_eq_mul,logarithmicRectangleMass]
  have hh := mul_le_mul hA hB hBn (add_nonneg haMass.1 hd0)
  have hda := mul_le_mul_of_nonneg_right haMass.2 hd0
  have hdb := mul_le_mul_of_nonneg_right hbMass.2 hd0
  have hdd := mul_le_mul_of_nonneg_right hd1 hd0
  nlinarith only [hh,hda,hdb,hdd]

theorem numerical_beta_grid_endpoint {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    liuBetaGridPoint n (i+1) ≤ 9/20 := by
  have hiR : ((i+1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hi)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : ((i+1 : ℕ) : ℝ)/(n : ℝ) ≤ 1 := (div_le_one hnR).mpr hiR
  unfold liuBetaGridPoint
  nlinarith only [hratio]

theorem numerical_prime_pair_grid (n N : ℕ) (hn : 0 < n) (hN : (10^12:ℝ) ≤ Real.log (N:ℝ)) :
    liuLogGridMajorant n N ≤ liuLogGridUpperSum n+105*primePairIntervalError N*(n : ℝ)^2 := by
  have hd0 : 0 ≤ primePairIntervalError N := by
    have hh := (numerical_prime_pair_parameters hN).2.1
    unfold primePairIntervalError
    positivity
  have hcard : (liuLogGridCells n).card ≤ n*n := by
    have hh := card_le_univ (liuLogGridCells n)
    simpa only [Fintype.card_prod,Fintype.card_fin] using hh
  have hcardR : ((liuLogGridCells n).card : ℝ) ≤ (n : ℝ)^2 := by
    simpa only [Nat.cast_mul,pow_two] using (show ((liuLogGridCells n).card : ℝ) ≤ (n*n : ℕ) by exact_mod_cast hcard)
  unfold liuLogGridMajorant
  calc
    _ ≤ ∑ q ∈ liuLogGridCells n,
        ((1/(1-liuAlphaGridPoint n (q.1+1)-liuBetaGridPoint n (q.2+1)))*
          logarithmicRectangleMass (liuAlphaGridPoint n q.1) (liuAlphaGridPoint n (q.1+1))
            (liuBetaGridPoint n q.2) (liuBetaGridPoint n (q.2+1)) + 105*primePairIntervalError N) := by
      apply sum_le_sum
      intro q hq
      have ha0 : 1/10 ≤ liuAlphaGridPoint n q.1 := by
        rw [liuAlphaGridPoint_eq_step hn]
        exact le_add_of_nonneg_right (by positivity [liuAlphaGridStep_pos hn])
      have hb0 : 1/10 ≤ liuBetaGridPoint n q.2 := by
        rw [liuBetaGridPoint_eq_step hn]
        have hh : 0 ≤ (q.2 : ℝ)*liuBetaGridStep n := by positivity [liuBetaGridStep_pos hn]
        linarith only [hh]
      have hRect := numerical_prime_pair_rectangle hN ha0 (liuAlphaGridPoint_lt_succ hn).le
        ((liuAlphaGridPoint_succ_le_end hn q.1.isLt).trans (by norm_num)) hb0
        (liuBetaGridPoint_lt_succ hn).le ((numerical_beta_grid_endpoint hn q.2.isLt).trans (by norm_num))
      have hcorner := liuLogGridCell_upperCorner_lt_one hn hq
      have hc0 : 0 ≤ 1/(1-liuAlphaGridPoint n (q.1+1)-liuBetaGridPoint n (q.2+1)) := by
        apply div_nonneg (by norm_num)
        linarith only [hcorner]
      have hc5 := liuLogGrid_upperKernel_le_five hn hq
      have hh := mul_le_mul_of_nonneg_left hRect hc0
      have he := mul_le_mul_of_nonneg_right hc5 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 21) hd0)
      nlinarith only [hh,he]
    _ = liuLogGridUpperSum n+((liuLogGridCells n).card : ℝ)*(105*primePairIntervalError N) := by
      rw [sum_add_distrib]
      simp only [liuLogGridUpperSum,sum_const,nsmul_eq_mul]
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hcardR (show 0 ≤ 105*primePairIntervalError N by positivity)]

theorem numerical_prime_pair_proxy {N : ℕ} (hN : (10^12:ℝ) ≤ Real.log (N:ℝ)) :
    Real.log (N : ℝ)*liuSourceReciprocalLogSum N ≤ (0.49254 : ℝ)+82/1000000 := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have hL0 : 0 < Real.log (N : ℝ) := by nlinarith only [hlog,sq_nonneg (Real.log (N:ℝ)-10^12)]
  have hg := numerical_prime_pair_grid primePairGrid N primePairGrid_pos hN
  have hm := liuLogGridUpperSum_sub_source_le primePairGrid primePairGrid_pos
  have hmesh : 759/(primePairGrid : ℝ) ≤ (8 : ℝ)/100000 := by rw [primePairGrid_eq]; norm_num
  have hfinite : 105*primePairIntervalError N*(primePairGrid : ℝ)^2 ≤ (2 : ℝ)/1000000 := by
    unfold primePairIntervalError
    rw [primePairGrid_eq]
    norm_num only [Nat.cast_ofNat]
    have he : 105*(100/Real.log (N:ℝ)^2)*(100000000000000:ℝ)=
        (1050000000000000000:ℝ)/Real.log (N:ℝ)^2 := by ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hL0)).mpr
    nlinarith only [hlog,sq_nonneg (Real.log (N:ℝ)-10^12)]
  have hcover := liuPairLogKernelSum_le_logGridMajorant primePairGrid N primePairGrid_pos (by omega)
  rw [← log_mul_liuSourceReciprocalLogSum_eq_pairLogKernelSum N (by omega)] at hcover
  linarith only [hcover,hg,hm,hmesh,hfinite,liuSourceMainIntegral_lt]

#print axioms numerical_prime_pair_proxy
end ChenEffective.H30
