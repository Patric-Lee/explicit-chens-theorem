import GRH14MediumPrimeSum
import NumericalPrimePairGrid

/-! A width-sensitive rectangle error, avoiding a fixed error per grid cell. -/
noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open LiuWeight PrimeReciprocalLogScale PrimeReciprocalLogRectangle
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def pairIntervalError (N : ℕ) : ℝ := 100/log (N:ℝ)^2

private opaque pairGridCertificate : {n : ℕ // n=200000} := ⟨200000,rfl⟩
def pairGrid : ℕ := pairGridCertificate.1
theorem pairGrid_eq : pairGrid=200000 := pairGridCertificate.2
theorem pairGrid_pos : 0<pairGrid := by rw [pairGrid_eq]; norm_num

theorem pair_log_mass {a b : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) :
    0 ≤ log (b/a) ∧ log (b/a) ≤ 10*(b-a) := by
  have ha0 : 0<a := by linarith only [ha]
  have hb0 : 0<b := ha0.trans_le hab
  refine ⟨log_nonneg ((le_div_iff₀ ha0).mpr (by simpa using hab)), ?_⟩
  have hh := log_le_sub_one_of_pos (div_pos hb0 ha0)
  have he : b/a-1=(b-a)/a := by field_simp
  rw [he] at hh
  apply hh.trans
  apply (div_le_iff₀ ha0).mpr
  nlinarith only [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ 10*a-1 by linarith only [ha])]

theorem pair_rectangle {N : ℕ} (hN : targetCutoff ≤ N) {a₀ a₁ b₀ b₁ : ℝ}
    (ha : 1/10 ≤ a₀) (haa : a₀ ≤ a₁) (ha1 : a₁ ≤ 1)
    (hb : 1/10 ≤ b₀) (hbb : b₀ ≤ b₁) (hb1 : b₁ ≤ 1) :
    primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ ≤
      logarithmicRectangleMass a₀ a₁ b₀ b₁+
        10*((a₁-a₀)+(b₁-b₀))*pairIntervalError N+pairIntervalError N^2 := by
  have hd0 : 0 ≤ pairIntervalError N := by unfold pairIntervalError; positivity
  have hA := numerical_prime_pair_interval hN ha haa ha1
  have hB := numerical_prime_pair_interval hN hb hbb hb1
  change _ ≤ log (a₁/a₀)+pairIntervalError N at hA
  change _ ≤ log (b₁/b₀)+pairIntervalError N at hB
  have hAn : 0 ≤ primeReciprocalLogInterval N a₀ a₁ := sum_nonneg fun _ _ => by positivity
  have hBn : 0 ≤ primeReciprocalLogInterval N b₀ b₁ := sum_nonneg fun _ _ => by positivity
  have hma := pair_log_mass ha haa
  have hmb := pair_log_mass hb hbb
  have hh := mul_le_mul hA hB hBn (add_nonneg hma.1 hd0)
  have hda := mul_le_mul_of_nonneg_right hma.2 hd0
  have hdb := mul_le_mul_of_nonneg_right hmb.2 hd0
  rw [primeReciprocalLogRectangle_eq_mul,logarithmicRectangleMass]
  nlinarith only [hh,hda,hdb]

theorem pair_grid (n N : ℕ) (hn : 0<n) (hN : targetCutoff ≤ N) :
    liuLogGridMajorant n N ≤ liuLogGridUpperSum n+
      30*(n:ℝ)*pairIntervalError N+5*(n:ℝ)^2*pairIntervalError N^2 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hd0 : 0 ≤ pairIntervalError N := by unfold pairIntervalError; positivity
  have hcard : ((liuLogGridCells n).card:ℝ) ≤ (n:ℝ)^2 := by
    have hh := card_le_univ (liuLogGridCells n)
    have hc : (liuLogGridCells n).card ≤ n*n := by simpa using hh
    simpa only [pow_two,Nat.cast_mul] using (show ((liuLogGridCells n).card:ℝ)≤(n*n:ℕ) by exact_mod_cast hc)
  have he0 : 0 ≤ 30*pairIntervalError N/(n:ℝ)+5*pairIntervalError N^2 := by positivity
  have hcells : liuLogGridMajorant n N ≤ liuLogGridUpperSum n+
      ((liuLogGridCells n).card:ℝ)*(30*pairIntervalError N/(n:ℝ)+5*pairIntervalError N^2) := by
    unfold liuLogGridMajorant liuLogGridUpperSum
    rw [show ((liuLogGridCells n).card:ℝ)*(30*pairIntervalError N/(n:ℝ)+5*pairIntervalError N^2) =
      ∑ _q ∈ liuLogGridCells n, (30*pairIntervalError N/(n:ℝ)+5*pairIntervalError N^2) by simp only [sum_const,nsmul_eq_mul] <;> ring]
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro q hq
    have ha0 : 1/10 ≤ liuAlphaGridPoint n q.1 := by
      rw [liuAlphaGridPoint_eq_step hn]
      exact le_add_of_nonneg_right (by positivity [liuAlphaGridStep_pos hn])
    have hb0 : 1/10 ≤ liuBetaGridPoint n q.2 := by
      rw [liuBetaGridPoint_eq_step hn]
      have hh : 0≤(q.2:ℝ)*liuBetaGridStep n := by positivity [liuBetaGridStep_pos hn]
      linarith only [hh]
    have hb1 := ChenEffective.numerical_beta_grid_endpoint hn q.2.isLt
    have hr := pair_rectangle hN ha0 (liuAlphaGridPoint_lt_succ hn).le
      ((liuAlphaGridPoint_succ_le_end hn q.1.isLt).trans (by norm_num)) hb0
      (liuBetaGridPoint_lt_succ hn).le (hb1.trans (by norm_num))
    have hw : 10*((liuAlphaGridPoint n (q.1+1)-liuAlphaGridPoint n q.1)+
        (liuBetaGridPoint n (q.2+1)-liuBetaGridPoint n q.2)) ≤ 6/(n:ℝ) := by
      rw [liuAlphaGridPoint_eq_step hn,liuAlphaGridPoint_eq_step hn,
        liuBetaGridPoint_eq_step hn,liuBetaGridPoint_eq_step hn]
      simp only [Nat.cast_add,Nat.cast_one,liuAlphaGridStep,liuBetaGridStep]
      field_simp <;> ring_nf <;> norm_num
    have hk := liuLogGrid_upperKernel_le_five hn hq
    have hk0 : 0 ≤ 1/(1-liuAlphaGridPoint n (q.1+1)-liuBetaGridPoint n (q.2+1)) := by
      have hh := liuLogGridCell_upperCorner_lt_one hn hq
      apply div_nonneg (by norm_num)
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_left hr hk0
    have her := mul_le_mul_of_nonneg_right hw hd0
    have hep := mul_le_mul_of_nonneg_left (show
      10*((liuAlphaGridPoint n (q.1+1)-liuAlphaGridPoint n q.1)+
        (liuBetaGridPoint n (q.2+1)-liuBetaGridPoint n q.2))*pairIntervalError N+
        pairIntervalError N^2 ≤ 6/(n:ℝ)*pairIntervalError N+pairIntervalError N^2 by
          linarith only [her]) hk0
    have he := mul_le_mul_of_nonneg_right hk (show
      0 ≤ 6/(n:ℝ)*pairIntervalError N+pairIntervalError N^2 by positivity)
    have hid : 5*(6/(n:ℝ)*pairIntervalError N+pairIntervalError N^2)=
      30*pairIntervalError N/(n:ℝ)+5*pairIntervalError N^2 := by ring
    rw [hid] at he
    nlinarith only [hh,hep,he]
  apply hcells.trans
  have hh := mul_le_mul_of_nonneg_right hcard he0
  have hid : (n:ℝ)^2*(30*pairIntervalError N/(n:ℝ)+5*pairIntervalError N^2)=
      30*(n:ℝ)*pairIntervalError N+5*(n:ℝ)^2*pairIntervalError N^2 := by field_simp <;> ring
  rw [hid] at hh
  linarith only [hh]

theorem pair_proxy_at_target {N : ℕ} (hN : targetCutoff ≤ N) :
    log (N:ℝ)*liuSourceReciprocalLogSum N ≤ (0.49694:ℝ) := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn9 := (numerical_prime_pair_parameters hN).1
  have he0 : 0 ≤ pairIntervalError N := by unfold pairIntervalError; positivity
  have he : pairIntervalError N ≤ (1/10000000000:ℝ) := by
    unfold pairIntervalError
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
    nlinarith only [hL,sq_nonneg (log (N:ℝ)-1000000)]
  have hes := pow_le_pow_left₀ he0 he 2
  have hg := pair_grid pairGrid N pairGrid_pos hN
  have hm := liuLogGridUpperSum_sub_source_le pairGrid pairGrid_pos
  have hc := liuPairLogKernelSum_le_logGridMajorant pairGrid N pairGrid_pos (by omega)
  rw [← log_mul_liuSourceReciprocalLogSum_eq_pairLogKernelSum N (by omega)] at hc
  have hmesh : 759/(pairGrid:ℝ)≤(0.003795:ℝ) := by rw [pairGrid_eq]; norm_num
  have hfinite : 30*(pairGrid:ℝ)*pairIntervalError N+
      5*(pairGrid:ℝ)^2*pairIntervalError N^2≤(0.000601:ℝ) := by
    rw [pairGrid_eq]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [he,hes]
  linarith only [hg,hm,hc,hmesh,hfinite,liuSourceMainIntegral_lt]

#print axioms pair_proxy_at_target
end ChenEffective.GRH14



