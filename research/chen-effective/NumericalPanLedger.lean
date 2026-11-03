import NumericalPanLow
import NumericalPanAggregate
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimitiveLedgerAssembly

noncomputable section
namespace ChenEffective
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open NumericalPanHigh
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def panLedgerConstant (U : ℕ) : ℝ := panLowConstant U (U+6)+panHighConstant+6984
@[irreducible] def panLedgerThreshold (U : ℕ) : ℕ :=
  max (panLowThreshold U (U+6)) (max (panHighThreshold (U+6)) (logPowerCutoff (U+2)))

theorem panLedgerConstant_pos (U : ℕ) : 0 < panLedgerConstant U := by
  unfold panLedgerConstant panLowConstant panMovingPrimeConstant panPrimePrefixConstant
    primitiveNumericalConstant panHighConstant panCellConstant panShortConstant panLongConstant
  have := panSharpConstant_pos
  positivity

theorem numerical_pan_conductor_bounds (B N : ℕ) (hN : panHighThreshold B ≤ N) :
    1 ≤ Real.log (N : ℝ) ∧ 1 ≤ ⌊lowConductor N (B : ℝ)⌋₊ ∧
      ⌊lowConductor N (B : ℝ)⌋₊ ≤ panModulusCutoff N (B : ℝ) ∧
      (panModulusCutoff N (B : ℝ) : ℝ) ≤ Real.sqrt N ∧
      panModulusCutoff N (B : ℝ) ≤ N := by
  have hl := numerical_high_log_four hN
  have hlog : 1 ≤ Real.log (N : ℝ) := by linarith only [hl]
  have hp := hN
  unfold panHighThreshold at hp
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hp
  have hbound := log_pow_le_rpow_inv_explicit (k := 2*B) (m := 2)
    (by norm_num) (by omega : 2*(2*B) ≤ 6*B) hp
  have hd : 1 ≤ lowConductor N (B : ℝ) := lowConductor_ge_one hlog (Nat.cast_nonneg B)
  have hdp : 0 < lowConductor N (B : ℝ) := zero_lt_one.trans_le hd
  have hsq : lowConductor N (B : ℝ)*lowConductor N (B : ℝ) ≤ Real.sqrt N := by
    rw [lowConductor, Real.rpow_natCast, ← pow_two, ← pow_mul, Nat.mul_comm B 2,
      Real.sqrt_eq_rpow]
    exact hbound
  have horder : lowConductor N (B : ℝ) ≤ upperConductor N (B : ℝ) :=
    (le_div_iff₀ hdp).mpr hsq
  have hfloor : (panModulusCutoff N (B : ℝ) : ℝ) ≤ Real.sqrt N := by
    rw [panModulusCutoff_eq_upper]
    exact (Nat.floor_le (by unfold upperConductor; positivity)).trans
      (upperConductor_le_sqrt hlog (Nat.cast_nonneg B))
  refine ⟨hlog, Nat.le_floor (by simpa using hd), ?_, hfloor, ?_⟩
  · rw [panModulusCutoff_eq_upper]
    exact Nat.floor_mono horder
  · exact_mod_cast hfloor.trans (Real.sqrt_le_self_iff.mpr
      (Or.inr (by exact_mod_cast (show 1 ≤ N by omega))))

theorem numerical_pan_high_remainder (U N : ℕ) (hN : logPowerCutoff (U+2) ≤ N) :
    6984*Real.log (N : ℝ)^2/N ≤ 6984*N/Real.log (N : ℝ)^U := by
  have hN9 := (logPowerCutoff_nine_le _).trans hN
  have hL := log_one_le_of_eight_le (by omega : 8 ≤ N)
  have hl0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp := log_pow_le_rpow_inv_explicit (k := U+2) (m := 1) (by norm_num)
    (by omega : 1*(U+2) ≤ U+2) hN
  norm_num only [Nat.cast_one, inv_one, Real.rpow_one] at hp
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < N) (pow_pos hl0 U)).mpr
  have hh : Real.log (N : ℝ)^2*Real.log (N : ℝ)^U ≤ (N : ℝ) := by
    rw [← pow_add, Nat.add_comm 2 U]
    exact hp
  nlinarith only [hh, hN1, sq_nonneg ((N : ℝ)-1)]

theorem numerical_pan_ledger (U N : ℕ) (hN : panLedgerThreshold U ≤ N)
    (m : ℕ) (hm : m ∈ Icc 1 (panModulusCutoff N ((U+6 : ℕ) : ℝ))) :
    liuPanPrimitiveCofactorLedger N (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ))
      (liuPanSourceIntervalUpper N) (panModulusCutoff N ((U+6 : ℕ) : ℝ)) m
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
        panLedgerConstant U*N/Real.log (N : ℝ)^U := by
  have hn := hN
  unfold panLedgerThreshold at hn
  obtain ⟨hNL, hNH, hNR⟩ := (max_le_iff.mp hn).imp_right max_le_iff.mp
  obtain ⟨hlog, hD1, hD, hDN, hcut⟩ := numerical_pan_conductor_bounds (U+6) N hNH
  have hN9 := (logPowerCutoff_nine_le _).trans hNR
  obtain ⟨hmpos, hmcutoff⟩ := mem_Icc.mp hm
  have hmN : (m : ℝ) ≤ Real.sqrt N :=
    (show (m : ℝ) ≤ panModulusCutoff N ((U+6 : ℕ) : ℝ) by exact_mod_cast hmcutoff).trans hDN
  have hA : (liuPanSourceIntervalUpper N : ℝ) ≤ (N : ℝ)^(2/3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hAN : liuPanSourceIntervalUpper N ≤ N := by
    exact_mod_cast hA.trans (Real.rpow_le_self_of_one_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num))
  have hf : ∀ a, ‖(liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)‖ ≤ 1 := by
    intro a
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_liuWeight] using
      liuWeight_le_one N (liuSourceZ10 N) (liuSourceY3 N) a
  have hlow := numerical_pan_low U (U+6) N hNL m
    (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ)) (liuPanSourceIntervalUpper N)
    ⌊lowConductor N ((U+6 : ℕ) : ℝ)⌋₊
    (panSourceG (fun a => (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)) m)
    hmpos hmN hA (by
      have hl0 : 0 ≤ Real.log (N : ℝ) := by linarith only [hlog]
      simpa only [lowConductor, Real.rpow_natCast] using
        (Nat.floor_le (Real.rpow_nonneg hl0 ((U+6 : ℕ) : ℝ)))) (by
      intro a _
      unfold panSourceG
      split_ifs
      · exact hf a
      · simp)
  have hhigh := numerical_high_source_log_saving (U+6) N hNH m
    (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ)) (liuPanSourceIntervalUpper N)
    (fun a => (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)) hAN hA
    (log_rpow_lt_liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ)).le hf
  have he : 6-((U+6 : ℕ) : ℝ) = -(U : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg (show 0 ≤ Real.log (N : ℝ) by linarith only [hlog]),
    Real.rpow_natCast, ← div_eq_mul_inv] at hhigh
  have hDfun : panSourceD m = (fun n => if n.Prime ∧ n.Coprime m then (1 : ℂ) else 0) := by
    funext n
    simp only [panSourceD, and_comm]
  rw [liuPanPrimitiveCofactorLedger_eq_source,
    PanLow.nonprincipalLow_eq_low_add_high _ _ _ _ _ _ _ hD1 hD,
    panModulusCutoff_eq_upper]
  rw [← hDfun] at hlow
  have hr := numerical_pan_high_remainder U N hNR
  calc
    _ ≤ panLowConstant U (U+6)*N/Real.log (N : ℝ)^U +
        (panHighConstant*N/Real.log (N : ℝ)^U + 6984*Real.log (N : ℝ)^2/N) :=
      add_le_add hlow hhigh
    _ ≤ panLowConstant U (U+6)*N/Real.log (N : ℝ)^U +
        (panHighConstant*N/Real.log (N : ℝ)^U + 6984*N/Real.log (N : ℝ)^U) := by
      exact add_le_add le_rfl (add_le_add le_rfl hr)
    _ = _ := by unfold panLedgerConstant; ring

#print axioms numerical_pan_ledger
end ChenEffective
