import GRH14PanEndpoints

noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def panLedgerConstant (_U : ℕ) : ℝ := 4+panHighConstant+6984
def panPrincipalConstant (_s : ℕ) : ℝ := 4
theorem panLedgerConstant_pos (U : ℕ) : 0<panLedgerConstant U := by
  unfold panLedgerConstant panHighConstant panCellConstant panShortConstant panLongConstant
  have := panSharpConstant_pos
  positivity
theorem panPrincipalConstant_pos (s : ℕ) : 0<panPrincipalConstant s := by norm_num [panPrincipalConstant]
theorem numerical_pan_ledger (U N : ℕ) (hN : targetCutoff ≤ N) (hU : U≤32)
    (m : ℕ) (hm : m ∈ Icc 1 (panModulusCutoff N ((U+6 : ℕ) : ℝ))) :
    liuPanPrimitiveCofactorLedger N (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ))
      (liuPanSourceIntervalUpper N) (panModulusCutoff N ((U+6 : ℕ) : ℝ)) m
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
        panLedgerConstant U*N/Real.log (N : ℝ)^U := by
  have hNH : panHighThreshold (U+6)≤N := by
    unfold panHighThreshold
    exact pan_log_cutoff_at_target (by omega) hN
  have hNR : logPowerCutoff (U+2)≤N := pan_log_cutoff_at_target (by omega) hN
  obtain ⟨hlog, hD1, hD, hDN, hcut⟩ := H30.numerical_pan_conductor_bounds (U+6) N hNH
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
  have hlow := pan_low_at_target U (U+6) N hN hU (by omega) m
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
  have hr := H30.numerical_pan_high_remainder U N hNR
  calc
    _ ≤ 4*N/Real.log (N : ℝ)^U +
        (panHighConstant*N/Real.log (N : ℝ)^U + 6984*Real.log (N : ℝ)^2/N) :=
      add_le_add hlow hhigh
    _ ≤ 4*N/Real.log (N : ℝ)^U +
        (panHighConstant*N/Real.log (N : ℝ)^U + 6984*N/Real.log (N : ℝ)^U) := by
      exact add_le_add le_rfl (add_le_add le_rfl hr)
    _ = _ := by unfold panLedgerConstant; ring


#print axioms numerical_pan_ledger
end ChenEffective.GRH14
