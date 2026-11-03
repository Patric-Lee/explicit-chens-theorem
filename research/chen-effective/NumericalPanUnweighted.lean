import NumericalPanLedger
import NumericalPanPrincipal
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanUnweightedUnconditional

noncomputable section
namespace ChenEffective
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def panUnweightedConstant (A : ℕ) : ℝ := 4*(panLedgerConstant (A+2)+panPrincipalConstant (A+2))
@[irreducible] def panUnweightedThreshold (A : ℕ) : ℕ :=
  max (panLedgerThreshold (A+2)) (panPrincipalThreshold (A+2))

theorem panUnweightedConstant_pos (A : ℕ) : 0 < panUnweightedConstant A := by
  unfold panUnweightedConstant
  have := panLedgerConstant_pos (A+2)
  have := panPrincipalConstant_pos (A+2)
  positivity

theorem numerical_pan_unweighted (A N : ℕ) (hN : panUnweightedThreshold A ≤ N) :
    liuPanUnweightedTheorem2Sum (2/Real.log 2) N ((A+8 : ℕ) : ℝ) ≤
      panUnweightedConstant A*N/Real.log (N : ℝ)^(A : ℝ) := by
  have hn := hN
  unfold panUnweightedThreshold at hn
  obtain ⟨hNk, hNp⟩ := max_le_iff.mp hn
  have hg := hNk
  unfold panLedgerThreshold at hg
  have hhigh : NumericalPanHigh.panHighThreshold (A+8) ≤ N := by
    simpa only [Nat.add_assoc] using (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  obtain ⟨hlog, _, _, hDroot, hDN⟩ := numerical_pan_conductor_bounds (A+8) N hhigh
  let K := panLedgerConstant (A+2)
  let P := panPrincipalConstant (A+2)
  have hK : 0 < K := panLedgerConstant_pos _
  have hP : 0 < P := panPrincipalConstant_pos _
  have hpaid := numerical_pan_actual_paid_principal (A+2) N hNp
  let D := panModulusCutoff N ((A+8 : ℕ) : ℝ)
  let M := K * N / Real.log (N : ℝ) ^ (((A+2 : ℕ) : ℝ))
  let T := P * N / Real.log (N : ℝ) ^ (((A+2 : ℕ) : ℝ))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hmass := liuPanActualNonprincipal_sum_le_log_sq N (liuPanSourceIntervalLower N ((A+8 : ℕ) : ℝ))
    (liuPanSourceIntervalUpper N) D (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
    M hM hDN (by
      simpa only [M, K, D, Real.rpow_natCast, Nat.add_assoc, Nat.reduceAdd] using
        numerical_pan_ledger (A+2) N hNk)
  have hprincipal : T * ∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ ≤
      T * (1 + Real.log (N : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left (PanCofactor.reciprocal_totient_mass_le_log_sq hDN) hT
  calc
    _ ≤ ∑ q ∈ Icc 1 D, liuPanActualError (2 / Real.log 2) N ((A+8 : ℕ) : ℝ) q :=
      liuPanUnweightedTheorem2Sum_le_closed _ _ _
    _ ≤ ∑ q ∈ Icc 1 D,
        (liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N ((A+8 : ℕ) : ℝ))
          (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) + T) /
            q.totient := by
      apply sum_le_sum
      intro q hq
      simpa only [T, P, Real.rpow_natCast] using hpaid ((A+8 : ℕ) : ℝ) q (mem_Icc.mp hq).1
        ((by exact_mod_cast (mem_Icc.mp hq).2 : (q : ℝ) ≤ D).trans hDroot)
    _ = (∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ *
        liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N ((A+8 : ℕ) : ℝ))
          (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) +
        T * ∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ := by
      simp only [add_div, sum_add_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ M * (1 + Real.log (N : ℝ)) ^ 2 + T * (1 + Real.log (N : ℝ)) ^ 2 :=
      add_le_add hmass hprincipal
    _ = ((K + P) * N / Real.log (N : ℝ) ^ (((A+2 : ℕ) : ℝ))) * (1 + Real.log (N : ℝ)) ^ 2 := by
      dsimp [M, T]
      ring
    _ ≤ _ := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, panUnweightedConstant] using
        pan_log_sq_payment N (A : ℝ) (K + P) (by positivity) hlog

#print axioms numerical_pan_unweighted
end ChenEffective
