import BJSSmallPrefixCertificate

/-! A signed lower-prefix bound on the initial finite range. -/
noncomputable section
namespace ChenEffective
open Real Finset AnalyticNumberTheory.Mertens
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem bjsSmallPrefixQ_cast (n : ℕ) :
    (bjsSmallPrefixQ n : ℝ) = primeReciprocalSum n := by
  simp only [bjsSmallPrefixQ,primeReciprocalSum,primesUpTo,Finset.sum_filter,
    Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

theorem bjsSignedLower_mono {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    log (log x)+mertensSecondConstant-1/(2*(log x)^2) ≤
      log (log y)+mertensSecondConstant-1/(2*(log y)^2) := by
  have hp := log_pos hx
  have hlog := log_le_log (by linarith only [hx]) hxy
  have hll := log_le_log hp hlog
  have hsq : 2*(log x)^2 ≤ 2*(log y)^2 := by nlinarith only [hp,hlog]
  have hi := one_div_le_one_div_of_le (by positivity : 0 < 2*(log x)^2) hsq
  linarith only [hll,hi]

theorem bjsSmallSignedPrefix_endpoint (n : ℕ) (hn : 2 ≤ n) (hu : n < 287) :
    log (log (n+1 : ℝ))+mertensSecondConstant-1/(2*(log (n+1 : ℝ))^2) ≤
      primeReciprocalSum n := by
  obtain ⟨hk,hU,hl,hV,hu1,hP⟩ := bjsSmallPrefixCertificates ⟨n,hu⟩ hn
  let row := bjsSmallLogRows[n]!
  change (2 : ℚ)^row.1 ≤ (n : ℚ)+1 at hk
  change bjsLogUpper ((n : ℚ)+1) row.1 ≤ row.2.1 at hU
  change (2 : ℚ)^row.2.2.1 ≤ row.2.1 at hl
  change bjsLogUpper row.2.1 row.2.2.1 ≤ row.2.2.2 at hV
  change row.2.2.2+27/100-1/(2*row.2.1^2) ≤ bjsSmallPrefixQ n at hP
  have hlogU : log (n+1 : ℝ) ≤ (row.2.1 : ℝ) := by
    have hh := bjsLogUpper_valid ((n : ℚ)+1) row.1 hk
    have hUr : (bjsLogUpper ((n : ℚ)+1) row.1 : ℝ) ≤ (row.2.1 : ℝ) :=
      Rat.cast_le.mpr hU
    simpa only [Rat.cast_add,Rat.cast_natCast,Rat.cast_one] using hh.trans hUr
  have hlogV : log (row.2.1 : ℝ) ≤ (row.2.2.2 : ℝ) :=
    (bjsLogUpper_valid row.2.1 row.2.2.1 hl).trans (by exact_mod_cast hV)
  have hn1 : (1 : ℝ) < n+1 := by exact_mod_cast (show 1 < n+1 by omega)
  have hp := log_pos hn1
  have hll := (log_le_log hp hlogU).trans hlogV
  have hsq : 2*(log (n+1 : ℝ))^2 ≤ 2*(row.2.1 : ℝ)^2 := by nlinarith only [hp,hlogU]
  have hi := one_div_le_one_div_of_le (by positivity : 0 < 2*(log (n+1 : ℝ))^2) hsq
  have hPr : (row.2.2.2 : ℝ)+27/100-1/(2*(row.2.1 : ℝ)^2) ≤ primeReciprocalSum n := by
    rw [← bjsSmallPrefixQ_cast]
    have hh : ((row.2.2.2+27/100-1/(2*row.2.1^2) : ℚ) : ℝ) ≤ (bjsSmallPrefixQ n : ℝ) :=
      Rat.cast_le.mpr hP
    push_cast at hh
    exact hh
  linarith only [hll,hi,hPr,bjsStudy_canonical_mertens_upper]

theorem bjsSmallSignedPrefix_lower {x : ℝ} (hx : 1 < x) (hu : x ≤ 286) :
    log (log x)+mertensSecondConstant-1/(2*(log x)^2) ≤
      primeReciprocalSum ⌊x⌋₊ := by
  by_cases hx2 : x < 2
  · have hp := log_pos hx
    have hl : log x ≤ 1 :=
      (log_le_log (by linarith only [hx]) hx2.le).trans (by linarith only [log_two_lt_d9])
    have hll := log_le_sub_one_of_pos hp
    have hi := one_div_le_one_div_of_le (by positivity : 0 < 2*(log x)^2)
      (show 2*(log x)^2 ≤ 2 by nlinarith only [hp,hl])
    have hnn := primeReciprocalSum_nonneg ⌊x⌋₊
    linarith only [hll,hl,hi,hnn,bjsStudy_canonical_mertens_upper]
  · have hn : 2 ≤ ⌊x⌋₊ := (Nat.le_floor (show (2 : ℝ) ≤ x by linarith only [hx2]))
    have hnle : ⌊x⌋₊ ≤ 286 := Nat.floor_le_of_le hu
    have hnx : x ≤ (⌊x⌋₊ : ℝ)+1 := (Nat.lt_floor_add_one x).le
    exact (bjsSignedLower_mono hx hnx).trans
      (bjsSmallSignedPrefix_endpoint ⌊x⌋₊ hn (by omega))

#print axioms bjsSmallSignedPrefix_lower
end ChenEffective
