import GRH14TruncationBudget
import GRHTruncatedSieveBounds

noncomputable section
namespace ChenEffective.GRH14
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

noncomputable def lowerDelta (N q : ℕ) : ℝ :=
  (N:ℝ)^(249/500:ℝ)/(2*(q:ℝ)*(preSieveTruncation N:ℝ))
noncomputable def lowerLevel (N q : ℕ) : ℕ := Nat.floor (lowerDelta N q)+1
noncomputable def lowerRatio (N q : ℕ) : ℝ :=
  log (lowerDelta N q)/log ((N:ℝ)^(1/10:ℝ))

theorem truncation_log_upper {N : ℕ} (hN : targetCutoff ≤ N) :
    log (preSieveTruncation N:ℝ) ≤ log (N:ℝ)/200 := by
  have hn : 0<N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hc : (0:ℝ)<preSieveTruncation N := by
    exact_mod_cast (truncation_log_lower hN).1
  have hh := log_le_log hc (Nat.floor_le (rpow_nonneg (Nat.cast_nonneg N) (1/200:ℝ)))
  rw [log_rpow hnR] at hh
  convert hh using 1 <;> ring

theorem lower_ratio_shift {N q : ℕ} (hN : targetCutoff ≤ N) (hq : 0<q) :
    0 ≤ (5-10*(log (q:ℝ)/log (N:ℝ)))-lowerRatio N q ∧
    (5-10*(log (q:ℝ)/log (N:ℝ)))-lowerRatio N q ≤ 71/1000 := by
  have hL := target_log_lower hN
  have hLp : 0<log (N:ℝ) := by linarith only [hL]
  have hn : 0<N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hc : (0:ℝ)<preSieveTruncation N := by exact_mod_cast (truncation_log_lower hN).1
  have hcl : 0 ≤ log (preSieveTruncation N:ℝ) :=
    log_nonneg (by exact_mod_cast (truncation_log_lower hN).1)
  have hcu := truncation_log_upper hN
  have hl2 : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  have hl2u : log (2:ℝ) ≤ 1 := by
    linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have heq : (5-10*(log (q:ℝ)/log (N:ℝ)))-lowerRatio N q =
      (1/50:ℝ)+10*(log 2+log (preSieveTruncation N:ℝ))/log (N:ℝ) := by
    unfold lowerRatio lowerDelta
    rw [log_div (rpow_pos_of_pos hnR _).ne' (by positivity),
      log_mul (by positivity : (2:ℝ)*q ≠ 0) hc.ne',
      log_mul (by norm_num : (2:ℝ) ≠ 0) hqR.ne',log_rpow hnR,log_rpow hnR]
    field_simp [hLp.ne']
    ring
  rw [heq]
  constructor
  · positivity
  · have hh : 10*(log 2+log (preSieveTruncation N:ℝ))/log (N:ℝ) ≤ 51/1000 := by
      apply (div_le_iff₀ hLp).mpr
      linarith only [hcu,hL,hl2u]
    linarith only [hh]

theorem lower_endpoint_parameters {N : ℕ} (hN : targetCutoff ≤ N) :
    2<N ∧ (2:ℝ) ≤ (N:ℝ)^(1/10:ℝ) := by
  have hL := target_log_lower hN
  have hn : 0<N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hh := log_le_sub_one_of_pos hnR
  constructor
  · exact_mod_cast (by linarith only [hh,hL] : (2:ℝ)<N)
  · apply (log_le_log_iff (by norm_num) (rpow_pos_of_pos hnR _)).mp
    rw [log_rpow hnR]
    linarith only [hL,log_two_lt_d9]

theorem lower_base_ratio {N : ℕ} (hN : targetCutoff ≤ N) :
    (4929/1000:ℝ) ≤ lowerRatio N 1 ∧ lowerRatio N 1 ≤ 5 := by
  have hh := lower_ratio_shift hN (q:=1) (by norm_num)
  norm_num only [Nat.cast_one,log_one,zero_div,mul_zero,sub_zero] at hh
  constructor <;> linarith only [hh.1,hh.2]

theorem lower_medium_ratio {N q : ℕ} (hN : targetCutoff ≤ N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
    (3/2:ℝ) ≤ lowerRatio N q ∧ lowerRatio N q ≤ 4 := by
  have hNp := (lower_endpoint_parameters hN).1
  have hqp := (mem_filter.mp hq).2.1.pos
  have hh := lower_ratio_shift hN hqp
  have hc := jurkatRichertSourceMediumPrime_log_mem (by omega : 1<N) hq
  constructor <;> linarith only [hh.1,hh.2,hc.1,hc.2]

theorem lower_level_geometry {N q : ℕ} (hN : targetCutoff ≤ N) (hq : 0<q)
    (hs : 3/2 ≤ lowerRatio N q) :
    let D := lowerLevel N q
    let Z := Nat.ceil ((D:ℝ)^(1/lowerRatio N q))
    1<D ∧ Z≤D ∧ ((N:ℝ)^(1/10:ℝ)) < (D:ℝ)^(1/lowerRatio N q) ∧
      ((q*preSieveTruncation N*D:ℕ):ℝ) ≤ (N:ℝ)^(249/500:ℝ) := by
  have hz := (lower_endpoint_parameters hN).2
  have hn : 0<N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hc : (0:ℝ)<preSieveTruncation N := by exact_mod_cast (truncation_log_lower hN).1
  have hdel : 0<lowerDelta N q := by unfold lowerDelta; positivity
  obtain ⟨hD,hDelta,hroot,hZ⟩ := real_level_to_natCeil_geometry hz hdel rfl hs
  change 2≤lowerLevel N q at hD
  refine ⟨by exact hD,?_,hroot,?_⟩
  · apply Nat.ceil_le.mpr
    exact rpow_le_self_of_one_le (by exact_mod_cast (show 1≤lowerLevel N q by omega))
      ((div_le_one (by linarith only [hs] : 0<lowerRatio N q)).mpr (by linarith only [hs]))
  · have hlz : 0<log ((N:ℝ)^(1/10:ℝ)) := log_pos (by linarith only [hz])
    have hlog : 0<log (lowerDelta N q) := by
      have hh := (le_div_iff₀ hlz).mp hs
      nlinarith only [hh,hlz]
    have hd1 : 1≤lowerDelta N q := (log_pos_iff hdel.le).mp hlog |>.le
    have hf := Nat.floor_le hdel.le
    have hid : ((q:ℝ)*preSieveTruncation N)*(lowerDelta N q)=(N:ℝ)^(249/500:ℝ)/2 := by
      unfold lowerDelta
      field_simp
    have hprod := mul_le_mul_of_nonneg_left hf (le_of_lt (mul_pos hqR hc))
    have hsmall := mul_le_mul_of_nonneg_left hd1 (le_of_lt (mul_pos hqR hc))
    change ((q*preSieveTruncation N*(Nat.floor (lowerDelta N q)+1):ℕ):ℝ) ≤ _
    push_cast
    nlinarith only [hid,hprod,hsmall]

theorem lower_level_le_endpoint {N q : ℕ} (hN : targetCutoff ≤ N) (hq : 0<q)
    (hs : 3/2≤lowerRatio N q) : lowerLevel N q≤N := by
  have hg := (lower_level_geometry hN hq hs).2.2.2
  have hc := (truncation_log_lower hN).1
  have hmult : lowerLevel N q≤q*preSieveTruncation N*lowerLevel N q := by
    have hh := Nat.mul_le_mul_right (lowerLevel N q) (show 1≤q*preSieveTruncation N from Nat.mul_pos hq hc)
    simpa only [one_mul] using hh
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by have := (lower_endpoint_parameters hN).1; omega)
  have hpow : (N:ℝ)^(249/500:ℝ)≤N := rpow_le_self_of_one_le hN1 (by norm_num)
  have hmreal : (lowerLevel N q:ℝ)≤((q*preSieveTruncation N*lowerLevel N q:ℕ):ℝ) := by exact_mod_cast hmult
  exact_mod_cast hmreal.trans (hg.trans hpow)

theorem lower_level_in_source {N q : ℕ} (hN : targetCutoff ≤ N) (hq : 0<q)
    (hs : 3/2≤lowerRatio N q) :
    preSieveTruncation N*lowerLevel N q≤jurkatRichertSourceUpperLevel N q (1/500:ℝ) := by
  have hg := (lower_level_geometry hN hq hs).2.2.2
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hh : ((preSieveTruncation N*lowerLevel N q:ℕ):ℝ)≤(N:ℝ)^(249/500:ℝ)/(q:ℝ) := by
    apply (le_div_iff₀ hqR).mpr
    simpa only [Nat.cast_mul,mul_assoc,mul_comm,mul_left_comm] using hg
  unfold jurkatRichertSourceUpperLevel
  norm_num only [show (1/2-(1/500:ℝ))=(249/500:ℝ) by norm_num]
  exact (Nat.le_floor hh).trans (Nat.le_succ _)

#print axioms lower_level_geometry
end ChenEffective.GRH14
