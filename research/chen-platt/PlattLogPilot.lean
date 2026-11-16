import PlattLogSoundness
import PlattLogPilotData
namespace ChenEffective.PlattWindow.LogCertificate
set_option maxRecDepth 100000
theorem pilot_loglog_bound :
    (882879269665140:ℝ) ≤ (2:ℝ)^48*Real.log (Real.log 9999935488) ∧
    (2:ℝ)^48*Real.log (Real.log 9999935488) ≤ (882879269665353:ℝ) := by
  have h := pilot_log_arithmetic
  simp only [Bool.and_eq_true] at h
  have hfirst : rationalBounds 9999935488 1 33=(6481199038390416,6481199038391538) :=
    Prod.ext (Nat.eq_of_beq_eq_true h.1.1.1) (Nat.eq_of_beq_eq_true h.1.1.2)
  have hlo := Nat.eq_of_beq_eq_true h.1.2
  have hhi := Nat.eq_of_beq_eq_true h.2
  have hr := loglog_of_certificates (x:=9999935488) (k:=33) (kl:=4) (ku:=4)
    (by norm_num) (by norm_num) (by norm_num) hfirst (by norm_num [scale])
    (by norm_num [scale]) (by norm_num [scale]) (by norm_num [scale]) (by norm_num [scale]) hlo hhi
  norm_num only [scale,Nat.cast_pow,Nat.cast_ofNat] at hr ⊢
  exact hr
#print axioms pilot_loglog_bound
end ChenEffective.PlattWindow.LogCertificate
