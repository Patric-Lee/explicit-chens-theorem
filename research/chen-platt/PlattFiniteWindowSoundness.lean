import PlattGlobalGridSoundness
import PlattCertificates.Log256.C000936

noncomputable section
namespace ChenEffective.PlattWindow
open Real AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000

theorem certified_reference_log :
    (882879348526828:ℝ)≤(2:ℝ)^48*log (log (10000000000:ℝ)) ∧
    (2:ℝ)^48*log (log (10000000000:ℝ))≤(882879348527041:ℝ) := by
  have h := LogCertificate.checkedRows_sound Manual.Log256.C000936.rows
    Manual.Log256.C000936.checked (Manual.Log256.C000936.rows[249])
    (List.getElem_mem (by decide))
  change (882879348526828:ℝ)≤(LogCertificate.scale:ℝ)*log (log (10000000000:ℝ)) ∧
    (LogCertificate.scale:ℝ)*log (log (10000000000:ℝ))≤(882879348527041:ℝ) at h
  simpa only [LogCertificate.scale,Nat.cast_pow,Nat.cast_ofNat] using h

theorem finite_relative_window_of_certificates {primePoints gridPoints : List PrimePoint}
    (hprime : PointChainCertificate 4000000 0 0 10000000000
      116863011702975 116863401833309 primePoints)
    (hgrid : GridWindowCertificate 4000000 10000000000 gridPoints)
    (hcover : ∀p∈gridPoints,p∈primePoints)
    (x : ℝ) (hx : 4000000≤x) (hxb : x≤(10:ℝ)^10) :
    |relativePrefix x ((10:ℝ)^10)|≤1/20000 := by
  have hzero : ScaledPrimeBound 4000000 4000000 0 0 := by
    simp [ScaledPrimeBound]
  have hp := pointChainCertificate_sound hprime hzero
  have hpoints : ∀ p∈gridPoints,ScaledPrimeBound 4000000 p.1 p.2.1 p.2.2 := by
    intro p hmem
    exact hp.1 p (hcover p hmem)
  by_cases he : x=(10000000000:ℝ)
  · rw [he,show (10:ℝ)^10=(10000000000:ℝ) by norm_num]
    simp only [relativePrefix,sub_self,abs_zero]
    norm_num
  · have hb : x<(10000000000:ℝ) := lt_of_le_of_ne (by norm_num at hxb; exact hxb) he
    simpa only [show (10:ℝ)^10=10000000000 by norm_num] using
      gridWindowCertificate_sound hgrid hpoints hp.2 certified_reference_log x hx hb

#print axioms certified_reference_log
#print axioms finite_relative_window_of_certificates
end ChenEffective.PlattWindow
