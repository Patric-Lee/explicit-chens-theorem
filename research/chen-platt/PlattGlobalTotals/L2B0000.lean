import PlattGlobalBoundKernel
import PlattGlobalTotals.L1B0000
import PlattGlobalTotals.L1B0001
import PlattGlobalTotals.L1B0002
namespace ChenEffective.PlattWindow.GlobalTotals.L2B0000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem leaf0 : ReciprocalBound 4000000 4242276352 106180664081439 106181047940154 := ChenEffective.PlattWindow.GlobalTotals.L1B0000.bound
theorem leaf1 : ReciprocalBound 4242276352 8530952192 8733327606187 8733332727643 := ChenEffective.PlattWindow.GlobalTotals.L1B0001.bound
theorem leaf2 : ReciprocalBound 8530952192 10000000000 1949020015349 1949021165512 := ChenEffective.PlattWindow.GlobalTotals.L1B0002.bound
theorem join0 : ReciprocalBound 4000000 8530952192 114913991687626 114914380667797 :=
 ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append leaf0 leaf1)
theorem join1 : ReciprocalBound 4000000 10000000000 116863011702975 116863401833309 :=
 ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append join0 leaf2)
theorem bound : ReciprocalBound 4000000 10000000000 116863011702975 116863401833309 := join1
#print axioms bound
end ChenEffective.PlattWindow.GlobalTotals.L2B0000
