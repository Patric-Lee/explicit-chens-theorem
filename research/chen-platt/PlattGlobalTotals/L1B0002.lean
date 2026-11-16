import PlattGlobalBoundKernel
import PlattGlobalTotals.L0B0064
import PlattGlobalTotals.L0B0065
import PlattGlobalTotals.L0B0066
import PlattGlobalTotals.L0B0067
import PlattGlobalTotals.L0B0068
import PlattGlobalTotals.L0B0069
import PlattGlobalTotals.L0B0070
import PlattGlobalTotals.L0B0071
import PlattGlobalTotals.L0B0072
import PlattGlobalTotals.L0B0073
import PlattGlobalTotals.L0B0074
namespace ChenEffective.PlattWindow.GlobalTotals.L1B0002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem leaf0 : ReciprocalBound 8530952192 8665169920 192099148226 192099259637 := ChenEffective.PlattWindow.GlobalTotals.L0B0064.bound
theorem leaf1 : ReciprocalBound 8665169920 8799387648 188990216174 188990326013 := ChenEffective.PlattWindow.GlobalTotals.L0B0065.bound
theorem leaf2 : ReciprocalBound 8799387648 8933605376 186020480175 186020588864 := ChenEffective.PlattWindow.GlobalTotals.L0B0066.bound
theorem leaf3 : ReciprocalBound 8933605376 9067823104 183129144843 183129252043 := ChenEffective.PlattWindow.GlobalTotals.L0B0067.bound
theorem leaf4 : ReciprocalBound 9067823104 9199943680 177465520110 177465624400 := ChenEffective.PlattWindow.GlobalTotals.L0B0068.bound
theorem leaf5 : ReciprocalBound 9199943680 9334161408 177725672280 177725777207 := ChenEffective.PlattWindow.GlobalTotals.L0B0069.bound
theorem leaf6 : ReciprocalBound 9334161408 9468379136 174977554312 174977657953 := ChenEffective.PlattWindow.GlobalTotals.L0B0070.bound
theorem leaf7 : ReciprocalBound 9468379136 9602596864 172410605015 172410707765 := ChenEffective.PlattWindow.GlobalTotals.L0B0071.bound
theorem leaf8 : ReciprocalBound 9602596864 9736814592 169984217254 169984318629 := ChenEffective.PlattWindow.GlobalTotals.L0B0072.bound
theorem leaf9 : ReciprocalBound 9736814592 9871032320 167483643715 167483744082 := ChenEffective.PlattWindow.GlobalTotals.L0B0073.bound
theorem leaf10 : ReciprocalBound 9871032320 10000000000 158733813245 158733908919 := ChenEffective.PlattWindow.GlobalTotals.L0B0074.bound
theorem join0 : ReciprocalBound 8530952192 8799387648 381089364400 381089585650 :=
 ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append leaf0 leaf1)
theorem join1 : ReciprocalBound 8799387648 9067823104 369149625018 369149840907 :=
 ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append leaf2 leaf3)
theorem join2 : ReciprocalBound 9067823104 9334161408 355191192390 355191401607 :=
 ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append leaf4 leaf5)
theorem join3 : ReciprocalBound 9334161408 9602596864 347388159327 347388365718 :=
 ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append leaf6 leaf7)
theorem join4 : ReciprocalBound 9602596864 9871032320 337467860969 337468062711 :=
 ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append leaf8 leaf9)
theorem join5 : ReciprocalBound 8530952192 9067823104 750238989418 750239426557 :=
 ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append join0 join1)
theorem join6 : ReciprocalBound 9067823104 9602596864 702579351717 702579767325 :=
 ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append join2 join3)
theorem join7 : ReciprocalBound 9602596864 10000000000 496201674214 496201971630 :=
 ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append join4 leaf10)
theorem join8 : ReciprocalBound 8530952192 9602596864 1452818341135 1452819193882 :=
 ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append join5 join6)
theorem join9 : ReciprocalBound 8530952192 10000000000 1949020015349 1949021165512 :=
 ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append join8 join7)
theorem bound : ReciprocalBound 8530952192 10000000000 1949020015349 1949021165512 := join9
#print axioms bound
end ChenEffective.PlattWindow.GlobalTotals.L1B0002
