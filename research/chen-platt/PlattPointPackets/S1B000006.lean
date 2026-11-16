import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000006
namespace ChenEffective.PlattWindow.PointPackets.S1B000006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts24 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.cuts24
abbrev points24 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.pointBounds24
opaque packet24 : CheckedPointSegment 7077889 5 2048 325955735401 325958657966 10375586941869 10375706839681 cuts24 points24 :=
 ⟨Manual.Count131072.C000024.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000024.count_checked,Manual.Count131072.C000024.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.checked24,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.point_links_checked24⟩
def segment24 : PointSegment := ⟨7077889,5,2048,325955735401,325958657966,10375586941869,10375706839681,cuts24,points24,packet24⟩
abbrev cuts25 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.cuts25
abbrev points25 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.pointBounds25
opaque packet25 : CheckedPointSegment 7208961 5 2048 320782014304 320784838764 10701542677270 10701665497647 cuts25 points25 :=
 ⟨Manual.Count131072.C000025.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000025.count_checked,Manual.Count131072.C000025.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.checked25,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.point_links_checked25⟩
def segment25 : PointSegment := ⟨7208961,5,2048,320782014304,320784838764,10701542677270,10701665497647,cuts25,points25,packet25⟩
abbrev cuts26 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.cuts26
abbrev points26 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.pointBounds26
opaque packet26 : CheckedPointSegment 7340033 5 2048 314040810099 314043526335 11022324691574 11022450336411 cuts26 points26 :=
 ⟨Manual.Count131072.C000026.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000026.count_checked,Manual.Count131072.C000026.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.checked26,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.point_links_checked26⟩
def segment26 : PointSegment := ⟨7340033,5,2048,314040810099,314043526335,11022324691574,11022450336411,cuts26,points26,packet26⟩
abbrev cuts27 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.cuts27
abbrev points27 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.pointBounds27
opaque packet27 : CheckedPointSegment 7471105 5 2048 308718290516 308720914279 11336365501673 11336493862746 cuts27 points27 :=
 ⟨Manual.Count131072.C000027.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000027.count_checked,Manual.Count131072.C000027.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.checked27,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000006.point_links_checked27⟩
def segment27 : PointSegment := ⟨7471105,5,2048,308718290516,308720914279,11336365501673,11336493862746,cuts27,points27,packet27⟩
def segments : List PointSegment := [segment24,segment25,segment26,segment27]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 7077888 10375586941869 10375706839681 7602176 11645083792189 11645214777025 segments = true := by decide +kernel
theorem certified : PointChainCertificate 7077888 10375586941869 10375706839681 7602176 11645083792189 11645214777025 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000006
