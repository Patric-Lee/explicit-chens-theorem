import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000013
namespace ChenEffective.PlattWindow.PointPackets.S1B000013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts52 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.cuts52
abbrev points52 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.pointBounds52
opaque packet52 : CheckedPointSegment 10747905 5 2048 209775078269 209776321897 17730007559582 17730181918197 cuts52 points52 :=
 ⟨Manual.Count131072.C000052.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000052.count_checked,Manual.Count131072.C000052.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.checked52,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.point_links_checked52⟩
def segment52 : PointSegment := ⟨10747905,5,2048,209775078269,209776321897,17730007559582,17730181918197,cuts52,points52,packet52⟩
abbrev cuts53 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.cuts53
abbrev points53 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.pointBounds53
opaque packet53 : CheckedPointSegment 10878977 5 2048 208144191524 208145410806 17939782637851 17939958240094 cuts53 points53 :=
 ⟨Manual.Count131072.C000053.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000053.count_checked,Manual.Count131072.C000053.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.checked53,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.point_links_checked53⟩
def segment53 : PointSegment := ⟨10878977,5,2048,208144191524,208145410806,17939782637851,17939958240094,cuts53,points53,packet53⟩
abbrev cuts54 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.cuts54
abbrev points54 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.pointBounds54
opaque packet54 : CheckedPointSegment 11010049 5 2048 205223696302 205224884262 18147926829375 18148103650900 cuts54 points54 :=
 ⟨Manual.Count131072.C000054.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000054.count_checked,Manual.Count131072.C000054.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.checked54,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.point_links_checked54⟩
def segment54 : PointSegment := ⟨11010049,5,2048,205223696302,205224884262,18147926829375,18148103650900,cuts54,points54,packet54⟩
abbrev cuts55 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.cuts55
abbrev points55 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.pointBounds55
opaque packet55 : CheckedPointSegment 11141121 5 2048 203053417501 203054579244 18353150525677 18353328535162 cuts55 points55 :=
 ⟨Manual.Count131072.C000055.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000055.count_checked,Manual.Count131072.C000055.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.checked55,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000013.point_links_checked55⟩
def segment55 : PointSegment := ⟨11141121,5,2048,203053417501,203054579244,18353150525677,18353328535162,cuts55,points55,packet55⟩
def segments : List PointSegment := [segment52,segment53,segment54,segment55]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 10747904 17730007559582 17730181918197 11272192 18556203943178 18556383114406 segments = true := by decide +kernel
theorem certified : PointChainCertificate 10747904 17730007559582 17730181918197 11272192 18556203943178 18556383114406 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000013
