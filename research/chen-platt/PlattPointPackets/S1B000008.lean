import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000008
namespace ChenEffective.PlattWindow.PointPackets.S1B000008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts32 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.cuts32
abbrev points32 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.pointBounds32
opaque packet32 : CheckedPointSegment 8126465 5 2048 282746462936 282748674018 12826933549621 12827074168142 cuts32 points32 :=
 ⟨Manual.Count131072.C000032.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000032.count_checked,Manual.Count131072.C000032.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.checked32,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.point_links_checked32⟩
def segment32 : PointSegment := ⟨8126465,5,2048,282746462936,282748674018,12826933549621,12827074168142,cuts32,points32,packet32⟩
abbrev cuts33 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.cuts33
abbrev points33 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.pointBounds33
opaque packet33 : CheckedPointSegment 8257537 5 2048 278062634428 278064774738 13109680012557 13109822842160 cuts33 points33 :=
 ⟨Manual.Count131072.C000033.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000033.count_checked,Manual.Count131072.C000033.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.checked33,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.point_links_checked33⟩
def segment33 : PointSegment := ⟨8257537,5,2048,278062634428,278064774738,13109680012557,13109822842160,cuts33,points33,packet33⟩
abbrev cuts34 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.cuts34
abbrev points34 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.pointBounds34
opaque packet34 : CheckedPointSegment 8388609 5 2048 273078100281 273080169640 13387742646985 13387887616898 cuts34 points34 :=
 ⟨Manual.Count131072.C000034.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000034.count_checked,Manual.Count131072.C000034.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.checked34,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.point_links_checked34⟩
def segment34 : PointSegment := ⟨8388609,5,2048,273078100281,273080169640,13387742646985,13387887616898,cuts34,points34,packet34⟩
abbrev cuts35 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.cuts35
abbrev points35 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.pointBounds35
opaque packet35 : CheckedPointSegment 8519681 5 2048 270628334316 270630353969 13660820747266 13660967786538 cuts35 points35 :=
 ⟨Manual.Count131072.C000035.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000035.count_checked,Manual.Count131072.C000035.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.checked35,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000008.point_links_checked35⟩
def segment35 : PointSegment := ⟨8519681,5,2048,270628334316,270630353969,13660820747266,13660967786538,cuts35,points35,packet35⟩
def segments : List PointSegment := [segment32,segment33,segment34,segment35]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 8126464 12826933549621 12827074168142 8650752 13931449081582 13931598140507 segments = true := by decide +kernel
theorem certified : PointChainCertificate 8126464 12826933549621 12827074168142 8650752 13931449081582 13931598140507 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000008
