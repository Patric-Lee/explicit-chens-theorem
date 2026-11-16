import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000022
namespace ChenEffective.PlattWindow.PointPackets.S1B000022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts88 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.cuts88
abbrev points88 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.pointBounds88
opaque packet88 : CheckedPointSegment 15466497 5 2048 144976783557 144977382976 23984454587918 23984660260855 cuts88 points88 :=
 ⟨Manual.Count131072.C000088.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000088.count_checked,Manual.Count131072.C000088.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.checked88,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.point_links_checked88⟩
def segment88 : PointSegment := ⟨15466497,5,2048,144976783557,144977382976,23984454587918,23984660260855,cuts88,points88,packet88⟩
abbrev cuts89 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.cuts89
abbrev points89 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.pointBounds89
opaque packet89 : CheckedPointSegment 15597569 5 2048 141842128640 141842710259 24129431371475 24129637643831 cuts89 points89 :=
 ⟨Manual.Count131072.C000089.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000089.count_checked,Manual.Count131072.C000089.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.checked89,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.point_links_checked89⟩
def segment89 : PointSegment := ⟨15597569,5,2048,141842128640,141842710259,24129431371475,24129637643831,cuts89,points89,packet89⟩
abbrev cuts90 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.cuts90
abbrev points90 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.pointBounds90
opaque packet90 : CheckedPointSegment 15728641 5 2048 141285789900 141286364427 24271273500115 24271480354090 cuts90 points90 :=
 ⟨Manual.Count131072.C000090.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000090.count_checked,Manual.Count131072.C000090.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.checked90,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.point_links_checked90⟩
def segment90 : PointSegment := ⟨15728641,5,2048,141285789900,141286364427,24271273500115,24271480354090,cuts90,points90,packet90⟩
abbrev cuts91 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.cuts91
abbrev points91 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.pointBounds91
opaque packet91 : CheckedPointSegment 15859713 5 2048 139737653444 139738217089 24412559290015 24412766718517 cuts91 points91 :=
 ⟨Manual.Count131072.C000091.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000091.count_checked,Manual.Count131072.C000091.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.checked91,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000022.point_links_checked91⟩
def segment91 : PointSegment := ⟨15859713,5,2048,139737653444,139738217089,24412559290015,24412766718517,cuts91,points91,packet91⟩
def segments : List PointSegment := [segment88,segment89,segment90,segment91]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 15466496 23984454587918 23984660260855 15990784 24552296943459 24552504935606 segments = true := by decide +kernel
theorem certified : PointChainCertificate 15466496 23984454587918 23984660260855 15990784 24552296943459 24552504935606 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000022
