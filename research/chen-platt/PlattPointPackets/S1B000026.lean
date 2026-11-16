import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000026
namespace ChenEffective.PlattWindow.PointPackets.S1B000026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts104 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.cuts104
abbrev points104 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.pointBounds104
opaque packet104 : CheckedPointSegment 17563649 6 1024 125178079612 125178989536 26141253961826 26141470936592 cuts104 points104 :=
 ⟨Manual.Count131072.C000104.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000104.count_checked,Manual.Count131072.C000104.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.checked104,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.point_links_checked104⟩
def segment104 : PointSegment := ⟨17563649,6,1024,125178079612,125178989536,26141253961826,26141470936592,cuts104,points104,packet104⟩
abbrev cuts105 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.cuts105
abbrev points105 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.pointBounds105
opaque packet105 : CheckedPointSegment 17694721 6 1024 124093505895 124094401258 26266432041438 26266649926128 cuts105 points105 :=
 ⟨Manual.Count131072.C000105.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000105.count_checked,Manual.Count131072.C000105.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.checked105,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.point_links_checked105⟩
def segment105 : PointSegment := ⟨17694721,6,1024,124093505895,124094401258,26266432041438,26266649926128,cuts105,points105,packet105⟩
abbrev cuts106 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.cuts106
abbrev points106 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.pointBounds106
opaque packet106 : CheckedPointSegment 17825793 6 1024 123842821567 123843708559 26390525547333 26390744327386 cuts106 points106 :=
 ⟨Manual.Count131072.C000106.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000106.count_checked,Manual.Count131072.C000106.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.checked106,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.point_links_checked106⟩
def segment106 : PointSegment := ⟨17825793,6,1024,123842821567,123843708559,26390525547333,26390744327386,cuts106,points106,packet106⟩
abbrev cuts107 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.cuts107
abbrev points107 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.pointBounds107
opaque packet107 : CheckedPointSegment 17956865 6 1024 121528516183 121529380370 26514368368900 26514588035945 cuts107 points107 :=
 ⟨Manual.Count131072.C000107.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000107.count_checked,Manual.Count131072.C000107.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.checked107,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000026.point_links_checked107⟩
def segment107 : PointSegment := ⟨17956865,6,1024,121528516183,121529380370,26514368368900,26514588035945,cuts107,points107,packet107⟩
def segments : List PointSegment := [segment104,segment105,segment106,segment107]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 17563648 26141253961826 26141470936592 18087936 26635896885083 26636117416315 segments = true := by decide +kernel
theorem certified : PointChainCertificate 17563648 26141253961826 26141470936592 18087936 26635896885083 26636117416315 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000026
