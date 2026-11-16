import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000025
namespace ChenEffective.PlattWindow.PointPackets.S1B000025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts100 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.cuts100
abbrev points100 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.pointBounds100
opaque packet100 : CheckedPointSegment 17039361 6 1024 128686361219 128687325258 25628703981254 25628917159518 cuts100 points100 :=
 ⟨Manual.Count131072.C000100.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000100.count_checked,Manual.Count131072.C000100.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.checked100,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.point_links_checked100⟩
def segment100 : PointSegment := ⟨17039361,6,1024,128686361219,128687325258,25628703981254,25628917159518,cuts100,points100,packet100⟩
abbrev cuts101 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.cuts101
abbrev points101 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.pointBounds101
opaque packet101 : CheckedPointSegment 17170433 6 1024 128209130666 128210083815 25757390342473 25757604484776 cuts101 points101 :=
 ⟨Manual.Count131072.C000101.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000101.count_checked,Manual.Count131072.C000101.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.checked101,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.point_links_checked101⟩
def segment101 : PointSegment := ⟨17170433,6,1024,128209130666,128210083815,25757390342473,25757604484776,cuts101,points101,packet101⟩
abbrev cuts102 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.cuts102
abbrev points102 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.pointBounds102
opaque packet102 : CheckedPointSegment 17301505 6 1024 128493773454 128494721547 25885599473139 25885814568591 cuts102 points102 :=
 ⟨Manual.Count131072.C000102.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000102.count_checked,Manual.Count131072.C000102.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.checked102,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.point_links_checked102⟩
def segment102 : PointSegment := ⟨17301505,6,1024,128493773454,128494721547,25885599473139,25885814568591,cuts102,points102,packet102⟩
abbrev cuts103 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.cuts103
abbrev points103 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.pointBounds103
opaque packet103 : CheckedPointSegment 17432577 6 1024 127160715233 127161646454 26014093246593 26014309290138 cuts103 points103 :=
 ⟨Manual.Count131072.C000103.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000103.count_checked,Manual.Count131072.C000103.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.checked103,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000025.point_links_checked103⟩
def segment103 : PointSegment := ⟨17432577,6,1024,127160715233,127161646454,26014093246593,26014309290138,cuts103,points103,packet103⟩
def segments : List PointSegment := [segment100,segment101,segment102,segment103]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 17039360 25628703981254 25628917159518 17563648 26141253961826 26141470936592 segments = true := by decide +kernel
theorem certified : PointChainCertificate 17039360 25628703981254 25628917159518 17563648 26141253961826 26141470936592 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000025
