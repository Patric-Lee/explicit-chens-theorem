import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000000
namespace ChenEffective.PlattWindow.PointPackets.S1B000000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts0 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.cuts0
abbrev points0 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.pointBounds0
opaque packet0 : CheckedPointSegment 4000001 4 4096 598080220703 598084933579 0 0 cuts0 points0 :=
 ⟨Manual.Count131072.C000000.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000000.count_checked,Manual.Count131072.C000000.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.checked0,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.point_links_checked0⟩
def segment0 : PointSegment := ⟨4000001,4,4096,598080220703,598084933579,0,0,cuts0,points0,packet0⟩
abbrev cuts1 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.cuts1
abbrev points1 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.pointBounds1
opaque packet1 : CheckedPointSegment 4131073 4 1976 281556403798 281558570197 598080220703 598084933579 cuts1 points1 :=
 ⟨Manual.Count131072.C000001.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000001.count_checked,Manual.Count131072.C000001.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.checked1,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.point_links_checked1⟩
def segment1 : PointSegment := ⟨4131073,4,1976,281556403798,281558570197,598080220703,598084933579,cuts1,points1,packet1⟩
abbrev cuts2 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.cuts2
abbrev points2 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.pointBounds2
opaque packet2 : CheckedPointSegment 4194305 5 2048 563436548591 563445017565 879636624501 879643503776 cuts2 points2 :=
 ⟨Manual.Count131072.C000002.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000002.count_checked,Manual.Count131072.C000002.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.checked2,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.point_links_checked2⟩
def segment2 : PointSegment := ⟨4194305,5,2048,563436548591,563445017565,879636624501,879643503776,cuts2,points2,packet2⟩
abbrev cuts3 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.cuts3
abbrev points3 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.pointBounds3
opaque packet3 : CheckedPointSegment 4325377 5 2048 552068910285 552076959834 1443073173092 1443088521341 cuts3 points3 :=
 ⟨Manual.Count131072.C000003.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000003.count_checked,Manual.Count131072.C000003.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.checked3,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000000.point_links_checked3⟩
def segment3 : PointSegment := ⟨4325377,5,2048,552068910285,552076959834,1443073173092,1443088521341,cuts3,points3,packet3⟩
def segments : List PointSegment := [segment0,segment1,segment2,segment3]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 4000000 0 0 4456448 1995142083377 1995165481175 segments = true := by decide +kernel
theorem certified : PointChainCertificate 4000000 0 0 4456448 1995142083377 1995165481175 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000000
