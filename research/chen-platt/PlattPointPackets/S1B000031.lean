import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000031
namespace ChenEffective.PlattWindow.PointPackets.S1B000031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts124 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.cuts124
abbrev points124 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.pointBounds124
opaque packet124 : CheckedPointSegment 20185089 6 1024 107469646338 107470326649 28478160092557 28478392987995 cuts124 points124 :=
 ⟨Manual.Count131072.C000124.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000124.count_checked,Manual.Count131072.C000124.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.checked124,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.point_links_checked124⟩
def segment124 : PointSegment := ⟨20185089,6,1024,107469646338,107470326649,28478160092557,28478392987995,cuts124,points124,packet124⟩
abbrev cuts125 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.cuts125
abbrev points125 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.pointBounds125
opaque packet125 : CheckedPointSegment 20316161 6 1024 106657303729 106657974592 28585629738895 28585863314644 cuts125 points125 :=
 ⟨Manual.Count131072.C000125.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000125.count_checked,Manual.Count131072.C000125.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.checked125,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.point_links_checked125⟩
def segment125 : PointSegment := ⟨20316161,6,1024,106657303729,106657974592,28585629738895,28585863314644,cuts125,points125,packet125⟩
abbrev cuts126 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.cuts126
abbrev points126 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.pointBounds126
opaque packet126 : CheckedPointSegment 20447233 6 1024 107182128696 107182798541 28692287042624 28692521289236 cuts126 points126 :=
 ⟨Manual.Count131072.C000126.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000126.count_checked,Manual.Count131072.C000126.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.checked126,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.point_links_checked126⟩
def segment126 : PointSegment := ⟨20447233,6,1024,107182128696,107182798541,28692287042624,28692521289236,cuts126,points126,packet126⟩
abbrev cuts127 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.cuts127
abbrev points127 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.pointBounds127
opaque packet127 : CheckedPointSegment 20578305 6 1024 106745394550 106746057434 28799469171320 28799704087777 cuts127 points127 :=
 ⟨Manual.Count131072.C000127.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000127.count_checked,Manual.Count131072.C000127.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.checked127,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000031.point_links_checked127⟩
def segment127 : PointSegment := ⟨20578305,6,1024,106745394550,106746057434,28799469171320,28799704087777,cuts127,points127,packet127⟩
def segments : List PointSegment := [segment124,segment125,segment126,segment127]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 20185088 28478160092557 28478392987995 20709376 28906214565870 28906450145211 segments = true := by decide +kernel
theorem certified : PointChainCertificate 20185088 28478160092557 28478392987995 20709376 28906214565870 28906450145211 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000031
