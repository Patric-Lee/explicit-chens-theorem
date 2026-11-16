import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000005
namespace ChenEffective.PlattWindow.PointPackets.S1B000005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts20 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.cuts20
abbrev points20 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.pointBounds20
opaque packet20 : CheckedPointSegment 6553601 5 2048 354469345955 354472775772 8994199215082 8994306120453 cuts20 points20 :=
 ⟨Manual.Count131072.C000020.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000020.count_checked,Manual.Count131072.C000020.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.checked20,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.point_links_checked20⟩
def segment20 : PointSegment := ⟨6553601,5,2048,354469345955,354472775772,8994199215082,8994306120453,cuts20,points20,packet20⟩
abbrev cuts21 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.cuts21
abbrev points21 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.pointBounds21
opaque packet21 : CheckedPointSegment 6684673 5 2048 348787927287 348791236606 9348668561037 9348778896225 cuts21 points21 :=
 ⟨Manual.Count131072.C000021.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000021.count_checked,Manual.Count131072.C000021.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.checked21,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.point_links_checked21⟩
def segment21 : PointSegment := ⟨6684673,5,2048,348787927287,348791236606,9348668561037,9348778896225,cuts21,points21,packet21⟩
abbrev cuts22 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.cuts22
abbrev points22 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.pointBounds22
opaque packet22 : CheckedPointSegment 6815745 5 2048 342225484520 342228669796 9697456488324 9697570132831 cuts22 points22 :=
 ⟨Manual.Count131072.C000022.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000022.count_checked,Manual.Count131072.C000022.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.checked22,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.point_links_checked22⟩
def segment22 : PointSegment := ⟨6815745,5,2048,342225484520,342228669796,9697456488324,9697570132831,cuts22,points22,packet22⟩
abbrev cuts23 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.cuts23
abbrev points23 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.pointBounds23
opaque packet23 : CheckedPointSegment 6946817 5 2048 335904969025 335908037054 10039681972844 10039798802627 cuts23 points23 :=
 ⟨Manual.Count131072.C000023.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000023.count_checked,Manual.Count131072.C000023.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.checked23,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000005.point_links_checked23⟩
def segment23 : PointSegment := ⟨6946817,5,2048,335904969025,335908037054,10039681972844,10039798802627,cuts23,points23,packet23⟩
def segments : List PointSegment := [segment20,segment21,segment22,segment23]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 6553600 8994199215082 8994306120453 7077888 10375586941869 10375706839681 segments = true := by decide +kernel
theorem certified : PointChainCertificate 6553600 8994199215082 8994306120453 7077888 10375586941869 10375706839681 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000005
