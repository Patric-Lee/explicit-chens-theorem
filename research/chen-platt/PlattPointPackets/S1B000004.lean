import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000004
namespace ChenEffective.PlattWindow.PointPackets.S1B000004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts16 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.cuts16
abbrev points16 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.pointBounds16
opaque packet16 : CheckedPointSegment 6029313 5 2048 385520819735 385524870086 7498551237318 7498642902210 cuts16 points16 :=
 ⟨Manual.Count131072.C000016.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000016.count_checked,Manual.Count131072.C000016.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.checked16,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.point_links_checked16⟩
def segment16 : PointSegment := ⟨6029313,5,2048,385520819735,385524870086,7498551237318,7498642902210,cuts16,points16,packet16⟩
abbrev cuts17 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.cuts17
abbrev points17 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.pointBounds17
opaque packet17 : CheckedPointSegment 6160385 5 2048 378995390021 378999288169 7884072057053 7884167772296 cuts17 points17 :=
 ⟨Manual.Count131072.C000017.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000017.count_checked,Manual.Count131072.C000017.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.checked17,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.point_links_checked17⟩
def segment17 : PointSegment := ⟨6160385,5,2048,378995390021,378999288169,7884072057053,7884167772296,cuts17,points17,packet17⟩
abbrev cuts18 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.cuts18
abbrev points18 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.pointBounds18
opaque packet18 : CheckedPointSegment 6291457 5 2048 369178001091 369181720409 8263067447074 8263167060465 cuts18 points18 :=
 ⟨Manual.Count131072.C000018.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000018.count_checked,Manual.Count131072.C000018.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.checked18,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.point_links_checked18⟩
def segment18 : PointSegment := ⟨6291457,5,2048,369178001091,369181720409,8263067447074,8263167060465,cuts18,points18,packet18⟩
abbrev cuts19 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.cuts19
abbrev points19 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.pointBounds19
opaque packet19 : CheckedPointSegment 6422529 5 2048 361953766917 361957339579 8632245448165 8632348780874 cuts19 points19 :=
 ⟨Manual.Count131072.C000019.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000019.count_checked,Manual.Count131072.C000019.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.checked19,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000004.point_links_checked19⟩
def segment19 : PointSegment := ⟨6422529,5,2048,361953766917,361957339579,8632245448165,8632348780874,cuts19,points19,packet19⟩
def segments : List PointSegment := [segment16,segment17,segment18,segment19]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 6029312 7498551237318 7498642902210 6553600 8994199215082 8994306120453 segments = true := by decide +kernel
theorem certified : PointChainCertificate 6029312 7498551237318 7498642902210 6553600 8994199215082 8994306120453 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000004
