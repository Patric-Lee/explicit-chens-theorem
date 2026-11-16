import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000007
namespace ChenEffective.PlattWindow.PointPackets.S1B000007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts28 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.cuts28
abbrev points28 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.pointBounds28
opaque packet28 : CheckedPointSegment 7602177 5 2048 304074860608 304077400865 11645083792189 11645214777025 cuts28 points28 :=
 ⟨Manual.Count131072.C000028.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000028.count_checked,Manual.Count131072.C000028.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.checked28,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.point_links_checked28⟩
def segment28 : PointSegment := ⟨7602177,5,2048,304074860608,304077400865,11645083792189,11645214777025,cuts28,points28,packet28⟩
abbrev cuts29 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.cuts29
abbrev points29 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.pointBounds29
opaque packet29 : CheckedPointSegment 7733249 5 2048 298256172276 298258621923 11949158652797 11949292177890 cuts29 points29 :=
 ⟨Manual.Count131072.C000029.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000029.count_checked,Manual.Count131072.C000029.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.checked29,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.point_links_checked29⟩
def segment29 : PointSegment := ⟨7733249,5,2048,298256172276,298258621923,11949158652797,11949292177890,cuts29,points29,packet29⟩
abbrev cuts30 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.cuts30
abbrev points30 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.pointBounds30
opaque packet30 : CheckedPointSegment 7864321 5 2048 292525947824 292528310938 12247414825073 12247550799813 cuts30 points30 :=
 ⟨Manual.Count131072.C000030.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000030.count_checked,Manual.Count131072.C000030.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.checked30,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.point_links_checked30⟩
def segment30 : PointSegment := ⟨7864321,5,2048,292525947824,292528310938,12247414825073,12247550799813,cuts30,points30,packet30⟩
abbrev cuts31 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.cuts31
abbrev points31 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.pointBounds31
opaque packet31 : CheckedPointSegment 7995393 5 2048 286992776724 286995057391 12539940772897 12540079110751 cuts31 points31 :=
 ⟨Manual.Count131072.C000031.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000031.count_checked,Manual.Count131072.C000031.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.checked31,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000007.point_links_checked31⟩
def segment31 : PointSegment := ⟨7995393,5,2048,286992776724,286995057391,12539940772897,12540079110751,cuts31,points31,packet31⟩
def segments : List PointSegment := [segment28,segment29,segment30,segment31]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 7602176 11645083792189 11645214777025 8126464 12826933549621 12827074168142 segments = true := by decide +kernel
theorem certified : PointChainCertificate 7602176 11645083792189 11645214777025 8126464 12826933549621 12827074168142 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000007
