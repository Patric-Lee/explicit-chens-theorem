import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000018
namespace ChenEffective.PlattWindow.PointPackets.S1B000018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts72 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.cuts72
abbrev points72 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.pointBounds72
opaque packet72 : CheckedPointSegment 13369345 5 2048 166079689886 166080483109 21498318814684 21498513378482 cuts72 points72 :=
 ⟨Manual.Count131072.C000072.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000072.count_checked,Manual.Count131072.C000072.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.checked72,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.point_links_checked72⟩
def segment72 : PointSegment := ⟨13369345,5,2048,166079689886,166080483109,21498318814684,21498513378482,cuts72,points72,packet72⟩
abbrev cuts73 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.cuts73
abbrev points73 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.pointBounds73
opaque packet73 : CheckedPointSegment 13500417 5 2048 165572239960 165573023132 21664398504570 21664593861591 cuts73 points73 :=
 ⟨Manual.Count131072.C000073.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000073.count_checked,Manual.Count131072.C000073.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.checked73,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.point_links_checked73⟩
def segment73 : PointSegment := ⟨13500417,5,2048,165572239960,165573023132,21664398504570,21664593861591,cuts73,points73,packet73⟩
abbrev cuts74 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.cuts74
abbrev points74 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.pointBounds74
opaque packet74 : CheckedPointSegment 13631489 5 2048 164321940809 164322710681 21829970744530 21830166884723 cuts74 points74 :=
 ⟨Manual.Count131072.C000074.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000074.count_checked,Manual.Count131072.C000074.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.checked74,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.point_links_checked74⟩
def segment74 : PointSegment := ⟨13631489,5,2048,164321940809,164322710681,21829970744530,21830166884723,cuts74,points74,packet74⟩
abbrev cuts75 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.cuts75
abbrev points75 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.pointBounds75
opaque packet75 : CheckedPointSegment 13762561 5 2048 163046984336 163047741013 21994292685339 21994489595404 cuts75 points75 :=
 ⟨Manual.Count131072.C000075.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000075.count_checked,Manual.Count131072.C000075.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.checked75,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000018.point_links_checked75⟩
def segment75 : PointSegment := ⟨13762561,5,2048,163046984336,163047741013,21994292685339,21994489595404,cuts75,points75,packet75⟩
def segments : List PointSegment := [segment72,segment73,segment74,segment75]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 13369344 21498318814684 21498513378482 13893632 22157339669675 22157537336417 segments = true := by decide +kernel
theorem certified : PointChainCertificate 13369344 21498318814684 21498513378482 13893632 22157339669675 22157537336417 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000018
