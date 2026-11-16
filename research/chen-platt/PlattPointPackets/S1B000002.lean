import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000002
namespace ChenEffective.PlattWindow.PointPackets.S1B000002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts8 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.cuts8
abbrev points8 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.pointBounds8
opaque packet8 : CheckedPointSegment 4980737 5 2048 471973827702 471979816399 4035733554828 4035784694748 cuts8 points8 :=
 ⟨Manual.Count131072.C000008.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000008.count_checked,Manual.Count131072.C000008.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.checked8,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.point_links_checked8⟩
def segment8 : PointSegment := ⟨4980737,5,2048,471973827702,471979816399,4035733554828,4035784694748,cuts8,points8,packet8⟩
abbrev cuts9 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.cuts9
abbrev points9 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.pointBounds9
opaque packet9 : CheckedPointSegment 5111809 5 2048 460781041625 460786740336 4507707382530 4507764511147 cuts9 points9 :=
 ⟨Manual.Count131072.C000009.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000009.count_checked,Manual.Count131072.C000009.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.checked9,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.point_links_checked9⟩
def segment9 : PointSegment := ⟨5111809,5,2048,460781041625,460786740336,4507707382530,4507764511147,cuts9,points9,packet9⟩
abbrev cuts10 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.cuts10
abbrev points10 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.pointBounds10
opaque packet10 : CheckedPointSegment 5242881 5 2048 449051495707 449056912521 4968488424155 4968551251483 cuts10 points10 :=
 ⟨Manual.Count131072.C000010.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000010.count_checked,Manual.Count131072.C000010.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.checked10,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.point_links_checked10⟩
def segment10 : PointSegment := ⟨5242881,5,2048,449051495707,449056912521,4968488424155,4968551251483,cuts10,points10,packet10⟩
abbrev cuts11 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.cuts11
abbrev points11 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.pointBounds11
opaque packet11 : CheckedPointSegment 5373953 5 2048 437293757423 437298905301 5417539919862 5417608164004 cuts11 points11 :=
 ⟨Manual.Count131072.C000011.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000011.count_checked,Manual.Count131072.C000011.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.checked11,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000002.point_links_checked11⟩
def segment11 : PointSegment := ⟨5373953,5,2048,437293757423,437298905301,5417539919862,5417608164004,cuts11,points11,packet11⟩
def segments : List PointSegment := [segment8,segment9,segment10,segment11]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 4980736 4035733554828 4035784694748 5505024 5854833677285 5854907069305 segments = true := by decide +kernel
theorem certified : PointChainCertificate 4980736 4035733554828 4035784694748 5505024 5854833677285 5854907069305 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000002
