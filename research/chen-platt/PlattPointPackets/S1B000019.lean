import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000019
namespace ChenEffective.PlattWindow.PointPackets.S1B000019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts76 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.cuts76
abbrev points76 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.pointBounds76
opaque packet76 : CheckedPointSegment 13893633 5 2048 159785466565 159786201242 22157339669675 22157537336417 cuts76 points76 :=
 ⟨Manual.Count131072.C000076.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000076.count_checked,Manual.Count131072.C000076.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.checked76,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.point_links_checked76⟩
def segment76 : PointSegment := ⟨13893633,5,2048,159785466565,159786201242,22157339669675,22157537336417,cuts76,points76,packet76⟩
abbrev cuts77 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.cuts77
abbrev points77 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.pointBounds77
opaque packet77 : CheckedPointSegment 14024705 5 2048 159413342630 159414068784 22317125136240 22317323537659 cuts77 points77 :=
 ⟨Manual.Count131072.C000077.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000077.count_checked,Manual.Count131072.C000077.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.checked77,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.point_links_checked77⟩
def segment77 : PointSegment := ⟨14024705,5,2048,159413342630,159414068784,22317125136240,22317323537659,cuts77,points77,packet77⟩
abbrev cuts78 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.cuts78
abbrev points78 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.pointBounds78
opaque packet78 : CheckedPointSegment 14155777 5 2048 157228128682 157228838309 22476538478870 22476737606443 cuts78 points78 :=
 ⟨Manual.Count131072.C000078.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000078.count_checked,Manual.Count131072.C000078.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.checked78,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.point_links_checked78⟩
def segment78 : PointSegment := ⟨14155777,5,2048,157228128682,157228838309,22476538478870,22476737606443,cuts78,points78,packet78⟩
abbrev cuts79 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.cuts79
abbrev points79 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.pointBounds79
opaque packet79 : CheckedPointSegment 14286849 5 2048 157207938489 157208641575 22633766607552 22633966444752 cuts79 points79 :=
 ⟨Manual.Count131072.C000079.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000079.count_checked,Manual.Count131072.C000079.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.checked79,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000019.point_links_checked79⟩
def segment79 : PointSegment := ⟨14286849,5,2048,157207938489,157208641575,22633766607552,22633966444752,cuts79,points79,packet79⟩
def segments : List PointSegment := [segment76,segment77,segment78,segment79]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 13893632 22157339669675 22157537336417 14417920 22790974546041 22791175086327 segments = true := by decide +kernel
theorem certified : PointChainCertificate 13893632 22157339669675 22157537336417 14417920 22790974546041 22791175086327 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000019
