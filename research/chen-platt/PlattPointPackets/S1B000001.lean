import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000001
namespace ChenEffective.PlattWindow.PointPackets.S1B000001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts4 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.cuts4
abbrev points4 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.pointBounds4
opaque packet4 : CheckedPointSegment 4456449 5 2048 532182173660 532189708963 1995142083377 1995165481175 cuts4 points4 :=
 ⟨Manual.Count131072.C000004.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000004.count_checked,Manual.Count131072.C000004.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.checked4,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.point_links_checked4⟩
def segment4 : PointSegment := ⟨4456449,5,2048,532182173660,532189708963,1995142083377,1995165481175,cuts4,points4,packet4⟩
abbrev cuts5 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.cuts5
abbrev points5 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.pointBounds5
opaque packet5 : CheckedPointSegment 4587521 5 2048 516808052010 516815163302 2527324257037 2527355190138 cuts5 points5 :=
 ⟨Manual.Count131072.C000005.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000005.count_checked,Manual.Count131072.C000005.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.checked5,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.point_links_checked5⟩
def segment5 : PointSegment := ⟨4587521,5,2048,516808052010,516815163302,2527324257037,2527355190138,cuts5,points5,packet5⟩
abbrev cuts6 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.cuts6
abbrev points6 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.pointBounds6
opaque packet6 : CheckedPointSegment 4718593 5 2048 500120888322 500127581581 3044132309047 3044170353440 cuts6 points6 :=
 ⟨Manual.Count131072.C000006.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000006.count_checked,Manual.Count131072.C000006.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.checked6,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.point_links_checked6⟩
def segment6 : PointSegment := ⟨4718593,5,2048,500120888322,500127581581,3044132309047,3044170353440,cuts6,points6,packet6⟩
abbrev cuts7 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.cuts7
abbrev points7 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.pointBounds7
opaque packet7 : CheckedPointSegment 4849665 5 2048 491480357459 491486759727 3544253197369 3544297935021 cuts7 points7 :=
 ⟨Manual.Count131072.C000007.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000007.count_checked,Manual.Count131072.C000007.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.checked7,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000001.point_links_checked7⟩
def segment7 : PointSegment := ⟨4849665,5,2048,491480357459,491486759727,3544253197369,3544297935021,cuts7,points7,packet7⟩
def segments : List PointSegment := [segment4,segment5,segment6,segment7]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 4456448 1995142083377 1995165481175 4980736 4035733554828 4035784694748 segments = true := by decide +kernel
theorem certified : PointChainCertificate 4456448 1995142083377 1995165481175 4980736 4035733554828 4035784694748 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000001
