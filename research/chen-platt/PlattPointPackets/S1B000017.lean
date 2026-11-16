import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000017
namespace ChenEffective.PlattWindow.PointPackets.S1B000017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts68 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.cuts68
abbrev points68 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.pointBounds68
opaque packet68 : CheckedPointSegment 12845057 5 2048 173414926784 173415788517 20813421067578 20813612278134 cuts68 points68 :=
 ⟨Manual.Count131072.C000068.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000068.count_checked,Manual.Count131072.C000068.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.checked68,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.point_links_checked68⟩
def segment68 : PointSegment := ⟨12845057,5,2048,173414926784,173415788517,20813421067578,20813612278134,cuts68,points68,packet68⟩
abbrev cuts69 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.cuts69
abbrev points69 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.pointBounds69
opaque packet69 : CheckedPointSegment 12976129 5 2048 171218033365 171218875676 20986835994362 20987028066651 cuts69 points69 :=
 ⟨Manual.Count131072.C000069.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000069.count_checked,Manual.Count131072.C000069.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.checked69,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.point_links_checked69⟩
def segment69 : PointSegment := ⟨12976129,5,2048,171218033365,171218875676,20986835994362,20987028066651,cuts69,points69,packet69⟩
abbrev cuts70 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.cuts70
abbrev points70 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.pointBounds70
opaque packet70 : CheckedPointSegment 13107201 5 2048 171007496494 171008329382 21158054027727 21158246942327 cuts70 points70 :=
 ⟨Manual.Count131072.C000070.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000070.count_checked,Manual.Count131072.C000070.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.checked70,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.point_links_checked70⟩
def segment70 : PointSegment := ⟨13107201,5,2048,171007496494,171008329382,21158054027727,21158246942327,cuts70,points70,packet70⟩
abbrev cuts71 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.cuts71
abbrev points71 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.pointBounds71
opaque packet71 : CheckedPointSegment 13238273 5 2048 169257290463 169258106773 21329061524221 21329255271709 cuts71 points71 :=
 ⟨Manual.Count131072.C000071.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000071.count_checked,Manual.Count131072.C000071.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.checked71,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000017.point_links_checked71⟩
def segment71 : PointSegment := ⟨13238273,5,2048,169257290463,169258106773,21329061524221,21329255271709,cuts71,points71,packet71⟩
def segments : List PointSegment := [segment68,segment69,segment70,segment71]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 12845056 20813421067578 20813612278134 13369344 21498318814684 21498513378482 segments = true := by decide +kernel
theorem certified : PointChainCertificate 12845056 20813421067578 20813612278134 13369344 21498318814684 21498513378482 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000017
