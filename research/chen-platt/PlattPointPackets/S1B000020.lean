import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000020
namespace ChenEffective.PlattWindow.PointPackets.S1B000020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts80 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.cuts80
abbrev points80 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.pointBounds80
opaque packet80 : CheckedPointSegment 14417921 5 2048 153628617742 153629298684 22790974546041 22791175086327 cuts80 points80 :=
 ⟨Manual.Count131072.C000080.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000080.count_checked,Manual.Count131072.C000080.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.checked80,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.point_links_checked80⟩
def segment80 : PointSegment := ⟨14417921,5,2048,153628617742,153629298684,22790974546041,22791175086327,cuts80,points80,packet80⟩
abbrev cuts81 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.cuts81
abbrev points81 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.pointBounds81
opaque packet81 : CheckedPointSegment 14548993 5 2048 152811129681 152811800948 22944603163783 22944804385011 cuts81 points81 :=
 ⟨Manual.Count131072.C000081.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000081.count_checked,Manual.Count131072.C000081.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.checked81,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.point_links_checked81⟩
def segment81 : PointSegment := ⟨14548993,5,2048,152811129681,152811800948,22944603163783,22944804385011,cuts81,points81,packet81⟩
abbrev cuts82 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.cuts82
abbrev points82 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.pointBounds82
opaque packet82 : CheckedPointSegment 14680065 5 2048 152367170545 152367833930 23097414293464 23097616185959 cuts82 points82 :=
 ⟨Manual.Count131072.C000082.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000082.count_checked,Manual.Count131072.C000082.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.checked82,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.point_links_checked82⟩
def segment82 : PointSegment := ⟨14680065,5,2048,152367170545,152367833930,23097414293464,23097616185959,cuts82,points82,packet82⟩
abbrev cuts83 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.cuts83
abbrev points83 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.pointBounds83
opaque packet83 : CheckedPointSegment 14811137 5 2048 149417210345 149417855169 23249781464009 23249984019889 cuts83 points83 :=
 ⟨Manual.Count131072.C000083.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000083.count_checked,Manual.Count131072.C000083.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.checked83,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000020.point_links_checked83⟩
def segment83 : PointSegment := ⟨14811137,5,2048,149417210345,149417855169,23249781464009,23249984019889,cuts83,points83,packet83⟩
def segments : List PointSegment := [segment80,segment81,segment82,segment83]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 14417920 22790974546041 22791175086327 14942208 23399198674354 23399401875058 segments = true := by decide +kernel
theorem certified : PointChainCertificate 14417920 22790974546041 22791175086327 14942208 23399198674354 23399401875058 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000020
