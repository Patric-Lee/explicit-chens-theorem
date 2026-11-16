import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000028
namespace ChenEffective.PlattWindow.PointPackets.S1B000028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts112 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.cuts112
abbrev points112 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.pointBounds112
opaque packet112 : CheckedPointSegment 18612225 6 1024 118405259727 118406072201 27116848509949 27117072400626 cuts112 points112 :=
 ⟨Manual.Count131072.C000112.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000112.count_checked,Manual.Count131072.C000112.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.checked112,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.point_links_checked112⟩
def segment112 : PointSegment := ⟨18612225,6,1024,118405259727,118406072201,27116848509949,27117072400626,cuts112,points112,packet112⟩
abbrev cuts113 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.cuts113
abbrev points113 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.pointBounds113
opaque packet113 : CheckedPointSegment 18743297 6 1024 117144902086 117145700322 27235253769676 27235478472827 cuts113 points113 :=
 ⟨Manual.Count131072.C000113.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000113.count_checked,Manual.Count131072.C000113.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.checked113,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.point_links_checked113⟩
def segment113 : PointSegment := ⟨18743297,6,1024,117144902086,117145700322,27235253769676,27235478472827,cuts113,points113,packet113⟩
abbrev cuts114 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.cuts114
abbrev points114 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.pointBounds114
opaque packet114 : CheckedPointSegment 18874369 6 1024 115843710754 115844494661 27352398671762 27352624173149 cuts114 points114 :=
 ⟨Manual.Count131072.C000114.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000114.count_checked,Manual.Count131072.C000114.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.checked114,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.point_links_checked114⟩
def segment114 : PointSegment := ⟨18874369,6,1024,115843710754,115844494661,27352398671762,27352624173149,cuts114,points114,packet114⟩
abbrev cuts115 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.cuts115
abbrev points115 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.pointBounds115
opaque packet115 : CheckedPointSegment 19005441 6 1024 115254884653 115255659261 27468242382516 27468468667810 cuts115 points115 :=
 ⟨Manual.Count131072.C000115.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000115.count_checked,Manual.Count131072.C000115.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.checked115,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000028.point_links_checked115⟩
def segment115 : PointSegment := ⟨19005441,6,1024,115254884653,115255659261,27468242382516,27468468667810,cuts115,points115,packet115⟩
def segments : List PointSegment := [segment112,segment113,segment114,segment115]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 18612224 27116848509949 27117072400626 19136512 27583497267169 27583724327071 segments = true := by decide +kernel
theorem certified : PointChainCertificate 18612224 27116848509949 27117072400626 19136512 27583497267169 27583724327071 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000028
