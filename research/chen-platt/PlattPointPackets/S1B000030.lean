import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000030
namespace ChenEffective.PlattWindow.PointPackets.S1B000030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts120 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.cuts120
abbrev points120 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.pointBounds120
opaque packet120 : CheckedPointSegment 19660801 6 1024 111897156097 111897883200 28035808217702 28036038266661 cuts120 points120 :=
 ⟨Manual.Count131072.C000120.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000120.count_checked,Manual.Count131072.C000120.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.checked120,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.point_links_checked120⟩
def segment120 : PointSegment := ⟨19660801,6,1024,111897156097,111897883200,28035808217702,28036038266661,cuts120,points120,packet120⟩
abbrev cuts121 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.cuts121
abbrev points121 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.pointBounds121
opaque packet121 : CheckedPointSegment 19791873 6 1024 110932226272 110932942373 28147705373799 28147936149861 cuts121 points121 :=
 ⟨Manual.Count131072.C000121.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000121.count_checked,Manual.Count131072.C000121.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.checked121,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.point_links_checked121⟩
def segment121 : PointSegment := ⟨19791873,6,1024,110932226272,110932942373,28147705373799,28147936149861,cuts121,points121,packet121⟩
abbrev cuts122 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.cuts122
abbrev points122 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.pointBounds122
opaque packet122 : CheckedPointSegment 19922945 6 1024 110204599448 110205306218 28258637600071 28258869092234 cuts122 points122 :=
 ⟨Manual.Count131072.C000122.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000122.count_checked,Manual.Count131072.C000122.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.checked122,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.point_links_checked122⟩
def segment122 : PointSegment := ⟨19922945,6,1024,110204599448,110205306218,28258637600071,28258869092234,cuts122,points122,packet122⟩
abbrev cuts123 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.cuts123
abbrev points123 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.pointBounds123
opaque packet123 : CheckedPointSegment 20054017 6 1024 109317893038 109318589543 28368842199519 28369074398452 cuts123 points123 :=
 ⟨Manual.Count131072.C000123.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000123.count_checked,Manual.Count131072.C000123.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.checked123,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000030.point_links_checked123⟩
def segment123 : PointSegment := ⟨20054017,6,1024,109317893038,109318589543,28368842199519,28369074398452,cuts123,points123,packet123⟩
def segments : List PointSegment := [segment120,segment121,segment122,segment123]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 19660800 28035808217702 28036038266661 20185088 28478160092557 28478392987995 segments = true := by decide +kernel
theorem certified : PointChainCertificate 19660800 28035808217702 28036038266661 20185088 28478160092557 28478392987995 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000030
