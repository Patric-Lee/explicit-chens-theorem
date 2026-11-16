import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000029
namespace ChenEffective.PlattWindow.PointPackets.S1B000029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts116 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.cuts116
abbrev points116 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.pointBounds116
opaque packet116 : CheckedPointSegment 19136513 6 1024 114087169613 114087931142 27583497267169 27583724327071 cuts116 points116 :=
 ⟨Manual.Count131072.C000116.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000116.count_checked,Manual.Count131072.C000116.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.checked116,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.point_links_checked116⟩
def segment116 : PointSegment := ⟨19136513,6,1024,114087169613,114087931142,27583497267169,27583724327071,cuts116,points116,packet116⟩
abbrev cuts117 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.cuts117
abbrev points117 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.pointBounds117
opaque packet117 : CheckedPointSegment 19267585 6 1024 114172907117 114173664056 27697584436782 27697812258213 cuts117 points117 :=
 ⟨Manual.Count131072.C000117.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000117.count_checked,Manual.Count131072.C000117.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.checked117,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.point_links_checked117⟩
def segment117 : PointSegment := ⟨19267585,6,1024,114172907117,114173664056,27697584436782,27697812258213,cuts117,points117,packet117⟩
abbrev cuts118 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.cuts118
abbrev points118 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.pointBounds118
opaque packet118 : CheckedPointSegment 19398657 6 1024 112756147517 112756890102 27811757343899 27811985922269 cuts118 points118 :=
 ⟨Manual.Count131072.C000118.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000118.count_checked,Manual.Count131072.C000118.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.checked118,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.point_links_checked118⟩
def segment118 : PointSegment := ⟨19398657,6,1024,112756147517,112756890102,27811757343899,27811985922269,cuts118,points118,packet118⟩
abbrev cuts119 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.cuts119
abbrev points119 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.pointBounds119
opaque packet119 : CheckedPointSegment 19529729 6 1024 111294726286 111295454290 27924513491416 27924742812371 cuts119 points119 :=
 ⟨Manual.Count131072.C000119.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000119.count_checked,Manual.Count131072.C000119.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.checked119,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000029.point_links_checked119⟩
def segment119 : PointSegment := ⟨19529729,6,1024,111294726286,111295454290,27924513491416,27924742812371,cuts119,points119,packet119⟩
def segments : List PointSegment := [segment116,segment117,segment118,segment119]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 19136512 27583497267169 27583724327071 19660800 28035808217702 28036038266661 segments = true := by decide +kernel
theorem certified : PointChainCertificate 19136512 27583497267169 27583724327071 19660800 28035808217702 28036038266661 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000029
