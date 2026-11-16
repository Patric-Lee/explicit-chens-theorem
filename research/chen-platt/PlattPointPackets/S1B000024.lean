import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000024
namespace ChenEffective.PlattWindow.PointPackets.S1B000024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts96 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.cuts96
abbrev points96 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.pointBounds96
opaque packet96 : CheckedPointSegment 16515073 5 2048 133515157404 133515674810 25098453028846 25098663180209 cuts96 points96 :=
 ⟨Manual.Count131072.C000096.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000096.count_checked,Manual.Count131072.C000096.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.checked96,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.point_links_checked96⟩
def segment96 : PointSegment := ⟨16515073,5,2048,133515157404,133515674810,25098453028846,25098663180209,cuts96,points96,packet96⟩
abbrev cuts97 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.cuts97
abbrev points97 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.pointBounds97
opaque packet97 : CheckedPointSegment 16646145 5 2048 133143898387 133144410321 25231968186250 25232178855019 cuts97 points97 :=
 ⟨Manual.Count131072.C000097.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000097.count_checked,Manual.Count131072.C000097.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.checked97,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.point_links_checked97⟩
def segment97 : PointSegment := ⟨16646145,5,2048,133143898387,133144410321,25231968186250,25232178855019,cuts97,points97,packet97⟩
abbrev cuts98 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.cuts98
abbrev points98 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.pointBounds98
opaque packet98 : CheckedPointSegment 16777217 6 1024 131774617076 131775619555 25365112084637 25365323265340 cuts98 points98 :=
 ⟨Manual.Count131072.C000098.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000098.count_checked,Manual.Count131072.C000098.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.checked98,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.point_links_checked98⟩
def segment98 : PointSegment := ⟨16777217,6,1024,131774617076,131775619555,25365112084637,25365323265340,cuts98,points98,packet98⟩
abbrev cuts99 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.cuts99
abbrev points99 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.pointBounds99
opaque packet99 : CheckedPointSegment 16908289 6 1024 131817279541 131818274623 25496886701713 25497098884895 cuts99 points99 :=
 ⟨Manual.Count131072.C000099.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000099.count_checked,Manual.Count131072.C000099.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.checked99,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000024.point_links_checked99⟩
def segment99 : PointSegment := ⟨16908289,6,1024,131817279541,131818274623,25496886701713,25497098884895,cuts99,points99,packet99⟩
def segments : List PointSegment := [segment96,segment97,segment98,segment99]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 16515072 25098453028846 25098663180209 17039360 25628703981254 25628917159518 segments = true := by decide +kernel
theorem certified : PointChainCertificate 16515072 25098453028846 25098663180209 17039360 25628703981254 25628917159518 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000024
