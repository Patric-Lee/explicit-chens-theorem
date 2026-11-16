import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000023
namespace ChenEffective.PlattWindow.PointPackets.S1B000023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts92 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.cuts92
abbrev points92 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.pointBounds92
opaque packet92 : CheckedPointSegment 15990785 5 2048 137981883079 137982435126 24552296943459 24552504935606 cuts92 points92 :=
 ⟨Manual.Count131072.C000092.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000092.count_checked,Manual.Count131072.C000092.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.checked92,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.point_links_checked92⟩
def segment92 : PointSegment := ⟨15990785,5,2048,137981883079,137982435126,24552296943459,24552504935606,cuts92,points92,packet92⟩
abbrev cuts93 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.cuts93
abbrev points93 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.pointBounds93
opaque packet93 : CheckedPointSegment 16121857 5 2048 137125266435 137125810648 24690278826538 24690487370732 cuts93 points93 :=
 ⟨Manual.Count131072.C000093.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000093.count_checked,Manual.Count131072.C000093.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.checked93,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.point_links_checked93⟩
def segment93 : PointSegment := ⟨16121857,5,2048,137125266435,137125810648,24690278826538,24690487370732,cuts93,points93,packet93⟩
abbrev cuts94 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.cuts94
abbrev points94 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.pointBounds94
opaque packet94 : CheckedPointSegment 16252929 5 2048 135371889107 135372422135 24827404092973 24827613181380 cuts94 points94 :=
 ⟨Manual.Count131072.C000094.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000094.count_checked,Manual.Count131072.C000094.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.checked94,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.point_links_checked94⟩
def segment94 : PointSegment := ⟨16252929,5,2048,135371889107,135372422135,24827404092973,24827613181380,cuts94,points94,packet94⟩
abbrev cuts95 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.cuts95
abbrev points95 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.pointBounds95
opaque packet95 : CheckedPointSegment 16384001 5 2048 135677046766 135677576694 24962775982080 24962985603515 cuts95 points95 :=
 ⟨Manual.Count131072.C000095.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000095.count_checked,Manual.Count131072.C000095.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.checked95,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000023.point_links_checked95⟩
def segment95 : PointSegment := ⟨16384001,5,2048,135677046766,135677576694,24962775982080,24962985603515,cuts95,points95,packet95⟩
def segments : List PointSegment := [segment92,segment93,segment94,segment95]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 15990784 24552296943459 24552504935606 16515072 25098453028846 25098663180209 segments = true := by decide +kernel
theorem certified : PointChainCertificate 15990784 24552296943459 24552504935606 16515072 25098453028846 25098663180209 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000023
