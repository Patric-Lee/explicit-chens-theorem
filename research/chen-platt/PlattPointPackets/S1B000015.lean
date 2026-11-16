import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000015
namespace ChenEffective.PlattWindow.PointPackets.S1B000015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts60 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.cuts60
abbrev points60 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.pointBounds60
opaque packet60 : CheckedPointSegment 11796481 5 2048 191468717037 191469752149 19343633953386 19343817503428 cuts60 points60 :=
 ⟨Manual.Count131072.C000060.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000060.count_checked,Manual.Count131072.C000060.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.checked60,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.point_links_checked60⟩
def segment60 : PointSegment := ⟨11796481,5,2048,191468717037,191469752149,19343633953386,19343817503428,cuts60,points60,packet60⟩
abbrev cuts61 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.cuts61
abbrev points61 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.pointBounds61
opaque packet61 : CheckedPointSegment 11927553 5 2048 188557098949 188558107239 19535102670423 19535287255577 cuts61 points61 :=
 ⟨Manual.Count131072.C000061.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000061.count_checked,Manual.Count131072.C000061.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.checked61,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.point_links_checked61⟩
def segment61 : PointSegment := ⟨11927553,5,2048,188557098949,188558107239,19535102670423,19535287255577,cuts61,points61,packet61⟩
abbrev cuts62 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.cuts62
abbrev points62 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.pointBounds62
opaque packet62 : CheckedPointSegment 12058625 5 2048 185868747198 185869730395 19723659769372 19723845362816 cuts62 points62 :=
 ⟨Manual.Count131072.C000062.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000062.count_checked,Manual.Count131072.C000062.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.checked62,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.point_links_checked62⟩
def segment62 : PointSegment := ⟨12058625,5,2048,185868747198,185869730395,19723659769372,19723845362816,cuts62,points62,packet62⟩
abbrev cuts63 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.cuts63
abbrev points63 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.pointBounds63
opaque packet63 : CheckedPointSegment 12189697 5 2048 185576726021 185577697191 19909528516570 19909715093211 cuts63 points63 :=
 ⟨Manual.Count131072.C000063.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000063.count_checked,Manual.Count131072.C000063.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.checked63,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000015.point_links_checked63⟩
def segment63 : PointSegment := ⟨12189697,5,2048,185576726021,185577697191,19909528516570,19909715093211,cuts63,points63,packet63⟩
def segments : List PointSegment := [segment60,segment61,segment62,segment63]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 11796480 19343633953386 19343817503428 12320768 20095105242591 20095292790402 segments = true := by decide +kernel
theorem certified : PointChainCertificate 11796480 19343633953386 19343817503428 12320768 20095105242591 20095292790402 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000015
