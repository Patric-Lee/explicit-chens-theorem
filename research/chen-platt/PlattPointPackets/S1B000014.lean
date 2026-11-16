import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000014
namespace ChenEffective.PlattWindow.PointPackets.S1B000014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts56 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.cuts56
abbrev points56 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.pointBounds56
opaque packet56 : CheckedPointSegment 11272193 5 2048 199755836557 199756966205 18556203943178 18556383114406 cuts56 points56 :=
 ⟨Manual.Count131072.C000056.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000056.count_checked,Manual.Count131072.C000056.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.checked56,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.point_links_checked56⟩
def segment56 : PointSegment := ⟨11272193,5,2048,199755836557,199756966205,18556203943178,18556383114406,cuts56,points56,packet56⟩
abbrev cuts57 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.cuts57
abbrev points57 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.pointBounds57
opaque packet57 : CheckedPointSegment 11403265 5 2048 198010579988 198011687020 18755959779735 18756140080611 cuts57 points57 :=
 ⟨Manual.Count131072.C000057.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000057.count_checked,Manual.Count131072.C000057.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.checked57,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.point_links_checked57⟩
def segment57 : PointSegment := ⟨11403265,5,2048,198010579988,198011687020,18755959779735,18756140080611,cuts57,points57,packet57⟩
abbrev cuts58 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.cuts58
abbrev points58 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.pointBounds58
opaque packet58 : CheckedPointSegment 11534337 5 2048 196869824691 196870912975 18953970359723 18954151767631 cuts58 points58 :=
 ⟨Manual.Count131072.C000058.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000058.count_checked,Manual.Count131072.C000058.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.checked58,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.point_links_checked58⟩
def segment58 : PointSegment := ⟨11534337,5,2048,196869824691,196870912975,18953970359723,18954151767631,cuts58,points58,packet58⟩
abbrev cuts59 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.cuts59
abbrev points59 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.pointBounds59
opaque packet59 : CheckedPointSegment 11665409 5 2048 192793768972 192794822822 19150840184414 19151022680606 cuts59 points59 :=
 ⟨Manual.Count131072.C000059.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000059.count_checked,Manual.Count131072.C000059.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.checked59,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000014.point_links_checked59⟩
def segment59 : PointSegment := ⟨11665409,5,2048,192793768972,192794822822,19150840184414,19151022680606,cuts59,points59,packet59⟩
def segments : List PointSegment := [segment56,segment57,segment58,segment59]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 11272192 18556203943178 18556383114406 11796480 19343633953386 19343817503428 segments = true := by decide +kernel
theorem certified : PointChainCertificate 11272192 18556203943178 18556383114406 11796480 19343633953386 19343817503428 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000014
