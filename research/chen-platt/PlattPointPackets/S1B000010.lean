import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000010
namespace ChenEffective.PlattWindow.PointPackets.S1B000010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts40 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.cuts40
abbrev points40 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.pointBounds40
opaque packet40 : CheckedPointSegment 9175041 5 2048 250547793353 250549530764 14964975496797 14965131990084 cuts40 points40 :=
 ⟨Manual.Count131072.C000040.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000040.count_checked,Manual.Count131072.C000040.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.checked40,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.point_links_checked40⟩
def segment40 : PointSegment := ⟨9175041,5,2048,250547793353,250549530764,14964975496797,14965131990084,cuts40,points40,packet40⟩
abbrev cuts41 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.cuts41
abbrev points41 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.pointBounds41
opaque packet41 : CheckedPointSegment 9306113 5 2048 244100283122 244101952229 15215523290150 15215681520848 cuts41 points41 :=
 ⟨Manual.Count131072.C000041.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000041.count_checked,Manual.Count131072.C000041.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.checked41,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.point_links_checked41⟩
def segment41 : PointSegment := ⟨9306113,5,2048,244100283122,244101952229,15215523290150,15215681520848,cuts41,points41,packet41⟩
abbrev cuts42 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.cuts42
abbrev points42 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.pointBounds42
opaque packet42 : CheckedPointSegment 9437185 5 2048 240937750653 240939375469 15459623573272 15459783473077 cuts42 points42 :=
 ⟨Manual.Count131072.C000042.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000042.count_checked,Manual.Count131072.C000042.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.checked42,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.point_links_checked42⟩
def segment42 : PointSegment := ⟨9437185,5,2048,240937750653,240939375469,15459623573272,15459783473077,cuts42,points42,packet42⟩
abbrev cuts43 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.cuts43
abbrev points43 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.pointBounds43
opaque packet43 : CheckedPointSegment 9568257 5 2048 239159951830 239161542805 15700561323925 15700722848546 cuts43 points43 :=
 ⟨Manual.Count131072.C000043.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000043.count_checked,Manual.Count131072.C000043.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.checked43,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000010.point_links_checked43⟩
def segment43 : PointSegment := ⟨9568257,5,2048,239159951830,239161542805,15700561323925,15700722848546,cuts43,points43,packet43⟩
def segments : List PointSegment := [segment40,segment41,segment42,segment43]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 9175040 14964975496797 14965131990084 9699328 15939721275755 15939884391351 segments = true := by decide +kernel
theorem certified : PointChainCertificate 9175040 14964975496797 14965131990084 9699328 15939721275755 15939884391351 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000010
