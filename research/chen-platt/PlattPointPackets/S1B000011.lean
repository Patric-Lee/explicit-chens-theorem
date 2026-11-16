import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000011
namespace ChenEffective.PlattWindow.PointPackets.S1B000011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts44 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.cuts44
abbrev points44 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.pointBounds44
opaque packet44 : CheckedPointSegment 9699329 5 2048 235359380071 235360924739 15939721275755 15939884391351 cuts44 points44 :=
 ⟨Manual.Count131072.C000044.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000044.count_checked,Manual.Count131072.C000044.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.checked44,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.point_links_checked44⟩
def segment44 : PointSegment := ⟨9699329,5,2048,235359380071,235360924739,15939721275755,15939884391351,cuts44,points44,packet44⟩
abbrev cuts45 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.cuts45
abbrev points45 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.pointBounds45
opaque packet45 : CheckedPointSegment 9830401 5 2048 229140404301 229141888284 16175080655826 16175245316090 cuts45 points45 :=
 ⟨Manual.Count131072.C000045.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000045.count_checked,Manual.Count131072.C000045.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.checked45,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.point_links_checked45⟩
def segment45 : PointSegment := ⟨9830401,5,2048,229140404301,229141888284,16175080655826,16175245316090,cuts45,points45,packet45⟩
abbrev cuts46 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.cuts46
abbrev points46 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.pointBounds46
opaque packet46 : CheckedPointSegment 9961473 5 2048 228108228260 228109686298 16404221060127 16404387204374 cuts46 points46 :=
 ⟨Manual.Count131072.C000046.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000046.count_checked,Manual.Count131072.C000046.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.checked46,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.point_links_checked46⟩
def segment46 : PointSegment := ⟨9961473,5,2048,228108228260,228109686298,16404221060127,16404387204374,cuts46,points46,packet46⟩
abbrev cuts47 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.cuts47
abbrev points47 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.pointBounds47
opaque packet47 : CheckedPointSegment 10092545 5 2048 223734486703 223735898453 16632329288387 16632496890672 cuts47 points47 :=
 ⟨Manual.Count131072.C000047.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000047.count_checked,Manual.Count131072.C000047.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.checked47,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000011.point_links_checked47⟩
def segment47 : PointSegment := ⟨10092545,5,2048,223734486703,223735898453,16632329288387,16632496890672,cuts47,points47,packet47⟩
def segments : List PointSegment := [segment44,segment45,segment46,segment47]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 9699328 15939721275755 15939884391351 10223616 16856063775090 16856232789125 segments = true := by decide +kernel
theorem certified : PointChainCertificate 9699328 15939721275755 15939884391351 10223616 16856063775090 16856232789125 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000011
