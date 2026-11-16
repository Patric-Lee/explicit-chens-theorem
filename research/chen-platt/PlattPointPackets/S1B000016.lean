import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000016
namespace ChenEffective.PlattWindow.PointPackets.S1B000016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts64 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.cuts64
abbrev points64 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.pointBounds64
opaque packet64 : CheckedPointSegment 12320769 5 2048 182752153334 182753099646 20095105242591 20095292790402 cuts64 points64 :=
 ⟨Manual.Count131072.C000064.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000064.count_checked,Manual.Count131072.C000064.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.checked64,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.point_links_checked64⟩
def segment64 : PointSegment := ⟨12320769,5,2048,182752153334,182753099646,20095105242591,20095292790402,cuts64,points64,packet64⟩
abbrev cuts65 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.cuts65
abbrev points65 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.pointBounds65
opaque packet65 : CheckedPointSegment 12451841 5 2048 179199212023 179200130326 20277857395925 20278045890048 cuts65 points65 :=
 ⟨Manual.Count131072.C000065.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000065.count_checked,Manual.Count131072.C000065.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.checked65,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.point_links_checked65⟩
def segment65 : PointSegment := ⟨12451841,5,2048,179199212023,179200130326,20277857395925,20278045890048,cuts65,points65,packet65⟩
abbrev cuts66 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.cuts66
abbrev points66 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.pointBounds66
opaque packet66 : CheckedPointSegment 12582913 5 2048 178855924244 178856831336 20457056607948 20457246020374 cuts66 points66 :=
 ⟨Manual.Count131072.C000066.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000066.count_checked,Manual.Count131072.C000066.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.checked66,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.point_links_checked66⟩
def segment66 : PointSegment := ⟨12582913,5,2048,178855924244,178856831336,20457056607948,20457246020374,cuts66,points66,packet66⟩
abbrev cuts67 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.cuts67
abbrev points67 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.pointBounds67
opaque packet67 : CheckedPointSegment 12713985 5 2048 177508535386 177509426424 20635912532192 20636102851710 cuts67 points67 :=
 ⟨Manual.Count131072.C000067.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000067.count_checked,Manual.Count131072.C000067.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.checked67,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000016.point_links_checked67⟩
def segment67 : PointSegment := ⟨12713985,5,2048,177508535386,177509426424,20635912532192,20636102851710,cuts67,points67,packet67⟩
def segments : List PointSegment := [segment64,segment65,segment66,segment67]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 12320768 20095105242591 20095292790402 12845056 20813421067578 20813612278134 segments = true := by decide +kernel
theorem certified : PointChainCertificate 12320768 20095105242591 20095292790402 12845056 20813421067578 20813612278134 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000016
