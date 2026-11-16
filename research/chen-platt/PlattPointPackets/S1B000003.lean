import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000003
namespace ChenEffective.PlattWindow.PointPackets.S1B000003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts12 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.cuts12
abbrev points12 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.pointBounds12
opaque packet12 : CheckedPointSegment 5505025 5 2048 424451615616 424456494579 5854833677285 5854907069305 cuts12 points12 :=
 ⟨Manual.Count131072.C000012.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000012.count_checked,Manual.Count131072.C000012.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.checked12,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.point_links_checked12⟩
def segment12 : PointSegment := ⟨5505025,5,2048,424451615616,424456494579,5854833677285,5854907069305,cuts12,points12,packet12⟩
abbrev cuts13 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.cuts13
abbrev points13 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.pointBounds13
opaque packet13 : CheckedPointSegment 5636097 5 2048 414350608883 414355262335 6279285292901 6279363563884 cuts13 points13 :=
 ⟨Manual.Count131072.C000013.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000013.count_checked,Manual.Count131072.C000013.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.checked13,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.point_links_checked13⟩
def segment13 : PointSegment := ⟨5636097,5,2048,414350608883,414355262335,6279285292901,6279363563884,cuts13,points13,packet13⟩
abbrev cuts14 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.cuts14
abbrev points14 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.pointBounds14
opaque packet14 : CheckedPointSegment 5767169 5 2048 405797830808 405802285702 6693635901784 6693718826219 cuts14 points14 :=
 ⟨Manual.Count131072.C000014.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000014.count_checked,Manual.Count131072.C000014.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.checked14,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.point_links_checked14⟩
def segment14 : PointSegment := ⟨5767169,5,2048,405797830808,405802285702,6693635901784,6693718826219,cuts14,points14,packet14⟩
abbrev cuts15 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.cuts15
abbrev points15 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.pointBounds15
opaque packet15 : CheckedPointSegment 5898241 5 2048 399117504726 399121790289 7099433732592 7099521111921 cuts15 points15 :=
 ⟨Manual.Count131072.C000015.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000015.count_checked,Manual.Count131072.C000015.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.checked15,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000003.point_links_checked15⟩
def segment15 : PointSegment := ⟨5898241,5,2048,399117504726,399121790289,7099433732592,7099521111921,cuts15,points15,packet15⟩
def segments : List PointSegment := [segment12,segment13,segment14,segment15]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 5505024 5854833677285 5854907069305 6029312 7498551237318 7498642902210 segments = true := by decide +kernel
theorem certified : PointChainCertificate 5505024 5854833677285 5854907069305 6029312 7498551237318 7498642902210 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000003
