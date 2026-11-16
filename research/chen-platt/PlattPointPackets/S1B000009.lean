import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000009
namespace ChenEffective.PlattWindow.PointPackets.S1B000009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts36 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.cuts36
abbrev points36 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.pointBounds36
opaque packet36 : CheckedPointSegment 8650753 5 2048 266357487758 266359445660 13931449081582 13931598140507 cuts36 points36 :=
 ⟨Manual.Count131072.C000036.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000036.count_checked,Manual.Count131072.C000036.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.checked36,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.point_links_checked36⟩
def segment36 : PointSegment := ⟨8650753,5,2048,266357487758,266359445660,13931449081582,13931598140507,cuts36,points36,packet36⟩
abbrev cuts37 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.cuts37
abbrev points37 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.pointBounds37
opaque packet37 : CheckedPointSegment 8781825 5 2048 259261399540 259263277087 14197806569340 14197957586167 cuts37 points37 :=
 ⟨Manual.Count131072.C000037.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000037.count_checked,Manual.Count131072.C000037.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.checked37,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.point_links_checked37⟩
def segment37 : PointSegment := ⟨8781825,5,2048,259261399540,259263277087,14197806569340,14197957586167,cuts37,points37,packet37⟩
abbrev cuts38 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.cuts38
abbrev points38 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.pointBounds38
opaque packet38 : CheckedPointSegment 8912897 5 2048 255642813025 255644637473 14457067968880 14457220863254 cuts38 points38 :=
 ⟨Manual.Count131072.C000038.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000038.count_checked,Manual.Count131072.C000038.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.checked38,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.point_links_checked38⟩
def segment38 : PointSegment := ⟨8912897,5,2048,255642813025,255644637473,14457067968880,14457220863254,cuts38,points38,packet38⟩
abbrev cuts39 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.cuts39
abbrev points39 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.pointBounds39
opaque packet39 : CheckedPointSegment 9043969 5 2048 252264714892 252266489357 14712710781905 14712865500727 cuts39 points39 :=
 ⟨Manual.Count131072.C000039.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000039.count_checked,Manual.Count131072.C000039.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.checked39,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000009.point_links_checked39⟩
def segment39 : PointSegment := ⟨9043969,5,2048,252264714892,252266489357,14712710781905,14712865500727,cuts39,points39,packet39⟩
def segments : List PointSegment := [segment36,segment37,segment38,segment39]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 8650752 13931449081582 13931598140507 9175040 14964975496797 14965131990084 segments = true := by decide +kernel
theorem certified : PointChainCertificate 8650752 13931449081582 13931598140507 9175040 14964975496797 14965131990084 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000009
