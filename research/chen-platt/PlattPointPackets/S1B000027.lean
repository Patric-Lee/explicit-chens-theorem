import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000027
namespace ChenEffective.PlattWindow.PointPackets.S1B000027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts108 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.cuts108
abbrev points108 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.pointBounds108
opaque packet108 : CheckedPointSegment 18087937 6 1024 121175880761 121176736207 26635896885083 26636117416315 cuts108 points108 :=
 ⟨Manual.Count131072.C000108.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000108.count_checked,Manual.Count131072.C000108.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.checked108,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.point_links_checked108⟩
def segment108 : PointSegment := ⟨18087937,6,1024,121175880761,121176736207,26635896885083,26636117416315,cuts108,points108,packet108⟩
abbrev cuts109 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.cuts109
abbrev points109 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.pointBounds109
opaque packet109 : CheckedPointSegment 18219009 6 1024 121924741108 121925595668 26757072765844 26757294152522 cuts109 points109 :=
 ⟨Manual.Count131072.C000109.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000109.count_checked,Manual.Count131072.C000109.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.checked109,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.point_links_checked109⟩
def segment109 : PointSegment := ⟨18219009,6,1024,121924741108,121925595668,26757072765844,26757294152522,cuts109,points109,packet109⟩
abbrev cuts110 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.cuts110
abbrev points110 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.pointBounds110
opaque packet110 : CheckedPointSegment 18350081 6 1024 118929575692 118930403373 26878997506952 26879219748190 cuts110 points110 :=
 ⟨Manual.Count131072.C000110.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000110.count_checked,Manual.Count131072.C000110.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.checked110,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.point_links_checked110⟩
def segment110 : PointSegment := ⟨18350081,6,1024,118929575692,118930403373,26878997506952,26879219748190,cuts110,points110,packet110⟩
abbrev cuts111 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.cuts111
abbrev points111 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.pointBounds111
opaque packet111 : CheckedPointSegment 18481153 6 1024 118921427305 118922249063 26997927082644 26998150151563 cuts111 points111 :=
 ⟨Manual.Count131072.C000111.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000111.count_checked,Manual.Count131072.C000111.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.checked111,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000027.point_links_checked111⟩
def segment111 : PointSegment := ⟨18481153,6,1024,118921427305,118922249063,26997927082644,26998150151563,cuts111,points111,packet111⟩
def segments : List PointSegment := [segment108,segment109,segment110,segment111]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 18087936 26635896885083 26636117416315 18612224 27116848509949 27117072400626 segments = true := by decide +kernel
theorem certified : PointChainCertificate 18087936 26635896885083 26636117416315 18612224 27116848509949 27117072400626 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000027
