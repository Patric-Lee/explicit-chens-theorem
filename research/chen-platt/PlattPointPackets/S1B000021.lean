import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000021
namespace ChenEffective.PlattWindow.PointPackets.S1B000021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts84 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.cuts84
abbrev points84 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.pointBounds84
opaque packet84 : CheckedPointSegment 14942209 5 2048 148149114583 148149748405 23399198674354 23399401875058 cuts84 points84 :=
 ⟨Manual.Count131072.C000084.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000084.count_checked,Manual.Count131072.C000084.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.checked84,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.point_links_checked84⟩
def segment84 : PointSegment := ⟨14942209,5,2048,148149114583,148149748405,23399198674354,23399401875058,cuts84,points84,packet84⟩
abbrev cuts85 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.cuts85
abbrev points85 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.pointBounds85
opaque packet85 : CheckedPointSegment 15073281 5 2048 146887120259 146887743274 23547347788937 23547551623463 cuts85 points85 :=
 ⟨Manual.Count131072.C000085.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000085.count_checked,Manual.Count131072.C000085.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.checked85,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.point_links_checked85⟩
def segment85 : PointSegment := ⟨15073281,5,2048,146887120259,146887743274,23547347788937,23547551623463,cuts85,points85,packet85⟩
abbrev cuts86 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.cuts86
abbrev points86 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.pointBounds86
opaque packet86 : CheckedPointSegment 15204353 5 2048 146639639373 146640256036 23694234909196 23694439366737 cuts86 points86 :=
 ⟨Manual.Count131072.C000086.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000086.count_checked,Manual.Count131072.C000086.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.checked86,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.point_links_checked86⟩
def segment86 : PointSegment := ⟨15204353,5,2048,146639639373,146640256036,23694234909196,23694439366737,cuts86,points86,packet86⟩
abbrev cuts87 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.cuts87
abbrev points87 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.pointBounds87
opaque packet87 : CheckedPointSegment 15335425 5 2048 143580039349 143580638082 23840874548569 23841079622773 cuts87 points87 :=
 ⟨Manual.Count131072.C000087.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000087.count_checked,Manual.Count131072.C000087.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.checked87,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000021.point_links_checked87⟩
def segment87 : PointSegment := ⟨15335425,5,2048,143580039349,143580638082,23840874548569,23841079622773,cuts87,points87,packet87⟩
def segments : List PointSegment := [segment84,segment85,segment86,segment87]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 14942208 23399198674354 23399401875058 15466496 23984454587918 23984660260855 segments = true := by decide +kernel
theorem certified : PointChainCertificate 14942208 23399198674354 23399401875058 15466496 23984454587918 23984660260855 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000021
