import PlattPointPacketKernel
import PlattAssembly.Prefix.S1.B000012
namespace ChenEffective.PlattWindow.PointPackets.S1B000012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev cuts48 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.cuts48
abbrev points48 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.pointBounds48
opaque packet48 : CheckedPointSegment 10223617 5 2048 222170192946 222171577000 16856063775090 16856232789125 cuts48 points48 :=
 ⟨Manual.Count131072.C000048.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000048.count_checked,Manual.Count131072.C000048.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.checked48,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.point_links_checked48⟩
def segment48 : PointSegment := ⟨10223617,5,2048,222170192946,222171577000,16856063775090,16856232789125,cuts48,points48,packet48⟩
abbrev cuts49 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.cuts49
abbrev points49 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.pointBounds49
opaque packet49 : CheckedPointSegment 10354689 5 2048 220667924060 220669281469 17078233968036 17078404366125 cuts49 points49 :=
 ⟨Manual.Count131072.C000049.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000049.count_checked,Manual.Count131072.C000049.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.checked49,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.point_links_checked49⟩
def segment49 : PointSegment := ⟨10354689,5,2048,220667924060,220669281469,17078233968036,17078404366125,cuts49,points49,packet49⟩
abbrev cuts50 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.cuts50
abbrev points50 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.pointBounds50
opaque packet50 : CheckedPointSegment 10485761 5 2048 216353440696 216354755104 17298901892096 17299073647594 cuts50 points50 :=
 ⟨Manual.Count131072.C000050.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000050.count_checked,Manual.Count131072.C000050.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.checked50,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.point_links_checked50⟩
def segment50 : PointSegment := ⟨10485761,5,2048,216353440696,216354755104,17298901892096,17299073647594,cuts50,points50,packet50⟩
abbrev cuts51 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.cuts51
abbrev points51 := ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.pointBounds51
opaque packet51 : CheckedPointSegment 10616833 5 2048 214752226790 214753515499 17515255332792 17515428402698 cuts51 points51 :=
 ⟨Manual.Count131072.C000051.packed,by decide +kernel,by decide +kernel,by decide +kernel,Manual.Count131072.C000051.count_checked,Manual.Count131072.C000051.arithmetic_checked,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.checked51,ChenEffective.PlattWindow.Assembly.Prefix.S1.B000012.point_links_checked51⟩
def segment51 : PointSegment := ⟨10616833,5,2048,214752226790,214753515499,17515255332792,17515428402698,cuts51,points51,packet51⟩
def segments : List PointSegment := [segment48,segment49,segment50,segment51]
def points : List PrimePoint := segments.flatMap PointSegment.points
theorem checked : checkPointChain 10223616 16856063775090 16856232789125 10747904 17730007559582 17730181918197 segments = true := by decide +kernel
theorem certified : PointChainCertificate 10223616 16856063775090 16856232789125 10747904 17730007559582 17730181918197 points := .leaf segments checked
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.S1B000012
