import PlattAssemblyKernel
import PlattCertificates.Count131072.C074064
import PlattCertificates.Count131072.C074065
import PlattCertificates.Count131072.C074066
import PlattCertificates.Count131072.C074067
import PlattCertificates.Count131072.C074068
import PlattCertificates.Count131072.C074069
import PlattCertificates.Count131072.C074070
import PlattCertificates.Count131072.C074071
import PlattCertificates.Count131072.C074072
import PlattCertificates.Count131072.C074073
import PlattCertificates.Count131072.C074074
import PlattCertificates.Count131072.C074075
import PlattCertificates.Count131072.C074076
import PlattCertificates.Count131072.C074077
import PlattCertificates.Count131072.C074078
import PlattCertificates.Count131072.C074079
import PlattCertificates.Count131072.C074080
import PlattCertificates.Count131072.C074081
import PlattCertificates.Count131072.C074082
import PlattCertificates.Count131072.C074083
import PlattCertificates.Count131072.C074084
import PlattCertificates.Count131072.C074085
import PlattCertificates.Count131072.C074086
import PlattCertificates.Count131072.C074087
import PlattCertificates.Count131072.C074088
import PlattCertificates.Count131072.C074089
import PlattCertificates.Count131072.C074090
import PlattCertificates.Count131072.C074091
import PlattCertificates.Count131072.C074092
import PlattCertificates.Count131072.C074093
import PlattCertificates.Count131072.C074094
import PlattCertificates.Count131072.C074095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000127
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74064 : List PrefixCut := [⟨64,165522076,165522171⟩]
theorem checked74064 : checkPrefixCuts (2^48) 9711648769 10 Manual.Count131072.C074064.packed 64 cuts74064 = true := by
 decide +kernel
def cuts74065 : List PrefixCut := [⟨64,165287993,165288087⟩]
theorem checked74065 : checkPrefixCuts (2^48) 9711779841 10 Manual.Count131072.C074065.packed 64 cuts74065 = true := by
 decide +kernel
def cuts74066 : List PrefixCut := [⟨11,28228866,28228882⟩,
⟨64,166734860,166734963⟩]
theorem checked74066 : checkPrefixCuts (2^48) 9711910913 10 Manual.Count131072.C074066.packed 64 cuts74066 = true := by
 decide +kernel
def pointBounds74066 : List (Nat × Nat × Nat) := [(9711933440,116505478402759,116505868318351)]
theorem point_links_checked74066 : (cuts74066.take 1).map (fun c => (9711910913-1+2*2^10*c.k,116505450173893+c.lower,116505840089469+c.upper)) = pointBounds74066 := by
 decide +kernel
def cuts74067 : List PrefixCut := [⟨64,167022428,167022527⟩]
theorem checked74067 : checkPrefixCuts (2^48) 9712041985 10 Manual.Count131072.C074067.packed 64 cuts74067 = true := by
 decide +kernel
def cuts74068 : List PrefixCut := [⟨32,83003189,83003240⟩,
⟨64,164614712,164614814⟩]
theorem checked74068 : checkPrefixCuts (2^48) 9712173057 10 Manual.Count131072.C074068.packed 64 cuts74068 = true := by
 decide +kernel
def pointBounds74068 : List (Nat × Nat × Nat) := [(9712238592,116505866934370,116506256850199)]
theorem point_links_checked74068 : (cuts74068.take 1).map (fun c => (9712173057-1+2*2^10*c.k,116505783931181+c.lower,116506173846959+c.upper)) = pointBounds74068 := by
 decide +kernel
def cuts74069 : List PrefixCut := [⟨64,165221100,165221200⟩]
theorem checked74069 : checkPrefixCuts (2^48) 9712304129 10 Manual.Count131072.C074069.packed 64 cuts74069 = true := by
 decide +kernel
def cuts74070 : List PrefixCut := [⟨53,137542471,137542547⟩,
⟨64,165276829,165276922⟩]
theorem checked74070 : checkPrefixCuts (2^48) 9712435201 10 Manual.Count131072.C074070.packed 64 cuts74070 = true := by
 decide +kernel
def pointBounds74070 : List (Nat × Nat × Nat) := [(9712543744,116506251309464,116506641225520)]
theorem point_links_checked74070 : (cuts74070.take 1).map (fun c => (9712435201-1+2*2^10*c.k,116506113766993+c.lower,116506503682973+c.upper)) = pointBounds74070 := by
 decide +kernel
def cuts74071 : List PrefixCut := [⟨64,165013760,165013861⟩]
theorem checked74071 : checkPrefixCuts (2^48) 9712566273 10 Manual.Count131072.C074071.packed 64 cuts74071 = true := by
 decide +kernel
def cuts74072 : List PrefixCut := [⟨64,165765025,165765123⟩]
theorem checked74072 : checkPrefixCuts (2^48) 9712697345 10 Manual.Count131072.C074072.packed 64 cuts74072 = true := by
 decide +kernel
def cuts74073 : List PrefixCut := [⟨10,26400481,26400497⟩,
⟨64,166110536,166110636⟩]
theorem checked74073 : checkPrefixCuts (2^48) 9712828417 10 Manual.Count131072.C074073.packed 64 cuts74073 = true := by
 decide +kernel
def pointBounds74073 : List (Nat × Nat × Nat) := [(9712848896,116506636223088,116507026139376)]
theorem point_links_checked74073 : (cuts74073.take 1).map (fun c => (9712828417-1+2*2^10*c.k,116506609822607+c.lower,116506999738879+c.upper)) = pointBounds74073 := by
 decide +kernel
def cuts74074 : List PrefixCut := [⟨64,164224657,164224754⟩]
theorem checked74074 : checkPrefixCuts (2^48) 9712959489 10 Manual.Count131072.C074074.packed 64 cuts74074 = true := by
 decide +kernel
def cuts74075 : List PrefixCut := [⟨31,79894622,79894670⟩,
⟨64,166192991,166193088⟩]
theorem checked74075 : checkPrefixCuts (2^48) 9713090561 10 Manual.Count131072.C074075.packed 64 cuts74075 = true := by
 decide +kernel
def pointBounds74075 : List (Nat × Nat × Nat) := [(9713154048,116507020052422,116507409968939)]
theorem point_links_checked74075 : (cuts74075.take 1).map (fun c => (9713090561-1+2*2^10*c.k,116506940157800+c.lower,116507330074269+c.upper)) = pointBounds74075 := by
 decide +kernel
def cuts74076 : List PrefixCut := [⟨64,166480541,166480643⟩]
theorem checked74076 : checkPrefixCuts (2^48) 9713221633 10 Manual.Count131072.C074076.packed 64 cuts74076 = true := by
 decide +kernel
def cuts74077 : List PrefixCut := [⟨52,133037908,133037994⟩,
⟨64,164102094,164102198⟩]
theorem checked74077 : checkPrefixCuts (2^48) 9713352705 10 Manual.Count131072.C074077.packed 64 cuts74077 = true := by
 decide +kernel
def pointBounds74077 : List (Nat × Nat × Nat) := [(9713459200,116507405869240,116507795785994)]
theorem point_links_checked74077 : (cuts74077.take 1).map (fun c => (9713352705-1+2*2^10*c.k,116507272831332+c.lower,116507662748000+c.upper)) = pointBounds74077 := by
 decide +kernel
def cuts74078 : List PrefixCut := [⟨64,164099887,164099980⟩]
theorem checked74078 : checkPrefixCuts (2^48) 9713483777 10 Manual.Count131072.C074078.packed 64 cuts74078 = true := by
 decide +kernel
def cuts74079 : List PrefixCut := [⟨64,164474378,164474477⟩]
theorem checked74079 : checkPrefixCuts (2^48) 9713614849 10 Manual.Count131072.C074079.packed 64 cuts74079 = true := by
 decide +kernel
def cuts74080 : List PrefixCut := [⟨9,23268482,23268496⟩,
⟨64,163892614,163892715⟩]
theorem checked74080 : checkPrefixCuts (2^48) 9713745921 10 Manual.Count131072.C074080.packed 64 cuts74080 = true := by
 decide +kernel
def pointBounds74080 : List (Nat × Nat × Nat) := [(9713764352,116507788776173,116508178693151)]
theorem point_links_checked74080 : (cuts74080.take 1).map (fun c => (9713745921-1+2*2^10*c.k,116507765507691+c.lower,116508155424655+c.upper)) = pointBounds74080 := by
 decide +kernel
def cuts74081 : List PrefixCut := [⟨64,167193702,167193799⟩]
theorem checked74081 : checkPrefixCuts (2^48) 9713876993 10 Manual.Count131072.C074081.packed 64 cuts74081 = true := by
 decide +kernel
def cuts74082 : List PrefixCut := [⟨30,76438933,76438977⟩,
⟨64,163743313,163743408⟩]
theorem checked74082 : checkPrefixCuts (2^48) 9714008065 10 Manual.Count131072.C074082.packed 64 cuts74082 = true := by
 decide +kernel
def pointBounds74082 : List (Nat × Nat × Nat) := [(9714069504,116508173032940,116508562950146)]
theorem point_links_checked74082 : (cuts74082.take 1).map (fun c => (9714008065-1+2*2^10*c.k,116508096594007+c.lower,116508486511169+c.upper)) = pointBounds74082 := by
 decide +kernel
def cuts74083 : List PrefixCut := [⟨64,166290965,166291067⟩]
theorem checked74083 : checkPrefixCuts (2^48) 9714139137 10 Manual.Count131072.C074083.packed 64 cuts74083 = true := by
 decide +kernel
def cuts74084 : List PrefixCut := [⟨51,133431012,133431085⟩,
⟨64,167128997,167129088⟩]
theorem checked74084 : checkPrefixCuts (2^48) 9714270209 10 Manual.Count131072.C074084.packed 64 cuts74084 = true := by
 decide +kernel
def pointBounds74084 : List (Nat × Nat × Nat) := [(9714374656,116508560059297,116508949976729)]
theorem point_links_checked74084 : (cuts74084.take 1).map (fun c => (9714270209-1+2*2^10*c.k,116508426628285+c.lower,116508816545644+c.upper)) = pointBounds74084 := by
 decide +kernel
def cuts74085 : List PrefixCut := [⟨64,164663883,164663974⟩]
theorem checked74085 : checkPrefixCuts (2^48) 9714401281 10 Manual.Count131072.C074085.packed 64 cuts74085 = true := by
 decide +kernel
def cuts74086 : List PrefixCut := [⟨64,165443963,165444064⟩]
theorem checked74086 : checkPrefixCuts (2^48) 9714532353 10 Manual.Count131072.C074086.packed 64 cuts74086 = true := by
 decide +kernel
def cuts74087 : List PrefixCut := [⟨8,20021176,20021189⟩,
⟨64,165499686,165499784⟩]
theorem checked74087 : checkPrefixCuts (2^48) 9714663425 10 Manual.Count131072.C074087.packed 64 cuts74087 = true := by
 decide +kernel
def pointBounds74087 : List (Nat × Nat × Nat) := [(9714679808,116508943886304,116509333803959)]
theorem point_links_checked74087 : (cuts74087.take 1).map (fun c => (9714663425-1+2*2^10*c.k,116508923865128+c.lower,116509313782770+c.upper)) = pointBounds74087 := by
 decide +kernel
def cuts74088 : List PrefixCut := [⟨64,165033867,165033967⟩]
theorem checked74088 : checkPrefixCuts (2^48) 9714794497 10 Manual.Count131072.C074088.packed 64 cuts74088 = true := by
 decide +kernel
def cuts74089 : List PrefixCut := [⟨29,75446632,75446674⟩,
⟨64,163959647,163959743⟩]
theorem checked74089 : checkPrefixCuts (2^48) 9714925569 10 Manual.Count131072.C074089.packed 64 cuts74089 = true := by
 decide +kernel
def pointBounds74089 : List (Nat × Nat × Nat) := [(9714984960,116509329845313,116509719763195)]
theorem point_links_checked74089 : (cuts74089.take 1).map (fun c => (9714925569-1+2*2^10*c.k,116509254398681+c.lower,116509644316521+c.upper)) = pointBounds74089 := by
 decide +kernel
def cuts74090 : List PrefixCut := [⟨64,166101423,166101518⟩]
theorem checked74090 : checkPrefixCuts (2^48) 9715056641 10 Manual.Count131072.C074090.packed 64 cuts74090 = true := by
 decide +kernel
def cuts74091 : List PrefixCut := [⟨50,128580018,128580096⟩,
⟨64,164389804,164389902⟩]
theorem checked74091 : checkPrefixCuts (2^48) 9715187713 10 Manual.Count131072.C074091.packed 64 cuts74091 = true := by
 decide +kernel
def pointBounds74091 : List (Nat × Nat × Nat) := [(9715290112,116509713039769,116510102957878)]
theorem point_links_checked74091 : (cuts74091.take 1).map (fun c => (9715187713-1+2*2^10*c.k,116509584459751+c.lower,116509974377782+c.upper)) = pointBounds74091 := by
 decide +kernel
def cuts74092 : List PrefixCut := [⟨64,163895052,163895147⟩]
theorem checked74092 : checkPrefixCuts (2^48) 9715318785 10 Manual.Count131072.C074092.packed 64 cuts74092 = true := by
 decide +kernel
def cuts74093 : List PrefixCut := [⟨64,165486285,165486383⟩]
theorem checked74093 : checkPrefixCuts (2^48) 9715449857 10 Manual.Count131072.C074093.packed 64 cuts74093 = true := by
 decide +kernel
def cuts74094 : List PrefixCut := [⟨7,17469799,17469809⟩,
⟨64,166179365,166179462⟩]
theorem checked74094 : checkPrefixCuts (2^48) 9715580929 10 Manual.Count131072.C074094.packed 64 cuts74094 = true := by
 decide +kernel
def pointBounds74094 : List (Nat × Nat × Nat) := [(9715595264,116510095700691,116510485619023)]
theorem point_links_checked74094 : (cuts74094.take 1).map (fun c => (9715580929-1+2*2^10*c.k,116510078230892+c.lower,116510468149214+c.upper)) = pointBounds74094 := by
 decide +kernel
def cuts74095 : List PrefixCut := [⟨64,165018290,165018387⟩]
theorem checked74095 : checkPrefixCuts (2^48) 9715712001 10 Manual.Count131072.C074095.packed 64 cuts74095 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000127
