import PlattAssemblyKernel
import PlattCertificates.Count131072.C074736
import PlattCertificates.Count131072.C074737
import PlattCertificates.Count131072.C074738
import PlattCertificates.Count131072.C074739
import PlattCertificates.Count131072.C074740
import PlattCertificates.Count131072.C074741
import PlattCertificates.Count131072.C074742
import PlattCertificates.Count131072.C074743
import PlattCertificates.Count131072.C074744
import PlattCertificates.Count131072.C074745
import PlattCertificates.Count131072.C074746
import PlattCertificates.Count131072.C074747
import PlattCertificates.Count131072.C074748
import PlattCertificates.Count131072.C074749
import PlattCertificates.Count131072.C074750
import PlattCertificates.Count131072.C074751
import PlattCertificates.Count131072.C074752
import PlattCertificates.Count131072.C074753
import PlattCertificates.Count131072.C074754
import PlattCertificates.Count131072.C074755
import PlattCertificates.Count131072.C074756
import PlattCertificates.Count131072.C074757
import PlattCertificates.Count131072.C074758
import PlattCertificates.Count131072.C074759
import PlattCertificates.Count131072.C074760
import PlattCertificates.Count131072.C074761
import PlattCertificates.Count131072.C074762
import PlattCertificates.Count131072.C074763
import PlattCertificates.Count131072.C074764
import PlattCertificates.Count131072.C074765
import PlattCertificates.Count131072.C074766
import PlattCertificates.Count131072.C074767
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000148
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74736 : List PrefixCut := [⟨7,18899537,18899548⟩,
⟨64,165125823,165125926⟩]
theorem checked74736 : checkPrefixCuts (2^48) 9799729153 10 Manual.Count131072.C074736.packed 64 cuts74736 = true := by
 decide +kernel
def pointBounds74736 : List (Nat × Nat × Nat) := [(9799743488,116615614517569,116616004499069)]
theorem point_links_checked74736 : (cuts74736.take 1).map (fun c => (9799729153-1+2*2^10*c.k,116615595618032+c.lower,116615985599521+c.upper)) = pointBounds74736 := by
 decide +kernel
def cuts74737 : List PrefixCut := [⟨64,164778956,164779056⟩]
theorem checked74737 : checkPrefixCuts (2^48) 9799860225 10 Manual.Count131072.C074737.packed 64 cuts74737 = true := by
 decide +kernel
def cuts74738 : List PrefixCut := [⟨29,74389635,74389677⟩,
⟨64,165983053,165983154⟩]
theorem checked74738 : checkPrefixCuts (2^48) 9799991297 10 Manual.Count131072.C074738.packed 64 cuts74738 = true := by
 decide +kernel
def pointBounds74738 : List (Nat × Nat × Nat) := [(9800050688,116615999912446,116616389894180)]
theorem point_links_checked74738 : (cuts74738.take 1).map (fun c => (9799991297-1+2*2^10*c.k,116615925522811+c.lower,116616315504503+c.upper)) = pointBounds74738 := by
 decide +kernel
def cuts74739 : List PrefixCut := [⟨64,162103443,162103553⟩]
theorem checked74739 : checkPrefixCuts (2^48) 9800122369 10 Manual.Count131072.C074739.packed 64 cuts74739 = true := by
 decide +kernel
def cuts74740 : List PrefixCut := [⟨51,131341282,131341362⟩,
⟨64,164312806,164312906⟩]
theorem checked74740 : checkPrefixCuts (2^48) 9800253441 10 Manual.Count131072.C074740.packed 64 cuts74740 = true := by
 decide +kernel
def pointBounds74740 : List (Nat × Nat × Nat) := [(9800357888,116616384950589,116616774932572)]
theorem point_links_checked74740 : (cuts74740.take 1).map (fun c => (9800253441-1+2*2^10*c.k,116616253609307+c.lower,116616643591210+c.upper)) = pointBounds74740 := by
 decide +kernel
def cuts74741 : List PrefixCut := [⟨64,165459421,165459520⟩]
theorem checked74741 : checkPrefixCuts (2^48) 9800384513 10 Manual.Count131072.C074741.packed 64 cuts74741 = true := by
 decide +kernel
def cuts74742 : List PrefixCut := [⟨64,163475520,163475622⟩]
theorem checked74742 : checkPrefixCuts (2^48) 9800515585 10 Manual.Count131072.C074742.packed 64 cuts74742 = true := by
 decide +kernel
def cuts74743 : List PrefixCut := [⟨9,23607845,23607859⟩,
⟨64,166259160,166259251⟩]
theorem checked74743 : checkPrefixCuts (2^48) 9800646657 10 Manual.Count131072.C074743.packed 64 cuts74743 = true := by
 decide +kernel
def pointBounds74743 : List (Nat × Nat × Nat) := [(9800665088,116616770464899,116617160447117)]
theorem point_links_checked74743 : (cuts74743.take 1).map (fun c => (9800646657-1+2*2^10*c.k,116616746857054+c.lower,116617136839258+c.upper)) = pointBounds74743 := by
 decide +kernel
def cuts74744 : List PrefixCut := [⟨64,166084621,166084720⟩]
theorem checked74744 : checkPrefixCuts (2^48) 9800777729 10 Manual.Count131072.C074744.packed 64 cuts74744 = true := by
 decide +kernel
def cuts74745 : List PrefixCut := [⟨31,79896736,79896783⟩,
⟨64,163957192,163957291⟩]
theorem checked74745 : checkPrefixCuts (2^48) 9800908801 10 Manual.Count131072.C074745.packed 64 cuts74745 = true := by
 decide +kernel
def pointBounds74745 : List (Nat × Nat × Nat) := [(9800972288,116617159097571,116617549080012)]
theorem point_links_checked74745 : (cuts74745.take 1).map (fun c => (9800908801-1+2*2^10*c.k,116617079200835+c.lower,116617469183229+c.upper)) = pointBounds74745 := by
 decide +kernel
def cuts74746 : List PrefixCut := [⟨64,160422591,160422695⟩]
theorem checked74746 : checkPrefixCuts (2^48) 9801039873 10 Manual.Count131072.C074746.packed 64 cuts74746 = true := by
 decide +kernel
def cuts74747 : List PrefixCut := [⟨53,135895167,135895252⟩,
⟨64,164412286,164412387⟩]
theorem checked74747 : checkPrefixCuts (2^48) 9801170945 10 Manual.Count131072.C074747.packed 64 cuts74747 = true := by
 decide +kernel
def pointBounds74747 : List (Nat × Nat × Nat) := [(9801279488,116617539475785,116617929458467)]
theorem point_links_checked74747 : (cuts74747.take 1).map (fun c => (9801170945-1+2*2^10*c.k,116617403580618+c.lower,116617793563215+c.upper)) = pointBounds74747 := by
 decide +kernel
def cuts74748 : List PrefixCut := [⟨64,163002913,163003011⟩]
theorem checked74748 : checkPrefixCuts (2^48) 9801302017 10 Manual.Count131072.C074748.packed 64 cuts74748 = true := by
 decide +kernel
def cuts74749 : List PrefixCut := [⟨64,164149438,164149536⟩]
theorem checked74749 : checkPrefixCuts (2^48) 9801433089 10 Manual.Count131072.C074749.packed 64 cuts74749 = true := by
 decide +kernel
def cuts74750 : List PrefixCut := [⟨11,28516290,28516308⟩,
⟨64,164233391,164233497⟩]
theorem checked74750 : checkPrefixCuts (2^48) 9801564161 10 Manual.Count131072.C074750.packed 64 cuts74750 = true := by
 decide +kernel
def pointBounds74750 : List (Nat × Nat × Nat) := [(9801586688,116617923661545,116618313644457)]
theorem point_links_checked74750 : (cuts74750.take 1).map (fun c => (9801564161-1+2*2^10*c.k,116617895145255+c.lower,116618285128149+c.upper)) = pointBounds74750 := by
 decide +kernel
def cuts74751 : List PrefixCut := [⟨64,163312265,163312359⟩]
theorem checked74751 : checkPrefixCuts (2^48) 9801695233 10 Manual.Count131072.C074751.packed 64 cuts74751 = true := by
 decide +kernel
def cuts74752 : List PrefixCut := [⟨33,85058212,85058262⟩,
⟨64,164889485,164889581⟩]
theorem checked74752 : checkPrefixCuts (2^48) 9801826305 10 Manual.Count131072.C074752.packed 64 cuts74752 = true := by
 decide +kernel
def pointBounds74752 : List (Nat × Nat × Nat) := [(9801893888,116618307749123,116618697732267)]
theorem point_links_checked74752 : (cuts74752.take 1).map (fun c => (9801826305-1+2*2^10*c.k,116618222690911+c.lower,116618612674005+c.upper)) = pointBounds74752 := by
 decide +kernel
def cuts74753 : List PrefixCut := [⟨64,163221755,163221850⟩]
theorem checked74753 : checkPrefixCuts (2^48) 9801957377 10 Manual.Count131072.C074753.packed 64 cuts74753 = true := by
 decide +kernel
def cuts74754 : List PrefixCut := [⟨55,140333351,140333441⟩,
⟨64,164712770,164712874⟩]
theorem checked74754 : checkPrefixCuts (2^48) 9802088449 10 Manual.Count131072.C074754.packed 64 cuts74754 = true := by
 decide +kernel
def pointBounds74754 : List (Nat × Nat × Nat) := [(9802201088,116618691135502,116619081118877)]
theorem point_links_checked74754 : (cuts74754.take 1).map (fun c => (9802088449-1+2*2^10*c.k,116618550802151+c.lower,116618940785436+c.upper)) = pointBounds74754 := by
 decide +kernel
def cuts74755 : List PrefixCut := [⟨64,162327201,162327304⟩]
theorem checked74755 : checkPrefixCuts (2^48) 9802219521 10 Manual.Count131072.C074755.packed 64 cuts74755 = true := by
 decide +kernel
def cuts74756 : List PrefixCut := [⟨64,163473626,163473726⟩]
theorem checked74756 : checkPrefixCuts (2^48) 9802350593 10 Manual.Count131072.C074756.packed 64 cuts74756 = true := by
 decide +kernel
def cuts74757 : List PrefixCut := [⟨13,34514968,34514992⟩,
⟨64,165309170,165309276⟩]
theorem checked74757 : checkPrefixCuts (2^48) 9802481665 10 Manual.Count131072.C074757.packed 64 cuts74757 = true := by
 decide +kernel
def pointBounds74757 : List (Nat × Nat × Nat) := [(9802508288,116619075830716,116619465814332)]
theorem point_links_checked74757 : (cuts74757.take 1).map (fun c => (9802481665-1+2*2^10*c.k,116619041315748+c.lower,116619431299340+c.upper)) = pointBounds74757 := by
 decide +kernel
def cuts74758 : List PrefixCut := [⟨64,164445536,164445637⟩]
theorem checked74758 : checkPrefixCuts (2^48) 9802612737 10 Manual.Count131072.C074758.packed 64 cuts74758 = true := by
 decide +kernel
def cuts74759 : List PrefixCut := [⟨35,89299868,89299921⟩,
⟨64,162232393,162232490⟩]
theorem checked74759 : checkPrefixCuts (2^48) 9802743809 10 Manual.Count131072.C074759.packed 64 cuts74759 = true := by
 decide +kernel
def pointBounds74759 : List (Nat × Nat × Nat) := [(9802815488,116619460370322,116619850354174)]
theorem point_links_checked74759 : (cuts74759.take 1).map (fun c => (9802743809-1+2*2^10*c.k,116619371070454+c.lower,116619761054253+c.upper)) = pointBounds74759 := by
 decide +kernel
def cuts74760 : List PrefixCut := [⟨64,166278788,166278890⟩]
theorem checked74760 : checkPrefixCuts (2^48) 9802874881 10 Manual.Count131072.C074760.packed 64 cuts74760 = true := by
 decide +kernel
def cuts74761 : List PrefixCut := [⟨57,146493473,146493558⟩,
⟨64,163979543,163979638⟩]
theorem checked74761 : checkPrefixCuts (2^48) 9803005953 10 Manual.Count131072.C074761.packed 64 cuts74761 = true := by
 decide +kernel
def pointBounds74761 : List (Nat × Nat × Nat) := [(9803122688,116619846075108,116620236059191)]
theorem point_links_checked74761 : (cuts74761.take 1).map (fun c => (9803005953-1+2*2^10*c.k,116619699581635+c.lower,116620089565633+c.upper)) = pointBounds74761 := by
 decide +kernel
def cuts74762 : List PrefixCut := [⟨64,164781285,164781388⟩]
theorem checked74762 : checkPrefixCuts (2^48) 9803137025 10 Manual.Count131072.C074762.packed 64 cuts74762 = true := by
 decide +kernel
def cuts74763 : List PrefixCut := [⟨64,161994005,161994110⟩]
theorem checked74763 : checkPrefixCuts (2^48) 9803268097 10 Manual.Count131072.C074763.packed 64 cuts74763 = true := by
 decide +kernel
def cuts74764 : List PrefixCut := [⟨15,38588826,38588852⟩,
⟨64,162767067,162767166⟩]
theorem checked74764 : checkPrefixCuts (2^48) 9803399169 10 Manual.Count131072.C074764.packed 64 cuts74764 = true := by
 decide +kernel
def pointBounds74764 : List (Nat × Nat × Nat) := [(9803429888,116620228925294,116620618909621)]
theorem point_links_checked74764 : (cuts74764.take 1).map (fun c => (9803399169-1+2*2^10*c.k,116620190336468+c.lower,116620580320769+c.upper)) = pointBounds74764 := by
 decide +kernel
def cuts74765 : List PrefixCut := [⟨64,163482676,163482773⟩]
theorem checked74765 : checkPrefixCuts (2^48) 9803530241 10 Manual.Count131072.C074765.packed 64 cuts74765 = true := by
 decide +kernel
def cuts74766 : List PrefixCut := [⟨37,94918860,94918919⟩,
⟨64,164571500,164571600⟩]
theorem checked74766 : checkPrefixCuts (2^48) 9803661313 10 Manual.Count131072.C074766.packed 64 cuts74766 = true := by
 decide +kernel
def pointBounds74766 : List (Nat × Nat × Nat) := [(9803737088,116620611505071,116621001489627)]
theorem point_links_checked74766 : (cuts74766.take 1).map (fun c => (9803661313-1+2*2^10*c.k,116620516586211+c.lower,116620906570708+c.upper)) = pointBounds74766 := by
 decide +kernel
def cuts74767 : List PrefixCut := [⟨64,164999957,165000051⟩]
theorem checked74767 : checkPrefixCuts (2^48) 9803792385 10 Manual.Count131072.C074767.packed 64 cuts74767 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000148
