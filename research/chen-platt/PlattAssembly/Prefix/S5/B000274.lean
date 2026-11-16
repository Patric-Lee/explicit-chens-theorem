import PlattAssemblyKernel
import PlattCertificates.Count131072.C048768
import PlattCertificates.Count131072.C048769
import PlattCertificates.Count131072.C048770
import PlattCertificates.Count131072.C048771
import PlattCertificates.Count131072.C048772
import PlattCertificates.Count131072.C048773
import PlattCertificates.Count131072.C048774
import PlattCertificates.Count131072.C048775
import PlattCertificates.Count131072.C048776
import PlattCertificates.Count131072.C048777
import PlattCertificates.Count131072.C048778
import PlattCertificates.Count131072.C048779
import PlattCertificates.Count131072.C048780
import PlattCertificates.Count131072.C048781
import PlattCertificates.Count131072.C048782
import PlattCertificates.Count131072.C048783
import PlattCertificates.Count131072.C048784
import PlattCertificates.Count131072.C048785
import PlattCertificates.Count131072.C048786
import PlattCertificates.Count131072.C048787
import PlattCertificates.Count131072.C048788
import PlattCertificates.Count131072.C048789
import PlattCertificates.Count131072.C048790
import PlattCertificates.Count131072.C048791
import PlattCertificates.Count131072.C048792
import PlattCertificates.Count131072.C048793
import PlattCertificates.Count131072.C048794
import PlattCertificates.Count131072.C048795
import PlattCertificates.Count131072.C048796
import PlattCertificates.Count131072.C048797
import PlattCertificates.Count131072.C048798
import PlattCertificates.Count131072.C048799
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000274
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48768 : List PrefixCut := [⟨30,115211350,115211421⟩,
⟨64,253525166,253525317⟩]
theorem checked48768 : checkPrefixCuts (2^48) 6396051457 10 Manual.Count131072.C048768.packed 64 cuts48768 = true := by
 decide +kernel
def pointBounds48768 : List (Nat × Nat × Nat) := [(6396112896,111346328531703,111346715476664)]
theorem point_links_checked48768 : (cuts48768.take 1).map (fun c => (6396051457-1+2*2^10*c.k,111346213320353+c.lower,111346600265243+c.upper)) = pointBounds48768 := by
 decide +kernel
def cuts48769 : List PrefixCut := [⟨64,255412272,255412411⟩]
theorem checked48769 : checkPrefixCuts (2^48) 6396182529 10 Manual.Count131072.C048769.packed 64 cuts48769 = true := by
 decide +kernel
def pointBounds48769 : List (Nat × Nat × Nat) := [(6396313600,111346722257791,111347109202971)]
theorem point_links_checked48769 : (cuts48769.take 1).map (fun c => (6396182529-1+2*2^10*c.k,111346466845519+c.lower,111346853790560+c.upper)) = pointBounds48769 := by
 decide +kernel
def cuts48770 : List PrefixCut := [⟨64,255231014,255231163⟩]
theorem checked48770 : checkPrefixCuts (2^48) 6396313601 10 Manual.Count131072.C048770.packed 64 cuts48770 = true := by
 decide +kernel
def cuts48771 : List PrefixCut := [⟨34,135974392,135974468⟩,
⟨64,255357804,255357949⟩]
theorem checked48771 : checkPrefixCuts (2^48) 6396444673 10 Manual.Count131072.C048771.packed 64 cuts48771 = true := by
 decide +kernel
def pointBounds48771 : List (Nat × Nat × Nat) := [(6396514304,111347113463197,111347500408602)]
theorem point_links_checked48771 : (cuts48771.take 1).map (fun c => (6396444673-1+2*2^10*c.k,111346977488805+c.lower,111347364434134+c.upper)) = pointBounds48771 := by
 decide +kernel
def cuts48772 : List PrefixCut := [⟨64,253988463,253988610⟩]
theorem checked48772 : checkPrefixCuts (2^48) 6396575745 10 Manual.Count131072.C048772.packed 64 cuts48772 = true := by
 decide +kernel
def cuts48773 : List PrefixCut := [⟨4,15973113,15973122⟩,
⟨64,255875362,255875506⟩]
theorem checked48773 : checkPrefixCuts (2^48) 6396706817 10 Manual.Count131072.C048773.packed 64 cuts48773 = true := by
 decide +kernel
def pointBounds48773 : List (Nat × Nat × Nat) := [(6396715008,111347502808185,111347889753815)]
theorem point_links_checked48773 : (cuts48773.take 1).map (fun c => (6396706817-1+2*2^10*c.k,111347486835072+c.lower,111347873780693+c.upper)) = pointBounds48773 := by
 decide +kernel
def cuts48774 : List PrefixCut := [⟨38,151630638,151630727⟩,
⟨64,257014173,257014323⟩]
theorem checked48774 : checkPrefixCuts (2^48) 6396837889 10 Manual.Count131072.C048774.packed 64 cuts48774 = true := by
 decide +kernel
def pointBounds48774 : List (Nat × Nat × Nat) := [(6396915712,111347894341072,111348281286926)]
theorem point_links_checked48774 : (cuts48774.take 1).map (fun c => (6396837889-1+2*2^10*c.k,111347742710434+c.lower,111348129656199+c.upper)) = pointBounds48774 := by
 decide +kernel
def cuts48775 : List PrefixCut := [⟨64,250232778,250232922⟩]
theorem checked48775 : checkPrefixCuts (2^48) 6396968961 10 Manual.Count131072.C048775.packed 64 cuts48775 = true := by
 decide +kernel
def cuts48776 : List PrefixCut := [⟨8,32076243,32076261⟩,
⟨64,253219653,253219800⟩]
theorem checked48776 : checkPrefixCuts (2^48) 6397100033 10 Manual.Count131072.C048776.packed 64 cuts48776 = true := by
 decide +kernel
def pointBounds48776 : List (Nat × Nat × Nat) := [(6397116416,111348282033628,111348668979705)]
theorem point_links_checked48776 : (cuts48776.take 1).map (fun c => (6397100033-1+2*2^10*c.k,111348249957385+c.lower,111348636903444+c.upper)) = pointBounds48776 := by
 decide +kernel
def cuts48777 : List PrefixCut := [⟨42,168384906,168385004⟩,
⟨64,255678402,255678554⟩]
theorem checked48777 : checkPrefixCuts (2^48) 6397231105 10 Manual.Count131072.C048777.packed 64 cuts48777 = true := by
 decide +kernel
def pointBounds48777 : List (Nat × Nat × Nat) := [(6397317120,111348671561944,111349058508248)]
theorem point_links_checked48777 : (cuts48777.take 1).map (fun c => (6397231105-1+2*2^10*c.k,111348503177038+c.lower,111348890123244+c.upper)) = pointBounds48777 := by
 decide +kernel
def cuts48778 : List PrefixCut := [⟨64,254221222,254221370⟩]
theorem checked48778 : checkPrefixCuts (2^48) 6397362177 10 Manual.Count131072.C048778.packed 64 cuts48778 = true := by
 decide +kernel
def cuts48779 : List PrefixCut := [⟨12,48617351,48617378⟩,
⟨64,256459908,256460060⟩]
theorem checked48779 : checkPrefixCuts (2^48) 6397493249 10 Manual.Count131072.C048779.packed 64 cuts48779 = true := by
 decide +kernel
def pointBounds48779 : List (Nat × Nat × Nat) := [(6397517824,111349061694013,111349448640546)]
theorem point_links_checked48779 : (cuts48779.take 1).map (fun c => (6397493249-1+2*2^10*c.k,111349013076662+c.lower,111349400023168+c.upper)) = pointBounds48779 := by
 decide +kernel
def cuts48780 : List PrefixCut := [⟨46,182233340,182233447⟩,
⟨64,253374883,253375033⟩]
theorem checked48780 : checkPrefixCuts (2^48) 6397624321 10 Manual.Count131072.C048780.packed 64 cuts48780 = true := by
 decide +kernel
def pointBounds48780 : List (Nat × Nat × Nat) := [(6397718528,111349451769910,111349838716675)]
theorem point_links_checked48780 : (cuts48780.take 1).map (fun c => (6397624321-1+2*2^10*c.k,111349269536570+c.lower,111349656483228+c.upper)) = pointBounds48780 := by
 decide +kernel
def cuts48781 : List PrefixCut := [⟨64,253017736,253017885⟩]
theorem checked48781 : checkPrefixCuts (2^48) 6397755393 10 Manual.Count131072.C048781.packed 64 cuts48781 = true := by
 decide +kernel
def cuts48782 : List PrefixCut := [⟨16,63176634,63176672⟩,
⟨64,254948312,254948464⟩]
theorem checked48782 : checkPrefixCuts (2^48) 6397886465 10 Manual.Count131072.C048782.packed 64 cuts48782 = true := by
 decide +kernel
def pointBounds48782 : List (Nat × Nat × Nat) := [(6397919232,111349839105823,111350226052818)]
theorem point_links_checked48782 : (cuts48782.take 1).map (fun c => (6397886465-1+2*2^10*c.k,111349775929189+c.lower,111350162876146+c.upper)) = pointBounds48782 := by
 decide +kernel
def cuts48783 : List PrefixCut := [⟨50,200083477,200083593⟩,
⟨64,256130911,256131060⟩]
theorem checked48783 : checkPrefixCuts (2^48) 6398017537 10 Manual.Count131072.C048783.packed 64 cuts48783 = true := by
 decide +kernel
def pointBounds48783 : List (Nat × Nat × Nat) := [(6398119936,111350230960978,111350617908203)]
theorem point_links_checked48783 : (cuts48783.take 1).map (fun c => (6398017537-1+2*2^10*c.k,111350030877501+c.lower,111350417824610+c.upper)) = pointBounds48783 := by
 decide +kernel
def cuts48784 : List PrefixCut := [⟨64,255377788,255377930⟩]
theorem checked48784 : checkPrefixCuts (2^48) 6398148609 10 Manual.Count131072.C048784.packed 64 cuts48784 = true := by
 decide +kernel
def cuts48785 : List PrefixCut := [⟨20,79009875,79009923⟩,
⟨64,252293120,252293269⟩]
theorem checked48785 : checkPrefixCuts (2^48) 6398279681 10 Manual.Count131072.C048785.packed 64 cuts48785 = true := by
 decide +kernel
def pointBounds48785 : List (Nat × Nat × Nat) := [(6398320640,111350621396075,111351008343523)]
theorem point_links_checked48785 : (cuts48785.take 1).map (fun c => (6398279681-1+2*2^10*c.k,111350542386200+c.lower,111350929333600+c.upper)) = pointBounds48785 := by
 decide +kernel
def cuts48786 : List PrefixCut := [⟨54,217975403,217975522⟩,
⟨64,257302952,257303093⟩]
theorem checked48786 : checkPrefixCuts (2^48) 6398410753 10 Manual.Count131072.C048786.packed 64 cuts48786 = true := by
 decide +kernel
def pointBounds48786 : List (Nat × Nat × Nat) := [(6398521344,111351012654723,111351399602391)]
theorem point_links_checked48786 : (cuts48786.take 1).map (fun c => (6398410753-1+2*2^10*c.k,111350794679320+c.lower,111351181626869+c.upper)) = pointBounds48786 := by
 decide +kernel
def cuts48787 : List PrefixCut := [⟨64,254746246,254746386⟩]
theorem checked48787 : checkPrefixCuts (2^48) 6398541825 10 Manual.Count131072.C048787.packed 64 cuts48787 = true := by
 decide +kernel
def cuts48788 : List PrefixCut := [⟨24,94753180,94753232⟩,
⟨64,256632542,256632686⟩]
theorem checked48788 : checkPrefixCuts (2^48) 6398672897 10 Manual.Count131072.C048788.packed 64 cuts48788 = true := by
 decide +kernel
def pointBounds48788 : List (Nat × Nat × Nat) := [(6398722048,111351401481698,111351788429580)]
theorem point_links_checked48788 : (cuts48788.take 1).map (fun c => (6398672897-1+2*2^10*c.k,111351306728518+c.lower,111351693676348+c.upper)) = pointBounds48788 := by
 decide +kernel
def cuts48789 : List PrefixCut := [⟨58,231774146,231774281⟩,
⟨64,255659529,255659678⟩]
theorem checked48789 : checkPrefixCuts (2^48) 6398803969 10 Manual.Count131072.C048789.packed 64 cuts48789 = true := by
 decide +kernel
def pointBounds48789 : List (Nat × Nat × Nat) := [(6398922752,111351795135206,111352182083315)]
theorem point_links_checked48789 : (cuts48789.take 1).map (fun c => (6398803969-1+2*2^10*c.k,111351563361060+c.lower,111351950309034+c.upper)) = pointBounds48789 := by
 decide +kernel
def cuts48790 : List PrefixCut := [⟨64,252179305,252179445⟩]
theorem checked48790 : checkPrefixCuts (2^48) 6398935041 10 Manual.Count131072.C048790.packed 64 cuts48790 = true := by
 decide +kernel
def cuts48791 : List PrefixCut := [⟨28,112297972,112298036⟩,
⟨64,257232582,257232728⟩]
theorem checked48791 : checkPrefixCuts (2^48) 6399066113 10 Manual.Count131072.C048791.packed 64 cuts48791 = true := by
 decide +kernel
def pointBounds48791 : List (Nat × Nat × Nat) := [(6399123456,111352183497866,111352570446193)]
theorem point_links_checked48791 : (cuts48791.take 1).map (fun c => (6399066113-1+2*2^10*c.k,111352071199894+c.lower,111352458148157+c.upper)) = pointBounds48791 := by
 decide +kernel
def cuts48792 : List PrefixCut := [⟨62,241304646,241304780⟩,
⟨64,250145648,250145787⟩]
theorem checked48792 : checkPrefixCuts (2^48) 6399197185 10 Manual.Count131072.C048792.packed 64 cuts48792 = true := by
 decide +kernel
def pointBounds48792 : List (Nat × Nat × Nat) := [(6399324160,111352569737122,111352956685665)]
theorem point_links_checked48792 : (cuts48792.take 1).map (fun c => (6399197185-1+2*2^10*c.k,111352328432476+c.lower,111352715380885+c.upper)) = pointBounds48792 := by
 decide +kernel
def cuts48793 : List PrefixCut := [⟨64,253087506,253087649⟩]
theorem checked48793 : checkPrefixCuts (2^48) 6399328257 10 Manual.Count131072.C048793.packed 64 cuts48793 = true := by
 decide +kernel
def cuts48794 : List PrefixCut := [⟨32,127509447,127509521⟩,
⟨64,255017587,255017731⟩]
theorem checked48794 : checkPrefixCuts (2^48) 6399459329 10 Manual.Count131072.C048794.packed 64 cuts48794 = true := by
 decide +kernel
def pointBounds48794 : List (Nat × Nat × Nat) := [(6399524864,111352959175077,111353346123842)]
theorem point_links_checked48794 : (cuts48794.take 1).map (fun c => (6399459329-1+2*2^10*c.k,111352831665630+c.lower,111353218614321+c.upper)) = pointBounds48794 := by
 decide +kernel
def cuts48795 : List PrefixCut := [⟨64,255056355,255056507⟩]
theorem checked48795 : checkPrefixCuts (2^48) 6399590401 10 Manual.Count131072.C048795.packed 64 cuts48795 = true := by
 decide +kernel
def cuts48796 : List PrefixCut := [⟨2,8488594,8488599⟩,
⟨64,254567345,254567489⟩]
theorem checked48796 : checkPrefixCuts (2^48) 6399721473 10 Manual.Count131072.C048796.packed 64 cuts48796 = true := by
 decide +kernel
def pointBounds48796 : List (Nat × Nat × Nat) := [(6399725568,111353350228166,111353737177158)]
theorem point_links_checked48796 : (cuts48796.take 1).map (fun c => (6399721473-1+2*2^10*c.k,111353341739572+c.lower,111353728688559+c.upper)) = pointBounds48796 := by
 decide +kernel
def cuts48797 : List PrefixCut := [⟨36,147688917,147688999⟩,
⟨64,259400047,259400194⟩]
theorem checked48797 : checkPrefixCuts (2^48) 6399852545 10 Manual.Count131072.C048797.packed 64 cuts48797 = true := by
 decide +kernel
def pointBounds48797 : List (Nat × Nat × Nat) := [(6399926272,111353743995834,111354130945047)]
theorem point_links_checked48797 : (cuts48797.take 1).map (fun c => (6399852545-1+2*2^10*c.k,111353596306917+c.lower,111353983256048+c.upper)) = pointBounds48797 := by
 decide +kernel
def cuts48798 : List PrefixCut := [⟨64,258295210,258295353⟩]
theorem checked48798 : checkPrefixCuts (2^48) 6399983617 10 Manual.Count131072.C048798.packed 64 cuts48798 = true := by
 decide +kernel
def cuts48799 : List PrefixCut := [⟨6,23573077,23573090⟩,
⟨64,254067906,254068048⟩]
theorem checked48799 : checkPrefixCuts (2^48) 6400114689 10 Manual.Count131072.C048799.packed 64 cuts48799 = true := by
 decide +kernel
def pointBounds48799 : List (Nat × Nat × Nat) := [(6400126976,111354137575251,111354524524685)]
theorem point_links_checked48799 : (cuts48799.take 1).map (fun c => (6400114689-1+2*2^10*c.k,111354114002174+c.lower,111354500951595+c.upper)) = pointBounds48799 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000274
