import PlattAssemblyKernel
import PlattCertificates.Count131072.C060768
import PlattCertificates.Count131072.C060769
import PlattCertificates.Count131072.C060770
import PlattCertificates.Count131072.C060771
import PlattCertificates.Count131072.C060772
import PlattCertificates.Count131072.C060773
import PlattCertificates.Count131072.C060774
import PlattCertificates.Count131072.C060775
import PlattCertificates.Count131072.C060776
import PlattCertificates.Count131072.C060777
import PlattCertificates.Count131072.C060778
import PlattCertificates.Count131072.C060779
import PlattCertificates.Count131072.C060780
import PlattCertificates.Count131072.C060781
import PlattCertificates.Count131072.C060782
import PlattCertificates.Count131072.C060783
import PlattCertificates.Count131072.C060784
import PlattCertificates.Count131072.C060785
import PlattCertificates.Count131072.C060786
import PlattCertificates.Count131072.C060787
import PlattCertificates.Count131072.C060788
import PlattCertificates.Count131072.C060789
import PlattCertificates.Count131072.C060790
import PlattCertificates.Count131072.C060791
import PlattCertificates.Count131072.C060792
import PlattCertificates.Count131072.C060793
import PlattCertificates.Count131072.C060794
import PlattCertificates.Count131072.C060795
import PlattCertificates.Count131072.C060796
import PlattCertificates.Count131072.C060797
import PlattCertificates.Count131072.C060798
import PlattCertificates.Count131072.C060799
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60768 : List PrefixCut := [⟨64,204263174,204263288⟩]
theorem checked60768 : checkPrefixCuts (2^48) 7968915457 10 Manual.Count131072.C060768.packed 64 cuts60768 = true := by
 decide +kernel
def pointBounds60768 : List (Nat × Nat × Nat) := [(7969046528,114073985439224,114074373936315)]
theorem point_links_checked60768 : (cuts60768.take 1).map (fun c => (7968915457-1+2*2^10*c.k,114073781176050+c.lower,114074169673027+c.upper)) = pointBounds60768 := by
 decide +kernel
def cuts60769 : List PrefixCut := [⟨64,203588699,203588816⟩]
theorem checked60769 : checkPrefixCuts (2^48) 7969046529 10 Manual.Count131072.C060769.packed 64 cuts60769 = true := by
 decide +kernel
def cuts60770 : List PrefixCut := [⟨58,185501610,185501717⟩,
⟨64,204468391,204468510⟩]
theorem checked60770 : checkPrefixCuts (2^48) 7969177601 10 Manual.Count131072.C060770.packed 64 cuts60770 = true := by
 decide +kernel
def pointBounds60770 : List (Nat × Nat × Nat) := [(7969296384,114074374529533,114074763026848)]
theorem point_links_checked60770 : (cuts60770.take 1).map (fun c => (7969177601-1+2*2^10*c.k,114074189027923+c.lower,114074577525131+c.upper)) = pointBounds60770 := by
 decide +kernel
def cuts60771 : List PrefixCut := [⟨64,203158172,203158292⟩]
theorem checked60771 : checkPrefixCuts (2^48) 7969308673 10 Manual.Count131072.C060771.packed 64 cuts60771 = true := by
 decide +kernel
def cuts60772 : List PrefixCut := [⟨52,166988457,166988554⟩,
⟨64,204461659,204461775⟩]
theorem checked60772 : checkPrefixCuts (2^48) 7969439745 10 Manual.Count131072.C060772.packed 64 cuts60772 = true := by
 decide +kernel
def pointBounds60772 : List (Nat × Nat × Nat) := [(7969546240,114074763642943,114075152140487)]
theorem point_links_checked60772 : (cuts60772.take 1).map (fun c => (7969439745-1+2*2^10*c.k,114074596654486+c.lower,114074985151933+c.upper)) = pointBounds60772 := by
 decide +kernel
def cuts60773 : List PrefixCut := [⟨64,203963831,203963943⟩]
theorem checked60773 : checkPrefixCuts (2^48) 7969570817 10 Manual.Count131072.C060773.packed 64 cuts60773 = true := by
 decide +kernel
def cuts60774 : List PrefixCut := [⟨46,147911408,147911491⟩,
⟨64,205867628,205867743⟩]
theorem checked60774 : checkPrefixCuts (2^48) 7969701889 10 Manual.Count131072.C060774.packed 64 cuts60774 = true := by
 decide +kernel
def pointBounds60774 : List (Nat × Nat × Nat) := [(7969796096,114075152991384,114075541489142)]
theorem point_links_checked60774 : (cuts60774.take 1).map (fun c => (7969701889-1+2*2^10*c.k,114075005079976+c.lower,114075393577651+c.upper)) = pointBounds60774 := by
 decide +kernel
def cuts60775 : List PrefixCut := [⟨64,201802769,201802885⟩]
theorem checked60775 : checkPrefixCuts (2^48) 7969832961 10 Manual.Count131072.C060775.packed 64 cuts60775 = true := by
 decide +kernel
def cuts60776 : List PrefixCut := [⟨40,127316990,127317064⟩,
⟨64,200810599,200810715⟩]
theorem checked60776 : checkPrefixCuts (2^48) 7969964033 10 Manual.Count131072.C060776.packed 64 cuts60776 = true := by
 decide +kernel
def pointBounds60776 : List (Nat × Nat × Nat) := [(7970045952,114075540067363,114075928565343)]
theorem point_links_checked60776 : (cuts60776.take 1).map (fun c => (7969964033-1+2*2^10*c.k,114075412750373+c.lower,114075801248279+c.upper)) = pointBounds60776 := by
 decide +kernel
def cuts60777 : List PrefixCut := [⟨64,204409521,204409636⟩]
theorem checked60777 : checkPrefixCuts (2^48) 7970095105 10 Manual.Count131072.C060777.packed 64 cuts60777 = true := by
 decide +kernel
def cuts60778 : List PrefixCut := [⟨34,109337234,109337296⟩,
⟨64,204688692,204688804⟩]
theorem checked60778 : checkPrefixCuts (2^48) 7970226177 10 Manual.Count131072.C060778.packed 64 cuts60778 = true := by
 decide +kernel
def pointBounds60778 : List (Nat × Nat × Nat) := [(7970295808,114075927307727,114076315805926)]
theorem point_links_checked60778 : (cuts60778.take 1).map (fun c => (7970226177-1+2*2^10*c.k,114075817970493+c.lower,114076206468630+c.upper)) = pointBounds60778 := by
 decide +kernel
def cuts60779 : List PrefixCut := [⟨64,206133221,206133340⟩]
theorem checked60779 : checkPrefixCuts (2^48) 7970357249 10 Manual.Count131072.C060779.packed 64 cuts60779 = true := by
 decide +kernel
def cuts60780 : List PrefixCut := [⟨28,86944325,86944374⟩,
⟨64,202315873,202315989⟩]
theorem checked60780 : checkPrefixCuts (2^48) 7970488321 10 Manual.Count131072.C060780.packed 64 cuts60780 = true := by
 decide +kernel
def pointBounds60780 : List (Nat × Nat × Nat) := [(7970545664,114076315736731,114076704235148)]
theorem point_links_checked60780 : (cuts60780.take 1).map (fun c => (7970488321-1+2*2^10*c.k,114076228792406+c.lower,114076617290774+c.upper)) = pointBounds60780 := by
 decide +kernel
def cuts60781 : List PrefixCut := [⟨64,203972291,203972410⟩]
theorem checked60781 : checkPrefixCuts (2^48) 7970619393 10 Manual.Count131072.C060781.packed 64 cuts60781 = true := by
 decide +kernel
def cuts60782 : List PrefixCut := [⟨22,69885171,69885212⟩,
⟨64,205875851,205875971⟩]
theorem checked60782 : checkPrefixCuts (2^48) 7970750465 10 Manual.Count131072.C060782.packed 64 cuts60782 = true := by
 decide +kernel
def pointBounds60782 : List (Nat × Nat × Nat) := [(7970795520,114076704965741,114077093464385)]
theorem point_links_checked60782 : (cuts60782.take 1).map (fun c => (7970750465-1+2*2^10*c.k,114076635080570+c.lower,114077023579173+c.upper)) = pointBounds60782 := by
 decide +kernel
def cuts60783 : List PrefixCut := [⟨64,202023411,202023531⟩]
theorem checked60783 : checkPrefixCuts (2^48) 7970881537 10 Manual.Count131072.C060783.packed 64 cuts60783 = true := by
 decide +kernel
def cuts60784 : List PrefixCut := [⟨16,51238063,51238092⟩,
⟨64,203644447,203644560⟩]
theorem checked60784 : checkPrefixCuts (2^48) 7971012609 10 Manual.Count131072.C060784.packed 64 cuts60784 = true := by
 decide +kernel
def pointBounds60784 : List (Nat × Nat × Nat) := [(7971045376,114077094217895,114077482716767)]
theorem point_links_checked60784 : (cuts60784.take 1).map (fun c => (7971012609-1+2*2^10*c.k,114077042979832+c.lower,114077431478675+c.upper)) = pointBounds60784 := by
 decide +kernel
def cuts60785 : List PrefixCut := [⟨64,199686206,199686321⟩]
theorem checked60785 : checkPrefixCuts (2^48) 7971143681 10 Manual.Count131072.C060785.packed 64 cuts60785 = true := by
 decide +kernel
def cuts60786 : List PrefixCut := [⟨10,30791285,30791303⟩,
⟨64,201024721,201024833⟩]
theorem checked60786 : checkPrefixCuts (2^48) 7971274753 10 Manual.Count131072.C060786.packed 64 cuts60786 = true := by
 decide +kernel
def pointBounds60786 : List (Nat × Nat × Nat) := [(7971295232,114077477101770,114077865600859)]
theorem point_links_checked60786 : (cuts60786.take 1).map (fun c => (7971274753-1+2*2^10*c.k,114077446310485+c.lower,114077834809556+c.upper)) = pointBounds60786 := by
 decide +kernel
def cuts60787 : List PrefixCut := [⟨64,201268602,201268716⟩]
theorem checked60787 : checkPrefixCuts (2^48) 7971405825 10 Manual.Count131072.C060787.packed 64 cuts60787 = true := by
 decide +kernel
def cuts60788 : List PrefixCut := [⟨4,12676280,12676288⟩,
⟨64,200029446,200029563⟩]
theorem checked60788 : checkPrefixCuts (2^48) 7971536897 10 Manual.Count131072.C060788.packed 64 cuts60788 = true := by
 decide +kernel
def pointBounds60788 : List (Nat × Nat × Nat) := [(7971545088,114077861280088,114078249779393)]
theorem point_links_checked60788 : (cuts60788.take 1).map (fun c => (7971536897-1+2*2^10*c.k,114077848603808+c.lower,114078237103105+c.upper)) = pointBounds60788 := by
 decide +kernel
def cuts60789 : List PrefixCut := [⟨62,192399447,192399561⟩,
⟨64,198048861,198048979⟩]
theorem checked60789 : checkPrefixCuts (2^48) 7971667969 10 Manual.Count131072.C060789.packed 64 cuts60789 = true := by
 decide +kernel
def pointBounds60789 : List (Nat × Nat × Nat) := [(7971794944,114078241032701,114078629532229)]
theorem point_links_checked60789 : (cuts60789.take 1).map (fun c => (7971667969-1+2*2^10*c.k,114078048633254+c.lower,114078437132668+c.upper)) = pointBounds60789 := by
 decide +kernel
def cuts60790 : List PrefixCut := [⟨64,204824840,204824954⟩]
theorem checked60790 : checkPrefixCuts (2^48) 7971799041 10 Manual.Count131072.C060790.packed 64 cuts60790 = true := by
 decide +kernel
def cuts60791 : List PrefixCut := [⟨56,176716513,176716615⟩,
⟨64,202138061,202138177⟩]
theorem checked60791 : checkPrefixCuts (2^48) 7971930113 10 Manual.Count131072.C060791.packed 64 cuts60791 = true := by
 decide +kernel
def pointBounds60791 : List (Nat × Nat × Nat) := [(7972044800,114078628223468,114079016723216)]
theorem point_links_checked60791 : (cuts60791.take 1).map (fun c => (7971930113-1+2*2^10*c.k,114078451506955+c.lower,114078840006601+c.upper)) = pointBounds60791 := by
 decide +kernel
def cuts60792 : List PrefixCut := [⟨64,202170044,202170158⟩]
theorem checked60792 : checkPrefixCuts (2^48) 7972061185 10 Manual.Count131072.C060792.packed 64 cuts60792 = true := by
 decide +kernel
def cuts60793 : List PrefixCut := [⟨50,156303472,156303556⟩,
⟨64,202025483,202025592⟩]
theorem checked60793 : checkPrefixCuts (2^48) 7972192257 10 Manual.Count131072.C060793.packed 64 cuts60793 = true := by
 decide +kernel
def pointBounds60793 : List (Nat × Nat × Nat) := [(7972294656,114079012118532,114079400618492)]
theorem point_links_checked60793 : (cuts60793.take 1).map (fun c => (7972192257-1+2*2^10*c.k,114078855815060+c.lower,114079244314936+c.upper)) = pointBounds60793 := by
 decide +kernel
def cuts60794 : List PrefixCut := [⟨64,200504016,200504131⟩]
theorem checked60794 : checkPrefixCuts (2^48) 7972323329 10 Manual.Count131072.C060794.packed 64 cuts60794 = true := by
 decide +kernel
def cuts60795 : List PrefixCut := [⟨44,140375578,140375658⟩,
⟨64,204101893,204102012⟩]
theorem checked60795 : checkPrefixCuts (2^48) 7972454401 10 Manual.Count131072.C060795.packed 64 cuts60795 = true := by
 decide +kernel
def pointBounds60795 : List (Nat × Nat × Nat) := [(7972544512,114079398720137,114079787220317)]
theorem point_links_checked60795 : (cuts60795.take 1).map (fun c => (7972454401-1+2*2^10*c.k,114079258344559+c.lower,114079646844659+c.upper)) = pointBounds60795 := by
 decide +kernel
def cuts60796 : List PrefixCut := [⟨64,208017392,208017506⟩]
theorem checked60796 : checkPrefixCuts (2^48) 7972585473 10 Manual.Count131072.C060796.packed 64 cuts60796 = true := by
 decide +kernel
def cuts60797 : List PrefixCut := [⟨38,119153000,119153069⟩,
⟨64,201412028,201412143⟩]
theorem checked60797 : checkPrefixCuts (2^48) 7972716545 10 Manual.Count131072.C060797.packed 64 cuts60797 = true := by
 decide +kernel
def pointBounds60797 : List (Nat × Nat × Nat) := [(7972794368,114079789616844,114080178117246)]
theorem point_links_checked60797 : (cuts60797.take 1).map (fun c => (7972716545-1+2*2^10*c.k,114079670463844+c.lower,114080058964177+c.upper)) = pointBounds60797 := by
 decide +kernel
def cuts60798 : List PrefixCut := [⟨64,201479344,201479458⟩]
theorem checked60798 : checkPrefixCuts (2^48) 7972847617 10 Manual.Count131072.C060798.packed 64 cuts60798 = true := by
 decide +kernel
def cuts60799 : List PrefixCut := [⟨32,102132914,102132971⟩,
⟨64,202817555,202817670⟩]
theorem checked60799 : checkPrefixCuts (2^48) 7972978689 10 Manual.Count131072.C060799.packed 64 cuts60799 = true := by
 decide +kernel
def pointBounds60799 : List (Nat × Nat × Nat) := [(7973044224,114080175488130,114080563988749)]
theorem point_links_checked60799 : (cuts60799.take 1).map (fun c => (7972978689-1+2*2^10*c.k,114080073355216+c.lower,114080461855778+c.upper)) = pointBounds60799 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000024
