import PlattAssemblyKernel
import PlattCertificates.Count131072.C072720
import PlattCertificates.Count131072.C072721
import PlattCertificates.Count131072.C072722
import PlattCertificates.Count131072.C072723
import PlattCertificates.Count131072.C072724
import PlattCertificates.Count131072.C072725
import PlattCertificates.Count131072.C072726
import PlattCertificates.Count131072.C072727
import PlattCertificates.Count131072.C072728
import PlattCertificates.Count131072.C072729
import PlattCertificates.Count131072.C072730
import PlattCertificates.Count131072.C072731
import PlattCertificates.Count131072.C072732
import PlattCertificates.Count131072.C072733
import PlattCertificates.Count131072.C072734
import PlattCertificates.Count131072.C072735
import PlattCertificates.Count131072.C072736
import PlattCertificates.Count131072.C072737
import PlattCertificates.Count131072.C072738
import PlattCertificates.Count131072.C072739
import PlattCertificates.Count131072.C072740
import PlattCertificates.Count131072.C072741
import PlattCertificates.Count131072.C072742
import PlattCertificates.Count131072.C072743
import PlattCertificates.Count131072.C072744
import PlattCertificates.Count131072.C072745
import PlattCertificates.Count131072.C072746
import PlattCertificates.Count131072.C072747
import PlattCertificates.Count131072.C072748
import PlattCertificates.Count131072.C072749
import PlattCertificates.Count131072.C072750
import PlattCertificates.Count131072.C072751
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000085
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72720 : List PrefixCut := [⟨64,169376936,169377044⟩]
theorem checked72720 : checkPrefixCuts (2^48) 9535488001 10 Manual.Count131072.C072720.packed 64 cuts72720 = true := by
 decide +kernel
def cuts72721 : List PrefixCut := [⟨54,139856703,139856789⟩,
⟨64,165448712,165448814⟩]
theorem checked72721 : checkPrefixCuts (2^48) 9535619073 10 Manual.Count131072.C072721.packed 64 cuts72721 = true := by
 decide +kernel
def pointBounds72721 : List (Nat × Nat × Nat) := [(9535729664,116281225973962,116281615755765)]
theorem point_links_checked72721 : (cuts72721.take 1).map (fun c => (9535619073-1+2*2^10*c.k,116281086117259+c.lower,116281475898976+c.upper)) = pointBounds72721 := by
 decide +kernel
def cuts72722 : List PrefixCut := [⟨64,168132558,168132657⟩]
theorem checked72722 : checkPrefixCuts (2^48) 9535750145 10 Manual.Count131072.C072722.packed 64 cuts72722 = true := by
 decide +kernel
def cuts72723 : List PrefixCut := [⟨64,167274239,167274335⟩]
theorem checked72723 : checkPrefixCuts (2^48) 9535881217 10 Manual.Count131072.C072723.packed 64 cuts72723 = true := by
 decide +kernel
def cuts72724 : List PrefixCut := [⟨8,21104668,21104681⟩,
⟨64,169957976,169958079⟩]
theorem checked72724 : checkPrefixCuts (2^48) 9536012289 10 Manual.Count131072.C072724.packed 64 cuts72724 = true := by
 decide +kernel
def pointBounds72724 : List (Nat × Nat × Nat) := [(9536028672,116281608077436,116281997859463)]
theorem point_links_checked72724 : (cuts72724.take 1).map (fun c => (9536012289-1+2*2^10*c.k,116281586972768+c.lower,116281976754782+c.upper)) = pointBounds72724 := by
 decide +kernel
def cuts72725 : List PrefixCut := [⟨64,171106781,171106883⟩]
theorem checked72725 : checkPrefixCuts (2^48) 9536143361 10 Manual.Count131072.C072725.packed 64 cuts72725 = true := by
 decide +kernel
def cuts72726 : List PrefixCut := [⟨26,68418436,68418478⟩,
⟨64,169569585,169569684⟩]
theorem checked72726 : checkPrefixCuts (2^48) 9536274433 10 Manual.Count131072.C072726.packed 64 cuts72726 = true := by
 decide +kernel
def pointBounds72726 : List (Nat × Nat × Nat) := [(9536327680,116281996455961,116282386238222)]
theorem point_links_checked72726 : (cuts72726.take 1).map (fun c => (9536274433-1+2*2^10*c.k,116281928037525+c.lower,116282317819744+c.upper)) = pointBounds72726 := by
 decide +kernel
def cuts72727 : List PrefixCut := [⟨64,170009997,170010089⟩]
theorem checked72727 : checkPrefixCuts (2^48) 9536405505 10 Manual.Count131072.C072727.packed 64 cuts72727 = true := by
 decide +kernel
def cuts72728 : List PrefixCut := [⟨44,115640876,115640943⟩,
⟨64,168266260,168266362⟩]
theorem checked72728 : checkPrefixCuts (2^48) 9536536577 10 Manual.Count131072.C072728.packed 64 cuts72728 = true := by
 decide +kernel
def pointBounds72728 : List (Nat × Nat × Nat) := [(9536626688,116282383257983,116282773040460)]
theorem point_links_checked72728 : (cuts72728.take 1).map (fun c => (9536536577-1+2*2^10*c.k,116282267617107+c.lower,116282657399517+c.upper)) = pointBounds72728 := by
 decide +kernel
def cuts72729 : List PrefixCut := [⟨64,168500069,168500168⟩]
theorem checked72729 : checkPrefixCuts (2^48) 9536667649 10 Manual.Count131072.C072729.packed 64 cuts72729 = true := by
 decide +kernel
def cuts72730 : List PrefixCut := [⟨62,162270240,162270336⟩,
⟨64,167346684,167346783⟩]
theorem checked72730 : checkPrefixCuts (2^48) 9536798721 10 Manual.Count131072.C072730.packed 64 cuts72730 = true := by
 decide +kernel
def pointBounds72730 : List (Nat × Nat × Nat) := [(9536925696,116282766653676,116283156436383)]
theorem point_links_checked72730 : (cuts72730.take 1).map (fun c => (9536798721-1+2*2^10*c.k,116282604383436+c.lower,116282994166047+c.upper)) = pointBounds72730 := by
 decide +kernel
def cuts72731 : List PrefixCut := [⟨64,170089193,170089295⟩]
theorem checked72731 : checkPrefixCuts (2^48) 9536929793 10 Manual.Count131072.C072731.packed 64 cuts72731 = true := by
 decide +kernel
def cuts72732 : List PrefixCut := [⟨64,165482727,165482824⟩]
theorem checked72732 : checkPrefixCuts (2^48) 9537060865 10 Manual.Count131072.C072732.packed 64 cuts72732 = true := by
 decide +kernel
def cuts72733 : List PrefixCut := [⟨16,41525274,41525296⟩,
⟨64,168608854,168608946⟩]
theorem checked72733 : checkPrefixCuts (2^48) 9537191937 10 Manual.Count131072.C072733.packed 64 cuts72733 = true := by
 decide +kernel
def pointBounds72733 : List (Nat × Nat × Nat) := [(9537224704,116283148827314,116283538610245)]
theorem point_links_checked72733 : (cuts72733.take 1).map (fun c => (9537191937-1+2*2^10*c.k,116283107302040+c.lower,116283497084949+c.upper)) = pointBounds72733 := by
 decide +kernel
def cuts72734 : List PrefixCut := [⟨64,169285339,169285437⟩]
theorem checked72734 : checkPrefixCuts (2^48) 9537323009 10 Manual.Count131072.C072734.packed 64 cuts72734 = true := by
 decide +kernel
def cuts72735 : List PrefixCut := [⟨34,88980108,88980162⟩,
⟨64,166479332,166479435⟩]
theorem checked72735 : checkPrefixCuts (2^48) 9537454081 10 Manual.Count131072.C072735.packed 64 cuts72735 = true := by
 decide +kernel
def pointBounds72735 : List (Nat × Nat × Nat) := [(9537523712,116283534176341,116283923959494)]
theorem point_links_checked72735 : (cuts72735.take 1).map (fun c => (9537454081-1+2*2^10*c.k,116283445196233+c.lower,116283834979332+c.upper)) = pointBounds72735 := by
 decide +kernel
def cuts72736 : List PrefixCut := [⟨64,168749459,168749565⟩]
theorem checked72736 : checkPrefixCuts (2^48) 9537585153 10 Manual.Count131072.C072736.packed 64 cuts72736 = true := by
 decide +kernel
def cuts72737 : List PrefixCut := [⟨52,139058684,139058775⟩,
⟨64,170399794,170399904⟩]
theorem checked72737 : checkPrefixCuts (2^48) 9537716225 10 Manual.Count131072.C072737.packed 64 cuts72737 = true := by
 decide +kernel
def pointBounds72737 : List (Nat × Nat × Nat) := [(9537822720,116283919483708,116284309267107)]
theorem point_links_checked72737 : (cuts72737.take 1).map (fun c => (9537716225-1+2*2^10*c.k,116283780425024+c.lower,116284170208332+c.upper)) = pointBounds72737 := by
 decide +kernel
def cuts72738 : List PrefixCut := [⟨64,167062681,167062784⟩]
theorem checked72738 : checkPrefixCuts (2^48) 9537847297 10 Manual.Count131072.C072738.packed 64 cuts72738 = true := by
 decide +kernel
def cuts72739 : List PrefixCut := [⟨64,169214666,169214767⟩]
theorem checked72739 : checkPrefixCuts (2^48) 9537978369 10 Manual.Count131072.C072739.packed 64 cuts72739 = true := by
 decide +kernel
def cuts72740 : List PrefixCut := [⟨6,15758626,15758635⟩,
⟨64,167500749,167500854⟩]
theorem checked72740 : checkPrefixCuts (2^48) 9538109441 10 Manual.Count131072.C072740.packed 64 cuts72740 = true := by
 decide +kernel
def pointBounds72740 : List (Nat × Nat × Nat) := [(9538121728,116284302860791,116284692644422)]
theorem point_links_checked72740 : (cuts72740.take 1).map (fun c => (9538109441-1+2*2^10*c.k,116284287102165+c.lower,116284676885787+c.upper)) = pointBounds72740 := by
 decide +kernel
def cuts72741 : List PrefixCut := [⟨64,167409916,167410018⟩]
theorem checked72741 : checkPrefixCuts (2^48) 9538240513 10 Manual.Count131072.C072741.packed 64 cuts72741 = true := by
 decide +kernel
def cuts72742 : List PrefixCut := [⟨24,62678532,62678568⟩,
⟨64,167466641,167466737⟩]
theorem checked72742 : checkPrefixCuts (2^48) 9538371585 10 Manual.Count131072.C072742.packed 64 cuts72742 = true := by
 decide +kernel
def pointBounds72742 : List (Nat × Nat × Nat) := [(9538420736,116284684691362,116285074475227)]
theorem point_links_checked72742 : (cuts72742.take 1).map (fun c => (9538371585-1+2*2^10*c.k,116284622012830+c.lower,116285011796659+c.upper)) = pointBounds72742 := by
 decide +kernel
def cuts72743 : List PrefixCut := [⟨64,167316783,167316880⟩]
theorem checked72743 : checkPrefixCuts (2^48) 9538502657 10 Manual.Count131072.C072743.packed 64 cuts72743 = true := by
 decide +kernel
def cuts72744 : List PrefixCut := [⟨42,111454737,111454795⟩,
⟨64,169055516,169055608⟩]
theorem checked72744 : checkPrefixCuts (2^48) 9538633729 10 Manual.Count131072.C072744.packed 64 cuts72744 = true := by
 decide +kernel
def pointBounds72744 : List (Nat × Nat × Nat) := [(9538719744,116285068250991,116285458035071)]
theorem point_links_checked72744 : (cuts72744.take 1).map (fun c => (9538633729-1+2*2^10*c.k,116284956796254+c.lower,116285346580276+c.upper)) = pointBounds72744 := by
 decide +kernel
def cuts72745 : List PrefixCut := [⟨64,169289250,169289352⟩]
theorem checked72745 : checkPrefixCuts (2^48) 9538764801 10 Manual.Count131072.C072745.packed 64 cuts72745 = true := by
 decide +kernel
def cuts72746 : List PrefixCut := [⟨60,158723153,158723251⟩,
⟨64,169375443,169375547⟩]
theorem checked72746 : checkPrefixCuts (2^48) 9538895873 10 Manual.Count131072.C072746.packed 64 cuts72746 = true := by
 decide +kernel
def pointBounds72746 : List (Nat × Nat × Nat) := [(9539018752,116285453864173,116285843648487)]
theorem point_links_checked72746 : (cuts72746.take 1).map (fun c => (9538895873-1+2*2^10*c.k,116285295141020+c.lower,116285684925236+c.upper)) = pointBounds72746 := by
 decide +kernel
def cuts72747 : List PrefixCut := [⟨64,169815728,169815832⟩]
theorem checked72747 : checkPrefixCuts (2^48) 9539026945 10 Manual.Count131072.C072747.packed 64 cuts72747 = true := by
 decide +kernel
def cuts72748 : List PrefixCut := [⟨64,169636351,169636451⟩]
theorem checked72748 : checkPrefixCuts (2^48) 9539158017 10 Manual.Count131072.C072748.packed 64 cuts72748 = true := by
 decide +kernel
def cuts72749 : List PrefixCut := [⟨14,37798288,37798310⟩,
⟨64,166004706,166004807⟩]
theorem checked72749 : checkPrefixCuts (2^48) 9539289089 10 Manual.Count131072.C072749.packed 64 cuts72749 = true := by
 decide +kernel
def pointBounds72749 : List (Nat × Nat × Nat) := [(9539317760,116285841766830,116286231551376)]
theorem point_links_checked72749 : (cuts72749.take 1).map (fun c => (9539289089-1+2*2^10*c.k,116285803968542+c.lower,116286193753066+c.upper)) = pointBounds72749 := by
 decide +kernel
def cuts72750 : List PrefixCut := [⟨64,170015284,170015385⟩]
theorem checked72750 : checkPrefixCuts (2^48) 9539420161 10 Manual.Count131072.C072750.packed 64 cuts72750 = true := by
 decide +kernel
def cuts72751 : List PrefixCut := [⟨32,82970848,82970899⟩,
⟨64,167091852,167091957⟩]
theorem checked72751 : checkPrefixCuts (2^48) 9539551233 10 Manual.Count131072.C072751.packed 64 cuts72751 = true := by
 decide +kernel
def pointBounds72751 : List (Nat × Nat × Nat) := [(9539616768,116286222959380,116286612744157)]
theorem point_links_checked72751 : (cuts72751.take 1).map (fun c => (9539551233-1+2*2^10*c.k,116286139988532+c.lower,116286529773258+c.upper)) = pointBounds72751 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000085
