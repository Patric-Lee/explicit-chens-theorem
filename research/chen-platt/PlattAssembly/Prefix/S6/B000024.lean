import PlattAssemblyKernel
import PlattCertificates.Count131072.C050768
import PlattCertificates.Count131072.C050769
import PlattCertificates.Count131072.C050770
import PlattCertificates.Count131072.C050771
import PlattCertificates.Count131072.C050772
import PlattCertificates.Count131072.C050773
import PlattCertificates.Count131072.C050774
import PlattCertificates.Count131072.C050775
import PlattCertificates.Count131072.C050776
import PlattCertificates.Count131072.C050777
import PlattCertificates.Count131072.C050778
import PlattCertificates.Count131072.C050779
import PlattCertificates.Count131072.C050780
import PlattCertificates.Count131072.C050781
import PlattCertificates.Count131072.C050782
import PlattCertificates.Count131072.C050783
import PlattCertificates.Count131072.C050784
import PlattCertificates.Count131072.C050785
import PlattCertificates.Count131072.C050786
import PlattCertificates.Count131072.C050787
import PlattCertificates.Count131072.C050788
import PlattCertificates.Count131072.C050789
import PlattCertificates.Count131072.C050790
import PlattCertificates.Count131072.C050791
import PlattCertificates.Count131072.C050792
import PlattCertificates.Count131072.C050793
import PlattCertificates.Count131072.C050794
import PlattCertificates.Count131072.C050795
import PlattCertificates.Count131072.C050796
import PlattCertificates.Count131072.C050797
import PlattCertificates.Count131072.C050798
import PlattCertificates.Count131072.C050799
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50768 : List PrefixCut := [⟨32,123653622,123653695⟩,
⟨64,247179205,247179349⟩]
theorem checked50768 : checkPrefixCuts (2^48) 6658195457 10 Manual.Count131072.C050768.packed 64 cuts50768 = true := by
 decide +kernel
def pointBounds50768 : List (Nat × Nat × Nat) := [(6658260992,111846651925450,111847039155508)]
theorem point_links_checked50768 : (cuts50768.take 1).map (fun c => (6658195457-1+2*2^10*c.k,111846528271828+c.lower,111846915501813+c.upper)) = pointBounds50768 := by
 decide +kernel
def cuts50769 : List PrefixCut := [⟨64,243961537,243961670⟩]
theorem checked50769 : checkPrefixCuts (2^48) 6658326529 10 Manual.Count131072.C050769.packed 64 cuts50769 = true := by
 decide +kernel
def cuts50770 : List PrefixCut := [⟨6,22616188,22616201⟩,
⟨64,245182669,245182805⟩]
theorem checked50770 : checkPrefixCuts (2^48) 6658457601 10 Manual.Count131072.C050770.packed 64 cuts50770 = true := by
 decide +kernel
def pointBounds50770 : List (Nat × Nat × Nat) := [(6658469888,111847042028758,111847429259033)]
theorem point_links_checked50770 : (cuts50770.take 1).map (fun c => (6658457601-1+2*2^10*c.k,111847019412570+c.lower,111847406642832+c.upper)) = pointBounds50770 := by
 decide +kernel
def cuts50771 : List PrefixCut := [⟨44,168623698,168623791⟩,
⟨64,245093299,245093435⟩]
theorem checked50771 : checkPrefixCuts (2^48) 6658588673 10 Manual.Count131072.C050771.packed 64 cuts50771 = true := by
 decide +kernel
def pointBounds50771 : List (Nat × Nat × Nat) := [(6658678784,111847433218937,111847820449428)]
theorem point_links_checked50771 : (cuts50771.take 1).map (fun c => (6658588673-1+2*2^10*c.k,111847264595239+c.lower,111847651825637+c.upper)) = pointBounds50771 := by
 decide +kernel
def cuts50772 : List PrefixCut := [⟨64,244496650,244496791⟩]
theorem checked50772 : checkPrefixCuts (2^48) 6658719745 10 Manual.Count131072.C050772.packed 64 cuts50772 = true := by
 decide +kernel
def cuts50773 : List PrefixCut := [⟨18,69197092,69197134⟩,
⟨64,245844504,245844644⟩]
theorem checked50773 : checkPrefixCuts (2^48) 6658850817 10 Manual.Count131072.C050773.packed 64 cuts50773 = true := by
 decide +kernel
def pointBounds50773 : List (Nat × Nat × Nat) := [(6658887680,111847823382280,111848210612997)]
theorem point_links_checked50773 : (cuts50773.take 1).map (fun c => (6658850817-1+2*2^10*c.k,111847754185188+c.lower,111848141415863+c.upper)) = pointBounds50773 := by
 decide +kernel
def cuts50774 : List PrefixCut := [⟨56,209699471,209699591⟩,
⟨64,240598242,240598379⟩]
theorem checked50774 : checkPrefixCuts (2^48) 6658981889 10 Manual.Count131072.C050774.packed 64 cuts50774 = true := by
 decide +kernel
def pointBounds50774 : List (Nat × Nat × Nat) := [(6659096576,111848209729163,111848596960098)]
theorem point_links_checked50774 : (cuts50774.take 1).map (fun c => (6658981889-1+2*2^10*c.k,111848000029692+c.lower,111848387260507+c.upper)) = pointBounds50774 := by
 decide +kernel
def cuts50775 : List PrefixCut := [⟨64,245116262,245116401⟩]
theorem checked50775 : checkPrefixCuts (2^48) 6659112961 10 Manual.Count131072.C050775.packed 64 cuts50775 = true := by
 decide +kernel
def cuts50776 : List PrefixCut := [⟨30,114335221,114335285⟩,
⟨64,243547533,243547673⟩]
theorem checked50776 : checkPrefixCuts (2^48) 6659244033 10 Manual.Count131072.C050776.packed 64 cuts50776 = true := by
 decide +kernel
def pointBounds50776 : List (Nat × Nat × Nat) := [(6659305472,111848600079417,111848987310572)]
theorem point_links_checked50776 : (cuts50776.take 1).map (fun c => (6659244033-1+2*2^10*c.k,111848485744196+c.lower,111848872975287+c.upper)) = pointBounds50776 := by
 decide +kernel
def cuts50777 : List PrefixCut := [⟨64,241852049,241852184⟩]
theorem checked50777 : checkPrefixCuts (2^48) 6659375105 10 Manual.Count131072.C050777.packed 64 cuts50777 = true := by
 decide +kernel
def cuts50778 : List PrefixCut := [⟨4,14539712,14539721⟩,
⟨64,241635971,241636113⟩]
theorem checked50778 : checkPrefixCuts (2^48) 6659506177 10 Manual.Count131072.C050778.packed 64 cuts50778 = true := by
 decide +kernel
def pointBounds50778 : List (Nat × Nat × Nat) := [(6659514368,111848985683490,111849372914865)]
theorem point_links_checked50778 : (cuts50778.take 1).map (fun c => (6659506177-1+2*2^10*c.k,111848971143778+c.lower,111849358375144+c.upper)) = pointBounds50778 := by
 decide +kernel
def cuts50779 : List PrefixCut := [⟨42,161750170,161750262⟩,
⟨64,243955815,243955953⟩]
theorem checked50779 : checkPrefixCuts (2^48) 6659637249 10 Manual.Count131072.C050779.packed 64 cuts50779 = true := by
 decide +kernel
def pointBounds50779 : List (Nat × Nat × Nat) := [(6659723264,111849374529919,111849761761519)]
theorem point_links_checked50779 : (cuts50779.take 1).map (fun c => (6659637249-1+2*2^10*c.k,111849212779749+c.lower,111849600011257+c.upper)) = pointBounds50779 := by
 decide +kernel
def cuts50780 : List PrefixCut := [⟨64,246909503,246909646⟩]
theorem checked50780 : checkPrefixCuts (2^48) 6659768321 10 Manual.Count131072.C050780.packed 64 cuts50780 = true := by
 decide +kernel
def cuts50781 : List PrefixCut := [⟨16,62254917,62254952⟩,
⟨64,246693347,246693485⟩]
theorem checked50781 : checkPrefixCuts (2^48) 6659899393 10 Manual.Count131072.C050781.packed 64 cuts50781 = true := by
 decide +kernel
def pointBounds50781 : List (Nat × Nat × Nat) := [(6659932160,111849765899984,111850153131808)]
theorem point_links_checked50781 : (cuts50781.take 1).map (fun c => (6659899393-1+2*2^10*c.k,111849703645067+c.lower,111850090876856+c.upper)) = pointBounds50781 := by
 decide +kernel
def cuts50782 : List PrefixCut := [⟨54,207003959,207004074⟩,
⟨64,245674181,245674317⟩]
theorem checked50782 : checkPrefixCuts (2^48) 6660030465 10 Manual.Count131072.C050782.packed 64 cuts50782 = true := by
 decide +kernel
def pointBounds50782 : List (Nat × Nat × Nat) := [(6660141056,111850157342373,111850544574415)]
theorem point_links_checked50782 : (cuts50782.take 1).map (fun c => (6660030465-1+2*2^10*c.k,111849950338414+c.lower,111850337570341+c.upper)) = pointBounds50782 := by
 decide +kernel
def cuts50783 : List PrefixCut := [⟨64,243260405,243260540⟩]
theorem checked50783 : checkPrefixCuts (2^48) 6660161537 10 Manual.Count131072.C050783.packed 64 cuts50783 = true := by
 decide +kernel
def cuts50784 : List PrefixCut := [⟨28,104512595,104512655⟩,
⟨64,240593155,240593296⟩]
theorem checked50784 : checkPrefixCuts (2^48) 6660292609 10 Manual.Count131072.C050784.packed 64 cuts50784 = true := by
 decide +kernel
def pointBounds50784 : List (Nat × Nat × Nat) := [(6660349952,111850543785595,111850931017853)]
theorem point_links_checked50784 : (cuts50784.take 1).map (fun c => (6660292609-1+2*2^10*c.k,111850439273000+c.lower,111850826505198+c.upper)) = pointBounds50784 := by
 decide +kernel
def cuts50785 : List PrefixCut := [⟨64,245532902,245533036⟩]
theorem checked50785 : checkPrefixCuts (2^48) 6660423681 10 Manual.Count131072.C050785.packed 64 cuts50785 = true := by
 decide +kernel
def cuts50786 : List PrefixCut := [⟨2,8874593,8874597⟩,
⟨64,248232682,248232822⟩]
theorem checked50786 : checkPrefixCuts (2^48) 6660554753 10 Manual.Count131072.C050786.packed 64 cuts50786 = true := by
 decide +kernel
def pointBounds50786 : List (Nat × Nat × Nat) := [(6660558848,111850934273650,111851321506127)]
theorem point_links_checked50786 : (cuts50786.take 1).map (fun c => (6660554753-1+2*2^10*c.k,111850925399057+c.lower,111851312631530+c.upper)) = pointBounds50786 := by
 decide +kernel
def cuts50787 : List PrefixCut := [⟨40,151329075,151329164⟩,
⟨64,241424135,241424276⟩]
theorem checked50787 : checkPrefixCuts (2^48) 6660685825 10 Manual.Count131072.C050787.packed 64 cuts50787 = true := by
 decide +kernel
def pointBounds50787 : List (Nat × Nat × Nat) := [(6660767744,111851324960814,111851712193516)]
theorem point_links_checked50787 : (cuts50787.take 1).map (fun c => (6660685825-1+2*2^10*c.k,111851173631739+c.lower,111851560864352+c.upper)) = pointBounds50787 := by
 decide +kernel
def cuts50788 : List PrefixCut := [⟨64,239771301,239771436⟩]
theorem checked50788 : checkPrefixCuts (2^48) 6660816897 10 Manual.Count131072.C050788.packed 64 cuts50788 = true := by
 decide +kernel
def cuts50789 : List PrefixCut := [⟨14,54300748,54300778⟩,
⟨64,243062659,243062800⟩]
theorem checked50789 : checkPrefixCuts (2^48) 6660947969 10 Manual.Count131072.C050789.packed 64 cuts50789 = true := by
 decide +kernel
def pointBounds50789 : List (Nat × Nat × Nat) := [(6660976640,111851709127923,111852096360842)]
theorem point_links_checked50789 : (cuts50789.take 1).map (fun c => (6660947969-1+2*2^10*c.k,111851654827175+c.lower,111852042060064+c.upper)) = pointBounds50789 := by
 decide +kernel
def cuts50790 : List PrefixCut := [⟨52,197125689,197125803⟩,
⟨64,241325359,241325497⟩]
theorem checked50790 : checkPrefixCuts (2^48) 6661079041 10 Manual.Count131072.C050790.packed 64 cuts50790 = true := by
 decide +kernel
def pointBounds50790 : List (Nat × Nat × Nat) := [(6661185536,111852095015523,111852482248667)]
theorem point_links_checked50790 : (cuts50790.take 1).map (fun c => (6661079041-1+2*2^10*c.k,111851897889834+c.lower,111852285122864+c.upper)) = pointBounds50790 := by
 decide +kernel
def cuts50791 : List PrefixCut := [⟨64,244489775,244489909⟩]
theorem checked50791 : checkPrefixCuts (2^48) 6661210113 10 Manual.Count131072.C050791.packed 64 cuts50791 = true := by
 decide +kernel
def cuts50792 : List PrefixCut := [⟨26,99129808,99129863⟩,
⟨64,243344107,243344244⟩]
theorem checked50792 : checkPrefixCuts (2^48) 6661341185 10 Manual.Count131072.C050792.packed 64 cuts50792 = true := by
 decide +kernel
def pointBounds50792 : List (Nat × Nat × Nat) := [(6661394432,111852482834776,111852870068133)]
theorem point_links_checked50792 : (cuts50792.take 1).map (fun c => (6661341185-1+2*2^10*c.k,111852383704968+c.lower,111852770938270+c.upper)) = pointBounds50792 := by
 decide +kernel
def cuts50793 : List PrefixCut := [⟨64,246128041,246128183⟩]
theorem checked50793 : checkPrefixCuts (2^48) 6661472257 10 Manual.Count131072.C050793.packed 64 cuts50793 = true := by
 decide +kernel
def pointBounds50793 : List (Nat × Nat × Nat) := [(6661603328,111852873177116,111853260410697)]
theorem point_links_checked50793 : (cuts50793.take 1).map (fun c => (6661472257-1+2*2^10*c.k,111852627049075+c.lower,111853014282514+c.upper)) = pointBounds50793 := by
 decide +kernel
def cuts50794 : List PrefixCut := [⟨64,247095012,247095148⟩]
theorem checked50794 : checkPrefixCuts (2^48) 6661603329 10 Manual.Count131072.C050794.packed 64 cuts50794 = true := by
 decide +kernel
def cuts50795 : List PrefixCut := [⟨38,144037912,144037996⟩,
⟨64,242695934,242696074⟩]
theorem checked50795 : checkPrefixCuts (2^48) 6661734401 10 Manual.Count131072.C050795.packed 64 cuts50795 = true := by
 decide +kernel
def pointBounds50795 : List (Nat × Nat × Nat) := [(6661812224,111853264310040,111853651543841)]
theorem point_links_checked50795 : (cuts50795.take 1).map (fun c => (6661734401-1+2*2^10*c.k,111853120272128+c.lower,111853507505845+c.upper)) = pointBounds50795 := by
 decide +kernel
def cuts50796 : List PrefixCut := [⟨64,242522155,242522292⟩]
theorem checked50796 : checkPrefixCuts (2^48) 6661865473 10 Manual.Count131072.C050796.packed 64 cuts50796 = true := by
 decide +kernel
def cuts50797 : List PrefixCut := [⟨12,46433580,46433605⟩,
⟨64,244967909,244968050⟩]
theorem checked50797 : checkPrefixCuts (2^48) 6661996545 10 Manual.Count131072.C050797.packed 64 cuts50797 = true := by
 decide +kernel
def pointBounds50797 : List (Nat × Nat × Nat) := [(6662021120,111853651923797,111854039157816)]
theorem point_links_checked50797 : (cuts50797.take 1).map (fun c => (6661996545-1+2*2^10*c.k,111853605490217+c.lower,111853992724211+c.upper)) = pointBounds50797 := by
 decide +kernel
def cuts50798 : List PrefixCut := [⟨50,189701045,189701161⟩,
⟨64,243906846,243906992⟩]
theorem checked50798 : checkPrefixCuts (2^48) 6662127617 10 Manual.Count131072.C050798.packed 64 cuts50798 = true := by
 decide +kernel
def pointBounds50798 : List (Nat × Nat × Nat) := [(6662230016,111854040159171,111854427393422)]
theorem point_links_checked50798 : (cuts50798.take 1).map (fun c => (6662127617-1+2*2^10*c.k,111853850458126+c.lower,111854237692261+c.upper)) = pointBounds50798 := by
 decide +kernel
def cuts50799 : List PrefixCut := [⟨64,242507839,242507984⟩]
theorem checked50799 : checkPrefixCuts (2^48) 6662258689 10 Manual.Count131072.C050799.packed 64 cuts50799 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000024
