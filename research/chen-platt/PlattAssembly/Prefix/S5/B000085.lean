import PlattAssemblyKernel
import PlattCertificates.Count131072.C042720
import PlattCertificates.Count131072.C042721
import PlattCertificates.Count131072.C042722
import PlattCertificates.Count131072.C042723
import PlattCertificates.Count131072.C042724
import PlattCertificates.Count131072.C042725
import PlattCertificates.Count131072.C042726
import PlattCertificates.Count131072.C042727
import PlattCertificates.Count131072.C042728
import PlattCertificates.Count131072.C042729
import PlattCertificates.Count131072.C042730
import PlattCertificates.Count131072.C042731
import PlattCertificates.Count131072.C042732
import PlattCertificates.Count131072.C042733
import PlattCertificates.Count131072.C042734
import PlattCertificates.Count131072.C042735
import PlattCertificates.Count131072.C042736
import PlattCertificates.Count131072.C042737
import PlattCertificates.Count131072.C042738
import PlattCertificates.Count131072.C042739
import PlattCertificates.Count131072.C042740
import PlattCertificates.Count131072.C042741
import PlattCertificates.Count131072.C042742
import PlattCertificates.Count131072.C042743
import PlattCertificates.Count131072.C042744
import PlattCertificates.Count131072.C042745
import PlattCertificates.Count131072.C042746
import PlattCertificates.Count131072.C042747
import PlattCertificates.Count131072.C042748
import PlattCertificates.Count131072.C042749
import PlattCertificates.Count131072.C042750
import PlattCertificates.Count131072.C042751
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000085
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42720 : List PrefixCut := [⟨58,270856283,270856442⟩,
⟨64,298835730,298835905⟩]
theorem checked42720 : checkPrefixCuts (2^48) 5603328001 10 Manual.Count131072.C042720.packed 64 cuts42720 = true := by
 decide +kernel
def pointBounds42720 : List (Nat × Nat × Nat) := [(5603446784,109692051546984,109692437538833)]
theorem point_links_checked42720 : (cuts42720.take 1).map (fun c => (5603328001-1+2*2^10*c.k,109691780690701+c.lower,109692166682391+c.upper)) = pointBounds42720 := by
 decide +kernel
def cuts42721 : List PrefixCut := [⟨64,289184228,289184393⟩]
theorem checked42721 : checkPrefixCuts (2^48) 5603459073 10 Manual.Count131072.C042721.packed 64 cuts42721 = true := by
 decide +kernel
def cuts42722 : List PrefixCut := [⟨16,71880596,71880640⟩,
⟨64,294853500,294853679⟩]
theorem checked42722 : checkPrefixCuts (2^48) 5603590145 10 Manual.Count131072.C042722.packed 64 cuts42722 = true := by
 decide +kernel
def pointBounds42722 : List (Nat × Nat × Nat) := [(5603622912,109692440591255,109692826583329)]
theorem point_links_checked42722 : (cuts42722.take 1).map (fun c => (5603590145-1+2*2^10*c.k,109692368710659+c.lower,109692754702689+c.upper)) = pointBounds42722 := by
 decide +kernel
def cuts42723 : List PrefixCut := [⟨38,175803774,175803874⟩,
⟨64,296805575,296805745⟩]
theorem checked42723 : checkPrefixCuts (2^48) 5603721217 10 Manual.Count131072.C042723.packed 64 cuts42723 = true := by
 decide +kernel
def pointBounds42723 : List (Nat × Nat × Nat) := [(5603799040,109692839367933,109693225360242)]
theorem point_links_checked42723 : (cuts42723.take 1).map (fun c => (5603721217-1+2*2^10*c.k,109692663564159+c.lower,109693049556368+c.upper)) = pointBounds42723 := by
 decide +kernel
def cuts42724 : List PrefixCut := [⟨60,276305700,276305859⟩,
⟨64,293433339,293433509⟩]
theorem checked42724 : checkPrefixCuts (2^48) 5603852289 10 Manual.Count131072.C042724.packed 64 cuts42724 = true := by
 decide +kernel
def pointBounds42724 : List (Nat × Nat × Nat) := [(5603975168,109693236675434,109693622667972)]
theorem point_links_checked42724 : (cuts42724.take 1).map (fun c => (5603852289-1+2*2^10*c.k,109692960369734+c.lower,109693346362113+c.upper)) = pointBounds42724 := by
 decide +kernel
def cuts42725 : List PrefixCut := [⟨64,290714211,290714382⟩]
theorem checked42725 : checkPrefixCuts (2^48) 5603983361 10 Manual.Count131072.C042725.packed 64 cuts42725 = true := by
 decide +kernel
def cuts42726 : List PrefixCut := [⟨18,82672504,82672552⟩,
⟨64,295026828,295027003⟩]
theorem checked42726 : checkPrefixCuts (2^48) 5604114433 10 Manual.Count131072.C042726.packed 64 cuts42726 = true := by
 decide +kernel
def pointBounds42726 : List (Nat × Nat × Nat) := [(5604151296,109693627189788,109694013182556)]
theorem point_links_checked42726 : (cuts42726.take 1).map (fun c => (5604114433-1+2*2^10*c.k,109693544517284+c.lower,109693930510004+c.upper)) = pointBounds42726 := by
 decide +kernel
def cuts42727 : List PrefixCut := [⟨40,180307488,180307590⟩,
⟨64,289344533,289344700⟩]
theorem checked42727 : checkPrefixCuts (2^48) 5604245505 10 Manual.Count131072.C042727.packed 64 cuts42727 = true := by
 decide +kernel
def pointBounds42727 : List (Nat × Nat × Nat) := [(5604327424,109694019851600,109694405844597)]
theorem point_links_checked42727 : (cuts42727.take 1).map (fun c => (5604245505-1+2*2^10*c.k,109693839544112+c.lower,109694225537007+c.upper)) = pointBounds42727 := by
 decide +kernel
def cuts42728 : List PrefixCut := [⟨62,286424933,286425099⟩,
⟨64,294611276,294611447⟩]
theorem checked42728 : checkPrefixCuts (2^48) 5604376577 10 Manual.Count131072.C042728.packed 64 cuts42728 = true := by
 decide +kernel
def pointBounds42728 : List (Nat × Nat × Nat) := [(5604503552,109694415313578,109694801306806)]
theorem point_links_checked42728 : (cuts42728.take 1).map (fun c => (5604376577-1+2*2^10*c.k,109694128888645+c.lower,109694514881707+c.upper)) = pointBounds42728 := by
 decide +kernel
def cuts42729 : List PrefixCut := [⟨64,292695916,292696087⟩]
theorem checked42729 : checkPrefixCuts (2^48) 5604507649 10 Manual.Count131072.C042729.packed 64 cuts42729 = true := by
 decide +kernel
def cuts42730 : List PrefixCut := [⟨20,92357507,92357558⟩,
⟨64,297208971,297209137⟩]
theorem checked42730 : checkPrefixCuts (2^48) 5604638721 10 Manual.Count131072.C042730.packed 64 cuts42730 = true := by
 decide +kernel
def pointBounds42730 : List (Nat × Nat × Nat) := [(5604679680,109694808553344,109695194546799)]
theorem point_links_checked42730 : (cuts42730.take 1).map (fun c => (5604638721-1+2*2^10*c.k,109694716195837+c.lower,109695102189241+c.upper)) = pointBounds42730 := by
 decide +kernel
def cuts42731 : List PrefixCut := [⟨42,194753986,194754093⟩,
⟨64,297302465,297302633⟩]
theorem checked42731 : checkPrefixCuts (2^48) 5604769793 10 Manual.Count131072.C042731.packed 64 cuts42731 = true := by
 decide +kernel
def pointBounds42731 : List (Nat × Nat × Nat) := [(5604855808,109695208158794,109695594152471)]
theorem point_links_checked42731 : (cuts42731.take 1).map (fun c => (5604769793-1+2*2^10*c.k,109695013404808+c.lower,109695399398378+c.upper)) = pointBounds42731 := by
 decide +kernel
def cuts42732 : List PrefixCut := [⟨64,290817276,290817441⟩]
theorem checked42732 : checkPrefixCuts (2^48) 5604900865 10 Manual.Count131072.C042732.packed 64 cuts42732 = true := by
 decide +kernel
def pointBounds42732 : List (Nat × Nat × Nat) := [(5605031936,109695601524549,109695987518452)]
theorem point_links_checked42732 : (cuts42732.take 1).map (fun c => (5604900865-1+2*2^10*c.k,109695310707273+c.lower,109695696701011+c.upper)) = pointBounds42732 := by
 decide +kernel
def cuts42733 : List PrefixCut := [⟨64,290760240,290760414⟩]
theorem checked42733 : checkPrefixCuts (2^48) 5605031937 10 Manual.Count131072.C042733.packed 64 cuts42733 = true := by
 decide +kernel
def cuts42734 : List PrefixCut := [⟨22,99580057,99580116⟩,
⟨64,291556914,291557083⟩]
theorem checked42734 : checkPrefixCuts (2^48) 5605163009 10 Manual.Count131072.C042734.packed 64 cuts42734 = true := by
 decide +kernel
def pointBounds42734 : List (Nat × Nat × Nat) := [(5605208064,109695991864846,109696377858982)]
theorem point_links_checked42734 : (cuts42734.take 1).map (fun c => (5605163009-1+2*2^10*c.k,109695892284789+c.lower,109696278278866+c.upper)) = pointBounds42734 := by
 decide +kernel
def cuts42735 : List PrefixCut := [⟨44,204577952,204578068⟩,
⟨64,297776828,297776998⟩]
theorem checked42735 : checkPrefixCuts (2^48) 5605294081 10 Manual.Count131072.C042735.packed 64 cuts42735 = true := by
 decide +kernel
def pointBounds42735 : List (Nat × Nat × Nat) := [(5605384192,109696388419655,109696774414017)]
theorem point_links_checked42735 : (cuts42735.take 1).map (fun c => (5605294081-1+2*2^10*c.k,109696183841703+c.lower,109696569835949+c.upper)) = pointBounds42735 := by
 decide +kernel
def cuts42736 : List PrefixCut := [⟨64,293300761,293300934⟩]
theorem checked42736 : checkPrefixCuts (2^48) 5605425153 10 Manual.Count131072.C042736.packed 64 cuts42736 = true := by
 decide +kernel
def cuts42737 : List PrefixCut := [⟨2,8335447,8335451⟩,
⟨64,294850506,294850677⟩]
theorem checked42737 : checkPrefixCuts (2^48) 5605556225 10 Manual.Count131072.C042737.packed 64 cuts42737 = true := by
 decide +kernel
def pointBounds42737 : List (Nat × Nat × Nat) := [(5605560320,109696783254739,109697169249332)]
theorem point_links_checked42737 : (cuts42737.take 1).map (fun c => (5605556225-1+2*2^10*c.k,109696774919292+c.lower,109697160913881+c.upper)) = pointBounds42737 := by
 decide +kernel
def cuts42738 : List PrefixCut := [⟨24,111470992,111471056⟩,
⟨64,293086252,293086426⟩]
theorem checked42738 : checkPrefixCuts (2^48) 5605687297 10 Manual.Count131072.C042738.packed 64 cuts42738 = true := by
 decide +kernel
def pointBounds42738 : List (Nat × Nat × Nat) := [(5605736448,109697181240790,109697567235614)]
theorem point_links_checked42738 : (cuts42738.take 1).map (fun c => (5605687297-1+2*2^10*c.k,109697069769798+c.lower,109697455764558+c.upper)) = pointBounds42738 := by
 decide +kernel
def cuts42739 : List PrefixCut := [⟨46,207722013,207722139⟩,
⟨64,288409802,288409974⟩]
theorem checked42739 : checkPrefixCuts (2^48) 5605818369 10 Manual.Count131072.C042739.packed 64 cuts42739 = true := by
 decide +kernel
def pointBounds42739 : List (Nat × Nat × Nat) := [(5605912576,109697570578063,109697956573123)]
theorem point_links_checked42739 : (cuts42739.take 1).map (fun c => (5605818369-1+2*2^10*c.k,109697362856050+c.lower,109697748850984+c.upper)) = pointBounds42739 := by
 decide +kernel
def cuts42740 : List PrefixCut := [⟨64,293675073,293675241⟩]
theorem checked42740 : checkPrefixCuts (2^48) 5605949441 10 Manual.Count131072.C042740.packed 64 cuts42740 = true := by
 decide +kernel
def cuts42741 : List PrefixCut := [⟨4,18326219,18326230⟩,
⟨64,293517515,293517687⟩]
theorem checked42741 : checkPrefixCuts (2^48) 5606080513 10 Manual.Count131072.C042741.packed 64 cuts42741 = true := by
 decide +kernel
def pointBounds42741 : List (Nat × Nat × Nat) := [(5606088704,109697963267144,109698349262429)]
theorem point_links_checked42741 : (cuts42741.take 1).map (fun c => (5606080513-1+2*2^10*c.k,109697944940925+c.lower,109698330936199+c.upper)) = pointBounds42741 := by
 decide +kernel
def cuts42742 : List PrefixCut := [⟨26,115326503,115326569⟩,
⟨64,293410220,293410387⟩]
theorem checked42742 : checkPrefixCuts (2^48) 5606211585 10 Manual.Count131072.C042742.packed 64 cuts42742 = true := by
 decide +kernel
def pointBounds42742 : List (Nat × Nat × Nat) := [(5606264832,109698353784943,109698739780455)]
theorem point_links_checked42742 : (cuts42742.take 1).map (fun c => (5606211585-1+2*2^10*c.k,109698238458440+c.lower,109698624453886+c.upper)) = pointBounds42742 := by
 decide +kernel
def cuts42743 : List PrefixCut := [⟨48,225023601,225023735⟩,
⟨64,298926074,298926251⟩]
theorem checked42743 : checkPrefixCuts (2^48) 5606342657 10 Manual.Count131072.C042743.packed 64 cuts42743 = true := by
 decide +kernel
def pointBounds42743 : List (Nat × Nat × Nat) := [(5606440960,109698756892261,109699142888008)]
theorem point_links_checked42743 : (cuts42743.take 1).map (fun c => (5606342657-1+2*2^10*c.k,109698531868660+c.lower,109698917864273+c.upper)) = pointBounds42743 := by
 decide +kernel
def cuts42744 : List PrefixCut := [⟨64,288827943,288828113⟩]
theorem checked42744 : checkPrefixCuts (2^48) 5606473729 10 Manual.Count131072.C042744.packed 64 cuts42744 = true := by
 decide +kernel
def cuts42745 : List PrefixCut := [⟨6,28114299,28114315⟩,
⟨64,292636655,292636825⟩]
theorem checked42745 : checkPrefixCuts (2^48) 5606604801 10 Manual.Count131072.C042745.packed 64 cuts42745 = true := by
 decide +kernel
def pointBounds42745 : List (Nat × Nat × Nat) := [(5606617088,109699147736976,109699533732952)]
theorem point_links_checked42745 : (cuts42745.take 1).map (fun c => (5606604801-1+2*2^10*c.k,109699119622677+c.lower,109699505618637+c.upper)) = pointBounds42745 := by
 decide +kernel
def cuts42746 : List PrefixCut := [⟨28,130978933,130979010⟩,
⟨64,296495413,296495585⟩]
theorem checked42746 : checkPrefixCuts (2^48) 5606735873 10 Manual.Count131072.C042746.packed 64 cuts42746 = true := by
 decide +kernel
def pointBounds42746 : List (Nat × Nat × Nat) := [(5606793216,109699543238265,109699929234472)]
theorem point_links_checked42746 : (cuts42746.take 1).map (fun c => (5606735873-1+2*2^10*c.k,109699412259332+c.lower,109699798255462+c.upper)) = pointBounds42746 := by
 decide +kernel
def cuts42747 : List PrefixCut := [⟨50,228064755,228064888⟩,
⟨64,295183183,295183356⟩]
theorem checked42747 : checkPrefixCuts (2^48) 5606866945 10 Manual.Count131072.C042747.packed 64 cuts42747 = true := by
 decide +kernel
def pointBounds42747 : List (Nat × Nat × Nat) := [(5606969344,109699936819500,109700322815935)]
theorem point_links_checked42747 : (cuts42747.take 1).map (fun c => (5606866945-1+2*2^10*c.k,109699708754745+c.lower,109700094751047+c.upper)) = pointBounds42747 := by
 decide +kernel
def cuts42748 : List PrefixCut := [⟨64,288449522,288449684⟩]
theorem checked42748 : checkPrefixCuts (2^48) 5606998017 10 Manual.Count131072.C042748.packed 64 cuts42748 = true := by
 decide +kernel
def cuts42749 : List PrefixCut := [⟨8,35691768,35691791⟩,
⟨64,296775772,296775944⟩]
theorem checked42749 : checkPrefixCuts (2^48) 5607129089 10 Manual.Count131072.C042749.packed 64 cuts42749 = true := by
 decide +kernel
def pointBounds42749 : List (Nat × Nat × Nat) := [(5607145472,109700328079218,109700714075878)]
theorem point_links_checked42749 : (cuts42749.take 1).map (fun c => (5607129089-1+2*2^10*c.k,109700292387450+c.lower,109700678384087+c.upper)) = pointBounds42749 := by
 decide +kernel
def cuts42750 : List PrefixCut := [⟨30,139701085,139701173⟩,
⟨64,297270831,297271010⟩]
theorem checked42750 : checkPrefixCuts (2^48) 5607260161 10 Manual.Count131072.C042750.packed 64 cuts42750 = true := by
 decide +kernel
def pointBounds42750 : List (Nat × Nat × Nat) := [(5607321600,109700728864307,109701114861204)]
theorem point_links_checked42750 : (cuts42750.take 1).map (fun c => (5607260161-1+2*2^10*c.k,109700589163222+c.lower,109700975160031+c.upper)) = pointBounds42750 := by
 decide +kernel
def cuts42751 : List PrefixCut := [⟨52,238634839,238634983⟩,
⟨64,292194031,292194204⟩]
theorem checked42751 : checkPrefixCuts (2^48) 5607391233 10 Manual.Count131072.C042751.packed 64 cuts42751 = true := by
 decide +kernel
def pointBounds42751 : List (Nat × Nat × Nat) := [(5607497728,109701125068892,109701511066024)]
theorem point_links_checked42751 : (cuts42751.take 1).map (fun c => (5607391233-1+2*2^10*c.k,109700886434053+c.lower,109701272431041+c.upper)) = pointBounds42751 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000085
