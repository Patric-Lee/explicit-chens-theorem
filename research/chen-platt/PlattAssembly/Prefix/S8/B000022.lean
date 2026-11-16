import PlattAssemblyKernel
import PlattCertificates.Count131072.C070704
import PlattCertificates.Count131072.C070705
import PlattCertificates.Count131072.C070706
import PlattCertificates.Count131072.C070707
import PlattCertificates.Count131072.C070708
import PlattCertificates.Count131072.C070709
import PlattCertificates.Count131072.C070710
import PlattCertificates.Count131072.C070711
import PlattCertificates.Count131072.C070712
import PlattCertificates.Count131072.C070713
import PlattCertificates.Count131072.C070714
import PlattCertificates.Count131072.C070715
import PlattCertificates.Count131072.C070716
import PlattCertificates.Count131072.C070717
import PlattCertificates.Count131072.C070718
import PlattCertificates.Count131072.C070719
import PlattCertificates.Count131072.C070720
import PlattCertificates.Count131072.C070721
import PlattCertificates.Count131072.C070722
import PlattCertificates.Count131072.C070723
import PlattCertificates.Count131072.C070724
import PlattCertificates.Count131072.C070725
import PlattCertificates.Count131072.C070726
import PlattCertificates.Count131072.C070727
import PlattCertificates.Count131072.C070728
import PlattCertificates.Count131072.C070729
import PlattCertificates.Count131072.C070730
import PlattCertificates.Count131072.C070731
import PlattCertificates.Count131072.C070732
import PlattCertificates.Count131072.C070733
import PlattCertificates.Count131072.C070734
import PlattCertificates.Count131072.C070735
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70704 : List PrefixCut := [⟨64,174082904,174083010⟩]
theorem checked70704 : checkPrefixCuts (2^48) 9271246849 10 Manual.Count131072.C070704.packed 64 cuts70704 = true := by
 decide +kernel
def cuts70705 : List PrefixCut := [⟨64,172835711,172835815⟩]
theorem checked70705 : checkPrefixCuts (2^48) 9271377921 10 Manual.Count131072.C070705.packed 64 cuts70705 = true := by
 decide +kernel
def cuts70706 : List PrefixCut := [⟨13,36643412,36643433⟩,
⟨64,172529693,172529798⟩]
theorem checked70706 : checkPrefixCuts (2^48) 9271508993 10 Manual.Count131072.C070706.packed 64 cuts70706 = true := by
 decide +kernel
def pointBounds70706 : List (Nat × Nat × Nat) := [(9271535616,115936846997254,115937236574946)]
theorem point_links_checked70706 : (cuts70706.take 1).map (fun c => (9271508993-1+2*2^10*c.k,115936810353842+c.lower,115937199931513+c.upper)) = pointBounds70706 := by
 decide +kernel
def cuts70707 : List PrefixCut := [⟨64,173680871,173680978⟩]
theorem checked70707 : checkPrefixCuts (2^48) 9271640065 10 Manual.Count131072.C070707.packed 64 cuts70707 = true := by
 decide +kernel
def cuts70708 : List PrefixCut := [⟨27,72495324,72495366⟩,
⟨64,175044520,175044621⟩]
theorem checked70708 : checkPrefixCuts (2^48) 9271771137 10 Manual.Count131072.C070708.packed 64 cuts70708 = true := by
 decide +kernel
def pointBounds70708 : List (Nat × Nat × Nat) := [(9271826432,115937229059730,115937618637655)]
theorem point_links_checked70708 : (cuts70708.take 1).map (fun c => (9271771137-1+2*2^10*c.k,115937156564406+c.lower,115937546142289+c.upper)) = pointBounds70708 := by
 decide +kernel
def cuts70709 : List PrefixCut := [⟨64,174192039,174192135⟩]
theorem checked70709 : checkPrefixCuts (2^48) 9271902209 10 Manual.Count131072.C070709.packed 64 cuts70709 = true := by
 decide +kernel
def cuts70710 : List PrefixCut := [⟨41,110227245,110227309⟩,
⟨64,171032430,171032532⟩]
theorem checked70710 : checkPrefixCuts (2^48) 9272033281 10 Manual.Count131072.C070710.packed 64 cuts70710 = true := by
 decide +kernel
def pointBounds70710 : List (Nat × Nat × Nat) := [(9272117248,115937616028210,115938005606354)]
theorem point_links_checked70710 : (cuts70710.take 1).map (fun c => (9272033281-1+2*2^10*c.k,115937505800965+c.lower,115937895379045+c.upper)) = pointBounds70710 := by
 decide +kernel
def cuts70711 : List PrefixCut := [⟨64,175431747,175431846⟩]
theorem checked70711 : checkPrefixCuts (2^48) 9272164353 10 Manual.Count131072.C070711.packed 64 cuts70711 = true := by
 decide +kernel
def cuts70712 : List PrefixCut := [⟨55,150446158,150446245⟩,
⟨64,175064995,175065097⟩]
theorem checked70712 : checkPrefixCuts (2^48) 9272295425 10 Manual.Count131072.C070712.packed 64 cuts70712 = true := by
 decide +kernel
def pointBounds70712 : List (Nat × Nat × Nat) := [(9272408064,115938002711300,115938392289668)]
theorem point_links_checked70712 : (cuts70712.take 1).map (fun c => (9272295425-1+2*2^10*c.k,115937852265142+c.lower,115938241843423+c.upper)) = pointBounds70712 := by
 decide +kernel
def cuts70713 : List PrefixCut := [⟨64,173908985,173909085⟩]
theorem checked70713 : checkPrefixCuts (2^48) 9272426497 10 Manual.Count131072.C070713.packed 64 cuts70713 = true := by
 decide +kernel
def cuts70714 : List PrefixCut := [⟨64,171781652,171781756⟩]
theorem checked70714 : checkPrefixCuts (2^48) 9272557569 10 Manual.Count131072.C070714.packed 64 cuts70714 = true := by
 decide +kernel
def cuts70715 : List PrefixCut := [⟨5,14115190,14115196⟩,
⟨64,174177261,174177364⟩]
theorem checked70715 : checkPrefixCuts (2^48) 9272688641 10 Manual.Count131072.C070715.packed 64 cuts70715 = true := by
 decide +kernel
def pointBounds70715 : List (Nat × Nat × Nat) := [(9272698880,115938387135964,115938776714557)]
theorem point_links_checked70715 : (cuts70715.take 1).map (fun c => (9272688641-1+2*2^10*c.k,115938373020774+c.lower,115938762599361+c.upper)) = pointBounds70715 := by
 decide +kernel
def cuts70716 : List PrefixCut := [⟨64,173264175,173264269⟩]
theorem checked70716 : checkPrefixCuts (2^48) 9272819713 10 Manual.Count131072.C070716.packed 64 cuts70716 = true := by
 decide +kernel
def cuts70717 : List PrefixCut := [⟨19,52179108,52179140⟩,
⟨64,174020569,174020675⟩]
theorem checked70717 : checkPrefixCuts (2^48) 9272950785 10 Manual.Count131072.C070717.packed 64 cuts70717 = true := by
 decide +kernel
def pointBounds70717 : List (Nat × Nat × Nat) := [(9272989696,115938772641318,115939162220134)]
theorem point_links_checked70717 : (cuts70717.take 1).map (fun c => (9272950785-1+2*2^10*c.k,115938720462210+c.lower,115939110040994+c.upper)) = pointBounds70717 := by
 decide +kernel
def cuts70718 : List PrefixCut := [⟨64,175505438,175505546⟩]
theorem checked70718 : checkPrefixCuts (2^48) 9273081857 10 Manual.Count131072.C070718.packed 64 cuts70718 = true := by
 decide +kernel
def cuts70719 : List PrefixCut := [⟨33,89997936,89997988⟩,
⟨64,173590706,173590805⟩]
theorem checked70719 : checkPrefixCuts (2^48) 9273212929 10 Manual.Count131072.C070719.packed 64 cuts70719 = true := by
 decide +kernel
def pointBounds70719 : List (Nat × Nat × Nat) := [(9273280512,115939159986153,115939549565203)]
theorem point_links_checked70719 : (cuts70719.take 1).map (fun c => (9273212929-1+2*2^10*c.k,115939069988217+c.lower,115939459567215+c.upper)) = pointBounds70719 := by
 decide +kernel
def cuts70720 : List PrefixCut := [⟨64,175621891,175621991⟩]
theorem checked70720 : checkPrefixCuts (2^48) 9273344001 10 Manual.Count131072.C070720.packed 64 cuts70720 = true := by
 decide +kernel
def cuts70721 : List PrefixCut := [⟨47,126266528,126266599⟩,
⟨64,172644870,172644965⟩]
theorem checked70721 : checkPrefixCuts (2^48) 9273475073 10 Manual.Count131072.C070721.packed 64 cuts70721 = true := by
 decide +kernel
def pointBounds70721 : List (Nat × Nat × Nat) := [(9273571328,115939545467342,115939935046610)]
theorem point_links_checked70721 : (cuts70721.take 1).map (fun c => (9273475073-1+2*2^10*c.k,115939419200814+c.lower,115939808780011+c.upper)) = pointBounds70721 := by
 decide +kernel
def cuts70722 : List PrefixCut := [⟨64,171428349,171428445⟩]
theorem checked70722 : checkPrefixCuts (2^48) 9273606145 10 Manual.Count131072.C070722.packed 64 cuts70722 = true := by
 decide +kernel
def cuts70723 : List PrefixCut := [⟨61,166751830,166751924⟩,
⟨64,174582494,174582592⟩]
theorem checked70723 : checkPrefixCuts (2^48) 9273737217 10 Manual.Count131072.C070723.packed 64 cuts70723 = true := by
 decide +kernel
def pointBounds70723 : List (Nat × Nat × Nat) := [(9273862144,115939930025863,115940319605345)]
theorem point_links_checked70723 : (cuts70723.take 1).map (fun c => (9273737217-1+2*2^10*c.k,115939763274033+c.lower,115940152853421+c.upper)) = pointBounds70723 := by
 decide +kernel
def cuts70724 : List PrefixCut := [⟨64,173335635,173335736⟩]
theorem checked70724 : checkPrefixCuts (2^48) 9273868289 10 Manual.Count131072.C070724.packed 64 cuts70724 = true := by
 decide +kernel
def cuts70725 : List PrefixCut := [⟨64,173424224,173424329⟩]
theorem checked70725 : checkPrefixCuts (2^48) 9273999361 10 Manual.Count131072.C070725.packed 64 cuts70725 = true := by
 decide +kernel
def cuts70726 : List PrefixCut := [⟨11,30350506,30350524⟩,
⟨64,172420215,172420311⟩]
theorem checked70726 : checkPrefixCuts (2^48) 9274130433 10 Manual.Count131072.C070726.packed 64 cuts70726 = true := by
 decide +kernel
def pointBounds70726 : List (Nat × Nat × Nat) := [(9274152960,115940314966892,115940704546602)]
theorem point_links_checked70726 : (cuts70726.take 1).map (fun c => (9274130433-1+2*2^10*c.k,115940284616386+c.lower,115940674196078+c.upper)) = pointBounds70726 := by
 decide +kernel
def cuts70727 : List PrefixCut := [⟨64,171962529,171962637⟩]
theorem checked70727 : checkPrefixCuts (2^48) 9274261505 10 Manual.Count131072.C070727.packed 64 cuts70727 = true := by
 decide +kernel
def cuts70728 : List PrefixCut := [⟨25,69318489,69318528⟩,
⟨64,174934360,174934462⟩]
theorem checked70728 : checkPrefixCuts (2^48) 9274392577 10 Manual.Count131072.C070728.packed 64 cuts70728 = true := by
 decide +kernel
def pointBounds70728 : List (Nat × Nat × Nat) := [(9274443776,115940698317619,115941087897554)]
theorem point_links_checked70728 : (cuts70728.take 1).map (fun c => (9274392577-1+2*2^10*c.k,115940628999130+c.lower,115941018579026+c.upper)) = pointBounds70728 := by
 decide +kernel
def cuts70729 : List PrefixCut := [⟨64,173748259,173748364⟩]
theorem checked70729 : checkPrefixCuts (2^48) 9274523649 10 Manual.Count131072.C070729.packed 64 cuts70729 = true := by
 decide +kernel
def cuts70730 : List PrefixCut := [⟨39,105461726,105461786⟩,
⟨64,172622917,172623017⟩]
theorem checked70730 : checkPrefixCuts (2^48) 9274654721 10 Manual.Count131072.C070730.packed 64 cuts70730 = true := by
 decide +kernel
def pointBounds70730 : List (Nat × Nat × Nat) := [(9274734592,115941083143475,115941472723638)]
theorem point_links_checked70730 : (cuts70730.take 1).map (fun c => (9274654721-1+2*2^10*c.k,115940977681749+c.lower,115941367261852+c.upper)) = pointBounds70730 := by
 decide +kernel
def cuts70731 : List PrefixCut := [⟨64,172286639,172286744⟩]
theorem checked70731 : checkPrefixCuts (2^48) 9274785793 10 Manual.Count131072.C070731.packed 64 cuts70731 = true := by
 decide +kernel
def cuts70732 : List PrefixCut := [⟨53,141056537,141056625⟩,
⟨64,170675773,170675878⟩]
theorem checked70732 : checkPrefixCuts (2^48) 9274916865 10 Manual.Count131072.C070732.packed 64 cuts70732 = true := by
 decide +kernel
def pointBounds70732 : List (Nat × Nat × Nat) := [(9275025408,115941463647842,115941853228238)]
theorem point_links_checked70732 : (cuts70732.take 1).map (fun c => (9274916865-1+2*2^10*c.k,115941322591305+c.lower,115941712171613+c.upper)) = pointBounds70732 := by
 decide +kernel
def cuts70733 : List PrefixCut := [⟨64,171583772,171583876⟩]
theorem checked70733 : checkPrefixCuts (2^48) 9275047937 10 Manual.Count131072.C070733.packed 64 cuts70733 = true := by
 decide +kernel
def cuts70734 : List PrefixCut := [⟨64,172795234,172795337⟩]
theorem checked70734 : checkPrefixCuts (2^48) 9275179009 10 Manual.Count131072.C070734.packed 64 cuts70734 = true := by
 decide +kernel
def cuts70735 : List PrefixCut := [⟨3,8011522,8011526⟩,
⟨64,177253726,177253822⟩]
theorem checked70735 : checkPrefixCuts (2^48) 9275310081 10 Manual.Count131072.C070735.packed 64 cuts70735 = true := by
 decide +kernel
def pointBounds70735 : List (Nat × Nat × Nat) := [(9275316224,115941845657606,115942235238230)]
theorem point_links_checked70735 : (cuts70735.take 1).map (fun c => (9275310081-1+2*2^10*c.k,115941837646084+c.lower,115942227226704+c.upper)) = pointBounds70735 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000022
