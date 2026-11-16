import PlattAssemblyKernel
import PlattCertificates.Count131072.C068704
import PlattCertificates.Count131072.C068705
import PlattCertificates.Count131072.C068706
import PlattCertificates.Count131072.C068707
import PlattCertificates.Count131072.C068708
import PlattCertificates.Count131072.C068709
import PlattCertificates.Count131072.C068710
import PlattCertificates.Count131072.C068711
import PlattCertificates.Count131072.C068712
import PlattCertificates.Count131072.C068713
import PlattCertificates.Count131072.C068714
import PlattCertificates.Count131072.C068715
import PlattCertificates.Count131072.C068716
import PlattCertificates.Count131072.C068717
import PlattCertificates.Count131072.C068718
import PlattCertificates.Count131072.C068719
import PlattCertificates.Count131072.C068720
import PlattCertificates.Count131072.C068721
import PlattCertificates.Count131072.C068722
import PlattCertificates.Count131072.C068723
import PlattCertificates.Count131072.C068724
import PlattCertificates.Count131072.C068725
import PlattCertificates.Count131072.C068726
import PlattCertificates.Count131072.C068727
import PlattCertificates.Count131072.C068728
import PlattCertificates.Count131072.C068729
import PlattCertificates.Count131072.C068730
import PlattCertificates.Count131072.C068731
import PlattCertificates.Count131072.C068732
import PlattCertificates.Count131072.C068733
import PlattCertificates.Count131072.C068734
import PlattCertificates.Count131072.C068735
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000272
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68704 : List PrefixCut := [⟨64,178367202,178367310⟩]
theorem checked68704 : checkPrefixCuts (2^48) 9009102849 10 Manual.Count131072.C068704.packed 64 cuts68704 = true := by
 decide +kernel
def cuts68705 : List PrefixCut := [⟨15,41615517,41615540⟩,
⟨64,178739521,178739628⟩]
theorem checked68705 : checkPrefixCuts (2^48) 9009233921 10 Manual.Count131072.C068705.packed 64 cuts68705 = true := by
 decide +kernel
def pointBounds68705 : List (Nat × Nat × Nat) := [(9009264640,115584679233087,115585068603765)]
theorem point_links_checked68705 : (cuts68705.take 1).map (fun c => (9009233921-1+2*2^10*c.k,115584637617570+c.lower,115585026988225+c.upper)) = pointBounds68705 := by
 decide +kernel
def cuts68706 : List PrefixCut := [⟨64,177331026,177331124⟩]
theorem checked68706 : checkPrefixCuts (2^48) 9009364993 10 Manual.Count131072.C068706.packed 64 cuts68706 = true := by
 decide +kernel
def cuts68707 : List PrefixCut := [⟨25,70731740,70731777⟩,
⟨64,179983991,179984093⟩]
theorem checked68707 : checkPrefixCuts (2^48) 9009496065 10 Manual.Count131072.C068707.packed 64 cuts68707 = true := by
 decide +kernel
def pointBounds68707 : List (Nat × Nat × Nat) := [(9009547264,115585064419857,115585453790754)]
theorem point_links_checked68707 : (cuts68707.take 1).map (fun c => (9009496065-1+2*2^10*c.k,115584993688117+c.lower,115585383058977+c.upper)) = pointBounds68707 := by
 decide +kernel
def cuts68708 : List PrefixCut := [⟨64,178700482,178700586⟩]
theorem checked68708 : checkPrefixCuts (2^48) 9009627137 10 Manual.Count131072.C068708.packed 64 cuts68708 = true := by
 decide +kernel
def cuts68709 : List PrefixCut := [⟨35,95378747,95378805⟩,
⟨64,175823717,175823821⟩]
theorem checked68709 : checkPrefixCuts (2^48) 9009758209 10 Manual.Count131072.C068709.packed 64 cuts68709 = true := by
 decide +kernel
def pointBounds68709 : List (Nat × Nat × Nat) := [(9009829888,115585447751337,115585837122461)]
theorem point_links_checked68709 : (cuts68709.take 1).map (fun c => (9009758209-1+2*2^10*c.k,115585352372590+c.lower,115585741743656+c.upper)) = pointBounds68709 := by
 decide +kernel
def cuts68710 : List PrefixCut := [⟨64,181100795,181100902⟩]
theorem checked68710 : checkPrefixCuts (2^48) 9009889281 10 Manual.Count131072.C068710.packed 64 cuts68710 = true := by
 decide +kernel
def cuts68711 : List PrefixCut := [⟨45,125522500,125522572⟩,
⟨64,178005397,178005498⟩]
theorem checked68711 : checkPrefixCuts (2^48) 9010020353 10 Manual.Count131072.C068711.packed 64 cuts68711 = true := by
 decide +kernel
def pointBounds68711 : List (Nat × Nat × Nat) := [(9010112512,115585834819602,115586224190951)]
theorem point_links_checked68711 : (cuts68711.take 1).map (fun c => (9010020353-1+2*2^10*c.k,115585709297102+c.lower,115586098668379+c.upper)) = pointBounds68711 := by
 decide +kernel
def cuts68712 : List PrefixCut := [⟨64,176034724,176034819⟩]
theorem checked68712 : checkPrefixCuts (2^48) 9010151425 10 Manual.Count131072.C068712.packed 64 cuts68712 = true := by
 decide +kernel
def cuts68713 : List PrefixCut := [⟨55,152009478,152009575⟩,
⟨64,177781550,177781662⟩]
theorem checked68713 : checkPrefixCuts (2^48) 9010282497 10 Manual.Count131072.C068713.packed 64 cuts68713 = true := by
 decide +kernel
def pointBounds68713 : List (Nat × Nat × Nat) := [(9010395136,115586215346701,115586604718271)]
theorem point_links_checked68713 : (cuts68713.take 1).map (fun c => (9010282497-1+2*2^10*c.k,115586063337223+c.lower,115586452708696+c.upper)) = pointBounds68713 := by
 decide +kernel
def cuts68714 : List PrefixCut := [⟨64,180371773,180371878⟩]
theorem checked68714 : checkPrefixCuts (2^48) 9010413569 10 Manual.Count131072.C068714.packed 64 cuts68714 = true := by
 decide +kernel
def cuts68715 : List PrefixCut := [⟨64,176683046,176683146⟩]
theorem checked68715 : checkPrefixCuts (2^48) 9010544641 10 Manual.Count131072.C068715.packed 64 cuts68715 = true := by
 decide +kernel
def cuts68716 : List PrefixCut := [⟨1,2873890,2873891⟩,
⟨64,180741368,180741469⟩]
theorem checked68716 : checkPrefixCuts (2^48) 9010675713 10 Manual.Count131072.C068716.packed 64 cuts68716 = true := by
 decide +kernel
def pointBounds68716 : List (Nat × Nat × Nat) := [(9010677760,115586601047482,115586990419273)]
theorem point_links_checked68716 : (cuts68716.take 1).map (fun c => (9010675713-1+2*2^10*c.k,115586598173592+c.lower,115586987545382+c.upper)) = pointBounds68716 := by
 decide +kernel
def cuts68717 : List PrefixCut := [⟨64,180332659,180332764⟩]
theorem checked68717 : checkPrefixCuts (2^48) 9010806785 10 Manual.Count131072.C068717.packed 64 cuts68717 = true := by
 decide +kernel
def cuts68718 : List PrefixCut := [⟨11,29987505,29987523⟩,
⟨64,178955614,178955720⟩]
theorem checked68718 : checkPrefixCuts (2^48) 9010937857 10 Manual.Count131072.C068718.packed 64 cuts68718 = true := by
 decide +kernel
def pointBounds68718 : List (Nat × Nat × Nat) := [(9010960384,115586989235124,115587378607138)]
theorem point_links_checked68718 : (cuts68718.take 1).map (fun c => (9010937857-1+2*2^10*c.k,115586959247619+c.lower,115587348619615+c.upper)) = pointBounds68718 := by
 decide +kernel
def cuts68719 : List PrefixCut := [⟨64,176235445,176235543⟩]
theorem checked68719 : checkPrefixCuts (2^48) 9011068929 10 Manual.Count131072.C068719.packed 64 cuts68719 = true := by
 decide +kernel
def cuts68720 : List PrefixCut := [⟨21,58598818,58598849⟩,
⟨64,178294468,178294570⟩]
theorem checked68720 : checkPrefixCuts (2^48) 9011200001 10 Manual.Count131072.C068720.packed 64 cuts68720 = true := by
 decide +kernel
def pointBounds68720 : List (Nat × Nat × Nat) := [(9011243008,115587373037496,115587762409727)]
theorem point_links_checked68720 : (cuts68720.take 1).map (fun c => (9011200001-1+2*2^10*c.k,115587314438678+c.lower,115587703810878+c.upper)) = pointBounds68720 := by
 decide +kernel
def cuts68721 : List PrefixCut := [⟨64,178354331,178354434⟩]
theorem checked68721 : checkPrefixCuts (2^48) 9011331073 10 Manual.Count131072.C068721.packed 64 cuts68721 = true := by
 decide +kernel
def cuts68722 : List PrefixCut := [⟨31,87989267,87989317⟩,
⟨64,180350780,180350886⟩]
theorem checked68722 : checkPrefixCuts (2^48) 9011462145 10 Manual.Count131072.C068722.packed 64 cuts68722 = true := by
 decide +kernel
def pointBounds68722 : List (Nat × Nat × Nat) := [(9011525632,115587759076744,115588148449199)]
theorem point_links_checked68722 : (cuts68722.take 1).map (fun c => (9011462145-1+2*2^10*c.k,115587671087477+c.lower,115588060459882+c.upper)) = pointBounds68722 := by
 decide +kernel
def cuts68723 : List PrefixCut := [⟨64,176037793,176037894⟩]
theorem checked68723 : checkPrefixCuts (2^48) 9011593217 10 Manual.Count131072.C068723.packed 64 cuts68723 = true := by
 decide +kernel
def cuts68724 : List PrefixCut := [⟨41,115066623,115066685⟩,
⟨64,179502215,179502313⟩]
theorem checked68724 : checkPrefixCuts (2^48) 9011724289 10 Manual.Count131072.C068724.packed 64 cuts68724 = true := by
 decide +kernel
def pointBounds68724 : List (Nat × Nat × Nat) := [(9011808256,115588142542673,115588531915347)]
theorem point_links_checked68724 : (cuts68724.take 1).map (fun c => (9011724289-1+2*2^10*c.k,115588027476050+c.lower,115588416848662+c.upper)) = pointBounds68724 := by
 decide +kernel
def cuts68725 : List PrefixCut := [⟨64,178437667,178437771⟩]
theorem checked68725 : checkPrefixCuts (2^48) 9011855361 10 Manual.Count131072.C068725.packed 64 cuts68725 = true := by
 decide +kernel
def cuts68726 : List PrefixCut := [⟨51,142735775,142735858⟩,
⟨64,180683849,180683953⟩]
theorem checked68726 : checkPrefixCuts (2^48) 9011986433 10 Manual.Count131072.C068726.packed 64 cuts68726 = true := by
 decide +kernel
def pointBounds68726 : List (Nat × Nat × Nat) := [(9012090880,115588528151707,115588917524604)]
theorem point_links_checked68726 : (cuts68726.take 1).map (fun c => (9011986433-1+2*2^10*c.k,115588385415932+c.lower,115588774788746+c.upper)) = pointBounds68726 := by
 decide +kernel
def cuts68727 : List PrefixCut := [⟨64,178307528,178307638⟩]
theorem checked68727 : checkPrefixCuts (2^48) 9012117505 10 Manual.Count131072.C068727.packed 64 cuts68727 = true := by
 decide +kernel
def cuts68728 : List PrefixCut := [⟨61,169091487,169091586⟩,
⟨64,177742762,177742865⟩]
theorem checked68728 : checkPrefixCuts (2^48) 9012248577 10 Manual.Count131072.C068728.packed 64 cuts68728 = true := by
 decide +kernel
def pointBounds68728 : List (Nat × Nat × Nat) := [(9012373504,115588913498796,115589302871923)]
theorem point_links_checked68728 : (cuts68728.take 1).map (fun c => (9012248577-1+2*2^10*c.k,115588744407309+c.lower,115589133780337+c.upper)) = pointBounds68728 := by
 decide +kernel
def cuts68729 : List PrefixCut := [⟨64,180113783,180113889⟩]
theorem checked68729 : checkPrefixCuts (2^48) 9012379649 10 Manual.Count131072.C068729.packed 64 cuts68729 = true := by
 decide +kernel
def cuts68730 : List PrefixCut := [⟨64,177518975,177519080⟩]
theorem checked68730 : checkPrefixCuts (2^48) 9012510721 10 Manual.Count131072.C068730.packed 64 cuts68730 = true := by
 decide +kernel
def cuts68731 : List PrefixCut := [⟨7,20393906,20393917⟩,
⟨64,176517025,176517125⟩]
theorem checked68731 : checkPrefixCuts (2^48) 9012641793 10 Manual.Count131072.C068731.packed 64 cuts68731 = true := by
 decide +kernel
def pointBounds68731 : List (Nat × Nat × Nat) := [(9012656128,115589300176735,115589689550088)]
theorem point_links_checked68731 : (cuts68731.take 1).map (fun c => (9012641793-1+2*2^10*c.k,115589279782829+c.lower,115589669156171+c.upper)) = pointBounds68731 := by
 decide +kernel
def cuts68732 : List PrefixCut := [⟨64,180199629,180199735⟩]
theorem checked68732 : checkPrefixCuts (2^48) 9012772865 10 Manual.Count131072.C068732.packed 64 cuts68732 = true := by
 decide +kernel
def cuts68733 : List PrefixCut := [⟨17,46657847,46657868⟩,
⟨64,180727914,180728012⟩]
theorem checked68733 : checkPrefixCuts (2^48) 9012903937 10 Manual.Count131072.C068733.packed 64 cuts68733 = true := by
 decide +kernel
def pointBounds68733 : List (Nat × Nat × Nat) := [(9012938752,115589683157330,115590072530899)]
theorem point_links_checked68733 : (cuts68733.take 1).map (fun c => (9012903937-1+2*2^10*c.k,115589636499483+c.lower,115590025873031+c.upper)) = pointBounds68733 := by
 decide +kernel
def cuts68734 : List PrefixCut := [⟨64,179975768,179975871⟩]
theorem checked68734 : checkPrefixCuts (2^48) 9013035009 10 Manual.Count131072.C068734.packed 64 cuts68734 = true := by
 decide +kernel
def cuts68735 : List PrefixCut := [⟨27,73045121,73045162⟩,
⟨64,176319354,176319457⟩]
theorem checked68735 : checkPrefixCuts (2^48) 9013166081 10 Manual.Count131072.C068735.packed 64 cuts68735 = true := by
 decide +kernel
def pointBounds68735 : List (Nat × Nat × Nat) := [(9013221376,115590070248286,115590459622076)]
theorem point_links_checked68735 : (cuts68735.take 1).map (fun c => (9013166081-1+2*2^10*c.k,115589997203165+c.lower,115590386576914+c.upper)) = pointBounds68735 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000272
