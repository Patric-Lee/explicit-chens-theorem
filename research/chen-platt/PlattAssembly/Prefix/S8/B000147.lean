import PlattAssemblyKernel
import PlattCertificates.Count131072.C074704
import PlattCertificates.Count131072.C074705
import PlattCertificates.Count131072.C074706
import PlattCertificates.Count131072.C074707
import PlattCertificates.Count131072.C074708
import PlattCertificates.Count131072.C074709
import PlattCertificates.Count131072.C074710
import PlattCertificates.Count131072.C074711
import PlattCertificates.Count131072.C074712
import PlattCertificates.Count131072.C074713
import PlattCertificates.Count131072.C074714
import PlattCertificates.Count131072.C074715
import PlattCertificates.Count131072.C074716
import PlattCertificates.Count131072.C074717
import PlattCertificates.Count131072.C074718
import PlattCertificates.Count131072.C074719
import PlattCertificates.Count131072.C074720
import PlattCertificates.Count131072.C074721
import PlattCertificates.Count131072.C074722
import PlattCertificates.Count131072.C074723
import PlattCertificates.Count131072.C074724
import PlattCertificates.Count131072.C074725
import PlattCertificates.Count131072.C074726
import PlattCertificates.Count131072.C074727
import PlattCertificates.Count131072.C074728
import PlattCertificates.Count131072.C074729
import PlattCertificates.Count131072.C074730
import PlattCertificates.Count131072.C074731
import PlattCertificates.Count131072.C074732
import PlattCertificates.Count131072.C074733
import PlattCertificates.Count131072.C074734
import PlattCertificates.Count131072.C074735
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000147
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74704 : List PrefixCut := [⟨64,163817257,163817352⟩]
theorem checked74704 : checkPrefixCuts (2^48) 9795534849 10 Manual.Count131072.C074704.packed 64 cuts74704 = true := by
 decide +kernel
def cuts74705 : List PrefixCut := [⟨41,106863652,106863709⟩,
⟨64,164993183,164993276⟩]
theorem checked74705 : checkPrefixCuts (2^48) 9795665921 10 Manual.Count131072.C074705.packed 64 cuts74705 = true := by
 decide +kernel
def pointBounds74705 : List (Nat × Nat × Nat) := [(9795749888,116610636235911,116611026214395)]
theorem point_links_checked74705 : (cuts74705.take 1).map (fun c => (9795665921-1+2*2^10*c.k,116610529372259+c.lower,116610919350686+c.upper)) = pointBounds74705 := by
 decide +kernel
def cuts74706 : List PrefixCut := [⟨64,163295665,163295770⟩]
theorem checked74706 : checkPrefixCuts (2^48) 9795796993 10 Manual.Count131072.C074706.packed 64 cuts74706 = true := by
 decide +kernel
def cuts74707 : List PrefixCut := [⟨63,160764940,160765032⟩,
⟨64,163437154,163437248⟩]
theorem checked74707 : checkPrefixCuts (2^48) 9795928065 10 Manual.Count131072.C074707.packed 64 cuts74707 = true := by
 decide +kernel
def pointBounds74707 : List (Nat × Nat × Nat) := [(9796057088,116611018426047,116611408404764)]
theorem point_links_checked74707 : (cuts74707.take 1).map (fun c => (9795928065-1+2*2^10*c.k,116610857661107+c.lower,116611247639732+c.upper)) = pointBounds74707 := by
 decide +kernel
def cuts74708 : List PrefixCut := [⟨64,161998283,161998386⟩]
theorem checked74708 : checkPrefixCuts (2^48) 9796059137 10 Manual.Count131072.C074708.packed 64 cuts74708 = true := by
 decide +kernel
def cuts74709 : List PrefixCut := [⟨64,165214210,165214307⟩]
theorem checked74709 : checkPrefixCuts (2^48) 9796190209 10 Manual.Count131072.C074709.packed 64 cuts74709 = true := by
 decide +kernel
def cuts74710 : List PrefixCut := [⟨21,53327797,53327831⟩,
⟨64,163200717,163200814⟩]
theorem checked74710 : checkPrefixCuts (2^48) 9796321281 10 Manual.Count131072.C074710.packed 64 cuts74710 = true := by
 decide +kernel
def pointBounds74710 : List (Nat × Nat × Nat) := [(9796364288,116611401638551,116611791617504)]
theorem point_links_checked74710 : (cuts74710.take 1).map (fun c => (9796321281-1+2*2^10*c.k,116611348310754+c.lower,116611738289673+c.upper)) = pointBounds74710 := by
 decide +kernel
def cuts74711 : List PrefixCut := [⟨64,165726960,165727056⟩]
theorem checked74711 : checkPrefixCuts (2^48) 9796452353 10 Manual.Count131072.C074711.packed 64 cuts74711 = true := by
 decide +kernel
def cuts74712 : List PrefixCut := [⟨43,110215244,110215313⟩,
⟨64,164144499,164144603⟩]
theorem checked74712 : checkPrefixCuts (2^48) 9796583425 10 Manual.Count131072.C074712.packed 64 cuts74712 = true := by
 decide +kernel
def pointBounds74712 : List (Nat × Nat × Nat) := [(9796671488,116611787453675,116612177432856)]
theorem point_links_checked74712 : (cuts74712.take 1).map (fun c => (9796583425-1+2*2^10*c.k,116611677238431+c.lower,116612067217543+c.upper)) = pointBounds74712 := by
 decide +kernel
def cuts74713 : List PrefixCut := [⟨64,162159844,162159947⟩]
theorem checked74713 : checkPrefixCuts (2^48) 9796714497 10 Manual.Count131072.C074713.packed 64 cuts74713 = true := by
 decide +kernel
def cuts74714 : List PrefixCut := [⟨64,165777783,165777880⟩]
theorem checked74714 : checkPrefixCuts (2^48) 9796845569 10 Manual.Count131072.C074714.packed 64 cuts74714 = true := by
 decide +kernel
def cuts74715 : List PrefixCut := [⟨1,2700694,2700696⟩,
⟨64,162643918,162644016⟩]
theorem checked74715 : checkPrefixCuts (2^48) 9796976641 10 Manual.Count131072.C074715.packed 64 cuts74715 = true := by
 decide +kernel
def pointBounds74715 : List (Nat × Nat × Nat) := [(9796978688,116612172021251,116612562000669)]
theorem point_links_checked74715 : (cuts74715.take 1).map (fun c => (9796976641-1+2*2^10*c.k,116612169320557+c.lower,116612559299973+c.upper)) = pointBounds74715 := by
 decide +kernel
def cuts74716 : List PrefixCut := [⟨64,163934608,163934699⟩]
theorem checked74716 : checkPrefixCuts (2^48) 9797107713 10 Manual.Count131072.C074716.packed 64 cuts74716 = true := by
 decide +kernel
def cuts74717 : List PrefixCut := [⟨23,58666564,58666601⟩,
⟨64,162352269,162352372⟩]
theorem checked74717 : checkPrefixCuts (2^48) 9797238785 10 Manual.Count131072.C074717.packed 64 cuts74717 = true := by
 decide +kernel
def pointBounds74717 : List (Nat × Nat × Nat) := [(9797285888,116612554565647,116612944545289)]
theorem point_links_checked74717 : (cuts74717.take 1).map (fun c => (9797238785-1+2*2^10*c.k,116612495899083+c.lower,116612885878688+c.upper)) = pointBounds74717 := by
 decide +kernel
def cuts74718 : List PrefixCut := [⟨64,161402026,161402125⟩]
theorem checked74718 : checkPrefixCuts (2^48) 9797369857 10 Manual.Count131072.C074718.packed 64 cuts74718 = true := by
 decide +kernel
def cuts74719 : List PrefixCut := [⟨45,115117582,115117653⟩,
⟨64,164588794,164588895⟩]
theorem checked74719 : checkPrefixCuts (2^48) 9797500929 10 Manual.Count131072.C074719.packed 64 cuts74719 = true := by
 decide +kernel
def pointBounds74719 : List (Nat × Nat × Nat) := [(9797593088,116612934770960,116613324750838)]
theorem point_links_checked74719 : (cuts74719.take 1).map (fun c => (9797500929-1+2*2^10*c.k,116612819653378+c.lower,116613209633185+c.upper)) = pointBounds74719 := by
 decide +kernel
def cuts74720 : List PrefixCut := [⟨64,163523631,163523733⟩]
theorem checked74720 : checkPrefixCuts (2^48) 9797632001 10 Manual.Count131072.C074720.packed 64 cuts74720 = true := by
 decide +kernel
def cuts74721 : List PrefixCut := [⟨64,161338097,161338189⟩]
theorem checked74721 : checkPrefixCuts (2^48) 9797763073 10 Manual.Count131072.C074721.packed 64 cuts74721 = true := by
 decide +kernel
def cuts74722 : List PrefixCut := [⟨3,7957681,7957686⟩,
⟨64,162456314,162456417⟩]
theorem checked74722 : checkPrefixCuts (2^48) 9797894145 10 Manual.Count131072.C074722.packed 64 cuts74722 = true := by
 decide +kernel
def pointBounds74722 : List (Nat × Nat × Nat) := [(9797900288,116613317061581,116613707041688)]
theorem point_links_checked74722 : (cuts74722.take 1).map (fun c => (9797894145-1+2*2^10*c.k,116613309103900+c.lower,116613699084002+c.upper)) = pointBounds74722 := by
 decide +kernel
def cuts74723 : List PrefixCut := [⟨64,163631981,163632079⟩]
theorem checked74723 : checkPrefixCuts (2^48) 9798025217 10 Manual.Count131072.C074723.packed 64 cuts74723 = true := by
 decide +kernel
def cuts74724 : List PrefixCut := [⟨25,64636329,64636369⟩,
⟨64,164750152,164750248⟩]
theorem checked74724 : checkPrefixCuts (2^48) 9798156289 10 Manual.Count131072.C074724.packed 64 cuts74724 = true := by
 decide +kernel
def pointBounds74724 : List (Nat × Nat × Nat) := [(9798207488,116613699828524,116614089808867)]
theorem point_links_checked74724 : (cuts74724.take 1).map (fun c => (9798156289-1+2*2^10*c.k,116613635192195+c.lower,116614025172498+c.upper)) = pointBounds74724 := by
 decide +kernel
def cuts74725 : List PrefixCut := [⟨64,162564699,162564802⟩]
theorem checked74725 : checkPrefixCuts (2^48) 9798287361 10 Manual.Count131072.C074725.packed 64 cuts74725 = true := by
 decide +kernel
def cuts74726 : List PrefixCut := [⟨47,120536073,120536143⟩,
⟨64,163769049,163769146⟩]
theorem checked74726 : checkPrefixCuts (2^48) 9798418433 10 Manual.Count131072.C074726.packed 64 cuts74726 = true := by
 decide +kernel
def pointBounds74726 : List (Nat × Nat × Nat) := [(9798514688,116614083043119,116614473023691)]
theorem point_links_checked74726 : (cuts74726.take 1).map (fun c => (9798418433-1+2*2^10*c.k,116613962507046+c.lower,116614352487548+c.upper)) = pointBounds74726 := by
 decide +kernel
def cuts74727 : List PrefixCut := [⟨64,164169021,164169124⟩]
theorem checked74727 : checkPrefixCuts (2^48) 9798549505 10 Manual.Count131072.C074727.packed 64 cuts74727 = true := by
 decide +kernel
def cuts74728 : List PrefixCut := [⟨64,160432495,160432592⟩]
theorem checked74728 : checkPrefixCuts (2^48) 9798680577 10 Manual.Count131072.C074728.packed 64 cuts74728 = true := by
 decide +kernel
def cuts74729 : List PrefixCut := [⟨5,13644563,13644572⟩,
⟨64,166721176,166721273⟩]
theorem checked74729 : checkPrefixCuts (2^48) 9798811649 10 Manual.Count131072.C074729.packed 64 cuts74729 = true := by
 decide +kernel
def pointBounds74729 : List (Nat × Nat × Nat) := [(9798821888,116614464522174,116614854502982)]
theorem point_links_checked74729 : (cuts74729.take 1).map (fun c => (9798811649-1+2*2^10*c.k,116614450877611+c.lower,116614840858410+c.upper)) = pointBounds74729 := by
 decide +kernel
def cuts74730 : List PrefixCut := [⟨64,163243241,163243339⟩]
theorem checked74730 : checkPrefixCuts (2^48) 9798942721 10 Manual.Count131072.C074730.packed 64 cuts74730 = true := by
 decide +kernel
def cuts74731 : List PrefixCut := [⟨27,69283645,69283687⟩,
⟨64,162005909,162006008⟩]
theorem checked74731 : checkPrefixCuts (2^48) 9799073793 10 Manual.Count131072.C074731.packed 64 cuts74731 = true := by
 decide +kernel
def pointBounds74731 : List (Nat × Nat × Nat) := [(9799129088,116614850125673,116615240106709)]
theorem point_links_checked74731 : (cuts74731.take 1).map (fun c => (9799073793-1+2*2^10*c.k,116614780842028+c.lower,116615170823022+c.upper)) = pointBounds74731 := by
 decide +kernel
def cuts74732 : List PrefixCut := [⟨64,164387846,164387944⟩]
theorem checked74732 : checkPrefixCuts (2^48) 9799204865 10 Manual.Count131072.C074732.packed 64 cuts74732 = true := by
 decide +kernel
def cuts74733 : List PrefixCut := [⟨49,125206729,125206800⟩,
⟨64,163150516,163150610⟩]
theorem checked74733 : checkPrefixCuts (2^48) 9799335937 10 Manual.Count131072.C074733.packed 64 cuts74733 = true := by
 decide +kernel
def pointBounds74733 : List (Nat × Nat × Nat) := [(9799436288,116615232442512,116615622423774)]
theorem point_links_checked74733 : (cuts74733.take 1).map (fun c => (9799335937-1+2*2^10*c.k,116615107235783+c.lower,116615497216974+c.upper)) = pointBounds74733 := by
 decide +kernel
def cuts74734 : List PrefixCut := [⟨64,162803652,162803752⟩]
theorem checked74734 : checkPrefixCuts (2^48) 9799467009 10 Manual.Count131072.C074734.packed 64 cuts74734 = true := by
 decide +kernel
def cuts74735 : List PrefixCut := [⟨64,162428081,162428185⟩]
theorem checked74735 : checkPrefixCuts (2^48) 9799598081 10 Manual.Count131072.C074735.packed 64 cuts74735 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000147
