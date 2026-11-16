import PlattAssemblyKernel
import PlattCertificates.Count131072.C042752
import PlattCertificates.Count131072.C042753
import PlattCertificates.Count131072.C042754
import PlattCertificates.Count131072.C042755
import PlattCertificates.Count131072.C042756
import PlattCertificates.Count131072.C042757
import PlattCertificates.Count131072.C042758
import PlattCertificates.Count131072.C042759
import PlattCertificates.Count131072.C042760
import PlattCertificates.Count131072.C042761
import PlattCertificates.Count131072.C042762
import PlattCertificates.Count131072.C042763
import PlattCertificates.Count131072.C042764
import PlattCertificates.Count131072.C042765
import PlattCertificates.Count131072.C042766
import PlattCertificates.Count131072.C042767
import PlattCertificates.Count131072.C042768
import PlattCertificates.Count131072.C042769
import PlattCertificates.Count131072.C042770
import PlattCertificates.Count131072.C042771
import PlattCertificates.Count131072.C042772
import PlattCertificates.Count131072.C042773
import PlattCertificates.Count131072.C042774
import PlattCertificates.Count131072.C042775
import PlattCertificates.Count131072.C042776
import PlattCertificates.Count131072.C042777
import PlattCertificates.Count131072.C042778
import PlattCertificates.Count131072.C042779
import PlattCertificates.Count131072.C042780
import PlattCertificates.Count131072.C042781
import PlattCertificates.Count131072.C042782
import PlattCertificates.Count131072.C042783
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000086
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42752 : List PrefixCut := [⟨64,293140937,293141108⟩]
theorem checked42752 : checkPrefixCuts (2^48) 5607522305 10 Manual.Count131072.C042752.packed 64 cuts42752 = true := by
 decide +kernel
def cuts42753 : List PrefixCut := [⟨10,44422292,44422320⟩,
⟨64,292782701,292782873⟩]
theorem checked42753 : checkPrefixCuts (2^48) 5607653377 10 Manual.Count131072.C042753.packed 64 cuts42753 = true := by
 decide +kernel
def pointBounds42753 : List (Nat × Nat × Nat) := [(5607673856,109701516191313,109701902188673)]
theorem point_links_checked42753 : (cuts42753.take 1).map (fun c => (5607653377-1+2*2^10*c.k,109701471769021+c.lower,109701857766353+c.upper)) = pointBounds42753 := by
 decide +kernel
def cuts42754 : List PrefixCut := [⟨32,146162909,146162993⟩,
⟨64,295084705,295084881⟩]
theorem checked42754 : checkPrefixCuts (2^48) 5607784449 10 Manual.Count131072.C042754.packed 64 cuts42754 = true := by
 decide +kernel
def pointBounds42754 : List (Nat × Nat × Nat) := [(5607849984,109701910714631,109702296712219)]
theorem point_links_checked42754 : (cuts42754.take 1).map (fun c => (5607784449-1+2*2^10*c.k,109701764551722+c.lower,109702150549226+c.upper)) = pointBounds42754 := by
 decide +kernel
def cuts42755 : List PrefixCut := [⟨54,246542777,246542925⟩,
⟨64,294425322,294425498⟩]
theorem checked42755 : checkPrefixCuts (2^48) 5607915521 10 Manual.Count131072.C042755.packed 64 cuts42755 = true := by
 decide +kernel
def pointBounds42755 : List (Nat × Nat × Nat) := [(5608026112,109702306179204,109702692177032)]
theorem point_links_checked42755 : (cuts42755.take 1).map (fun c => (5607915521-1+2*2^10*c.k,109702059636427+c.lower,109702445634107+c.upper)) = pointBounds42755 := by
 decide +kernel
def cuts42756 : List PrefixCut := [⟨64,288295224,288295399⟩]
theorem checked42756 : checkPrefixCuts (2^48) 5608046593 10 Manual.Count131072.C042756.packed 64 cuts42756 = true := by
 decide +kernel
def cuts42757 : List PrefixCut := [⟨12,56262960,56262990⟩,
⟨64,293407787,293407959⟩]
theorem checked42757 : checkPrefixCuts (2^48) 5608177665 10 Manual.Count131072.C042757.packed 64 cuts42757 = true := by
 decide +kernel
def pointBounds42757 : List (Nat × Nat × Nat) := [(5608202240,109702698619933,109703084617994)]
theorem point_links_checked42757 : (cuts42757.take 1).map (fun c => (5608177665-1+2*2^10*c.k,109702642356973+c.lower,109703028355004+c.upper)) = pointBounds42757 := by
 decide +kernel
def cuts42758 : List PrefixCut := [⟨34,160101619,160101711⟩,
⟨64,295408492,295408663⟩]
theorem checked42758 : checkPrefixCuts (2^48) 5608308737 10 Manual.Count131072.C042758.packed 64 cuts42758 = true := by
 decide +kernel
def pointBounds42758 : List (Nat × Nat × Nat) := [(5608378368,109703095866379,109703481864674)]
theorem point_links_checked42758 : (cuts42758.take 1).map (fun c => (5608308737-1+2*2^10*c.k,109702935764760+c.lower,109703321762963+c.upper)) = pointBounds42758 := by
 decide +kernel
def cuts42759 : List PrefixCut := [⟨56,258062711,258062863⟩,
⟨64,294347649,294347823⟩]
theorem checked42759 : checkPrefixCuts (2^48) 5608439809 10 Manual.Count131072.C042759.packed 64 cuts42759 = true := by
 decide +kernel
def pointBounds42759 : List (Nat × Nat × Nat) := [(5608554496,109703489235963,109703875234489)]
theorem point_links_checked42759 : (cuts42759.take 1).map (fun c => (5608439809-1+2*2^10*c.k,109703231173252+c.lower,109703617171626+c.upper)) = pointBounds42759 := by
 decide +kernel
def cuts42760 : List PrefixCut := [⟨64,289221794,289221959⟩]
theorem checked42760 : checkPrefixCuts (2^48) 5608570881 10 Manual.Count131072.C042760.packed 64 cuts42760 = true := by
 decide +kernel
def cuts42761 : List PrefixCut := [⟨14,62330096,62330132⟩,
⟨64,288261508,288261675⟩]
theorem checked42761 : checkPrefixCuts (2^48) 5608701953 10 Manual.Count131072.C042761.packed 64 cuts42761 = true := by
 decide +kernel
def pointBounds42761 : List (Nat × Nat × Nat) := [(5608730624,109703877072791,109704263071540)]
theorem point_links_checked42761 : (cuts42761.take 1).map (fun c => (5608701953-1+2*2^10*c.k,109703814742695+c.lower,109704200741408+c.upper)) = pointBounds42761 := by
 decide +kernel
def cuts42762 : List PrefixCut := [⟨36,166108678,166108774⟩,
⟨64,296836175,296836346⟩]
theorem checked42762 : checkPrefixCuts (2^48) 5608833025 10 Manual.Count131072.C042762.packed 64 cuts42762 = true := by
 decide +kernel
def pointBounds42762 : List (Nat × Nat × Nat) := [(5608906752,109704269112881,109704655111857)]
theorem point_links_checked42762 : (cuts42762.take 1).map (fun c => (5608833025-1+2*2^10*c.k,109704103004203+c.lower,109704489003083+c.upper)) = pointBounds42762 := by
 decide +kernel
def cuts42763 : List PrefixCut := [⟨58,265917141,265917302⟩,
⟨64,293918656,293918833⟩]
theorem checked42763 : checkPrefixCuts (2^48) 5608964097 10 Manual.Count131072.C042763.packed 64 cuts42763 = true := by
 decide +kernel
def pointBounds42763 : List (Nat × Nat × Nat) := [(5609082880,109704665757519,109705051756731)]
theorem point_links_checked42763 : (cuts42763.take 1).map (fun c => (5608964097-1+2*2^10*c.k,109704399840378+c.lower,109704785839429+c.upper)) = pointBounds42763 := by
 decide +kernel
def cuts42764 : List PrefixCut := [⟨64,293259416,293259593⟩]
theorem checked42764 : checkPrefixCuts (2^48) 5609095169 10 Manual.Count131072.C042764.packed 64 cuts42764 = true := by
 decide +kernel
def cuts42765 : List PrefixCut := [⟨16,73915956,73915997⟩,
⟨64,291697002,291697170⟩]
theorem checked42765 : checkPrefixCuts (2^48) 5609226241 10 Manual.Count131072.C042765.packed 64 cuts42765 = true := by
 decide +kernel
def pointBounds42765 : List (Nat × Nat × Nat) := [(5609259008,109705060934406,109705446933852)]
theorem point_links_checked42765 : (cuts42765.take 1).map (fun c => (5609226241-1+2*2^10*c.k,109704987018450+c.lower,109705373017855+c.upper)) = pointBounds42765 := by
 decide +kernel
def cuts42766 : List PrefixCut := [⟨38,174824250,174824351⟩,
⟨64,294450019,294450192⟩]
theorem checked42766 : checkPrefixCuts (2^48) 5609357313 10 Manual.Count131072.C042766.packed 64 cuts42766 = true := by
 decide +kernel
def pointBounds42766 : List (Nat × Nat × Nat) := [(5609435136,109705453539702,109705839539376)]
theorem point_links_checked42766 : (cuts42766.take 1).map (fun c => (5609357313-1+2*2^10*c.k,109705278715452+c.lower,109705664715025+c.upper)) = pointBounds42766 := by
 decide +kernel
def cuts42767 : List PrefixCut := [⟨60,274924175,274924338⟩,
⟨64,293539923,293540098⟩]
theorem checked42767 : checkPrefixCuts (2^48) 5609488385 10 Manual.Count131072.C042767.packed 64 cuts42767 = true := by
 decide +kernel
def pointBounds42767 : List (Nat × Nat × Nat) := [(5609611264,109705848089646,109706234089555)]
theorem point_links_checked42767 : (cuts42767.take 1).map (fun c => (5609488385-1+2*2^10*c.k,109705573165471+c.lower,109705959165217+c.upper)) = pointBounds42767 := by
 decide +kernel
def cuts42768 : List PrefixCut := [⟨64,292830609,292830775⟩]
theorem checked42768 : checkPrefixCuts (2^48) 5609619457 10 Manual.Count131072.C042768.packed 64 cuts42768 = true := by
 decide +kernel
def cuts42769 : List PrefixCut := [⟨18,81485575,81485623⟩,
⟨64,291719924,291720095⟩]
theorem checked42769 : checkPrefixCuts (2^48) 5609750529 10 Manual.Count131072.C042769.packed 64 cuts42769 = true := by
 decide +kernel
def pointBounds42769 : List (Nat × Nat × Nat) := [(5609787392,109706241021578,109706627021713)]
theorem point_links_checked42769 : (cuts42769.take 1).map (fun c => (5609750529-1+2*2^10*c.k,109706159536003+c.lower,109706545536090+c.upper)) = pointBounds42769 := by
 decide +kernel
def cuts42770 : List PrefixCut := [⟨40,180427395,180427499⟩,
⟨64,289956982,289957153⟩]
theorem checked42770 : checkPrefixCuts (2^48) 5609881601 10 Manual.Count131072.C042770.packed 64 cuts42770 = true := by
 decide +kernel
def pointBounds42770 : List (Nat × Nat × Nat) := [(5609963520,109706631683322,109707017683684)]
theorem point_links_checked42770 : (cuts42770.take 1).map (fun c => (5609881601-1+2*2^10*c.k,109706451255927+c.lower,109706837256185+c.upper)) = pointBounds42770 := by
 decide +kernel
def cuts42771 : List PrefixCut := [⟨62,282775601,282775771⟩,
⟨64,292408724,292408898⟩]
theorem checked42771 : checkPrefixCuts (2^48) 5610012673 10 Manual.Count131072.C042771.packed 64 cuts42771 = true := by
 decide +kernel
def pointBounds42771 : List (Nat × Nat × Nat) := [(5610139648,109707023988510,109707409989109)]
theorem point_links_checked42771 : (cuts42771.take 1).map (fun c => (5610012673-1+2*2^10*c.k,109706741212909+c.lower,109707127213338+c.upper)) = pointBounds42771 := by
 decide +kernel
def cuts42772 : List PrefixCut := [⟨64,297669938,297670108⟩]
theorem checked42772 : checkPrefixCuts (2^48) 5610143745 10 Manual.Count131072.C042772.packed 64 cuts42772 = true := by
 decide +kernel
def cuts42773 : List PrefixCut := [⟨20,90960271,90960321⟩,
⟨64,293548948,293549112⟩]
theorem checked42773 : checkPrefixCuts (2^48) 5610274817 10 Manual.Count131072.C042773.packed 64 cuts42773 = true := by
 decide +kernel
def pointBounds42773 : List (Nat × Nat × Nat) := [(5610315776,109707422251842,109707808252665)]
theorem point_links_checked42773 : (cuts42773.take 1).map (fun c => (5610274817-1+2*2^10*c.k,109707331291571+c.lower,109707717292344+c.upper)) = pointBounds42773 := by
 decide +kernel
def cuts42774 : List PrefixCut := [⟨42,190193563,190193674⟩,
⟨64,290983443,290983612⟩]
theorem checked42774 : checkPrefixCuts (2^48) 5610405889 10 Manual.Count131072.C042774.packed 64 cuts42774 = true := by
 decide +kernel
def pointBounds42774 : List (Nat × Nat × Nat) := [(5610491904,109707815034082,109708201035130)]
theorem point_links_checked42774 : (cuts42774.take 1).map (fun c => (5610405889-1+2*2^10*c.k,109707624840519+c.lower,109708010841456+c.upper)) = pointBounds42774 := by
 decide +kernel
def cuts42775 : List PrefixCut := [⟨64,293836243,293836416⟩]
theorem checked42775 : checkPrefixCuts (2^48) 5610536961 10 Manual.Count131072.C042775.packed 64 cuts42775 = true := by
 decide +kernel
def pointBounds42775 : List (Nat × Nat × Nat) := [(5610668032,109708209660205,109708595661484)]
theorem point_links_checked42775 : (cuts42775.take 1).map (fun c => (5610536961-1+2*2^10*c.k,109707915823962+c.lower,109708301825068+c.upper)) = pointBounds42775 := by
 decide +kernel
def cuts42776 : List PrefixCut := [⟨64,295986571,295986742⟩]
theorem checked42776 : checkPrefixCuts (2^48) 5610668033 10 Manual.Count131072.C042776.packed 64 cuts42776 = true := by
 decide +kernel
def cuts42777 : List PrefixCut := [⟨22,100583687,100583749⟩,
⟨64,288856106,288856276⟩]
theorem checked42777 : checkPrefixCuts (2^48) 5610799105 10 Manual.Count131072.C042777.packed 64 cuts42777 = true := by
 decide +kernel
def pointBounds42777 : List (Nat × Nat × Nat) := [(5610844160,109708606230463,109708992231975)]
theorem point_links_checked42777 : (cuts42777.take 1).map (fun c => (5610799105-1+2*2^10*c.k,109708505646776+c.lower,109708891648226+c.upper)) = pointBounds42777 := by
 decide +kernel
def cuts42778 : List PrefixCut := [⟨44,202365836,202365953⟩,
⟨64,293013032,293013206⟩]
theorem checked42778 : checkPrefixCuts (2^48) 5610930177 10 Manual.Count131072.C042778.packed 64 cuts42778 = true := by
 decide +kernel
def pointBounds42778 : List (Nat × Nat × Nat) := [(5611020288,109708996868718,109709382870455)]
theorem point_links_checked42778 : (cuts42778.take 1).map (fun c => (5610930177-1+2*2^10*c.k,109708794502882+c.lower,109709180504502+c.upper)) = pointBounds42778 := by
 decide +kernel
def cuts42779 : List PrefixCut := [⟨64,292404229,292404403⟩]
theorem checked42779 : checkPrefixCuts (2^48) 5611061249 10 Manual.Count131072.C042779.packed 64 cuts42779 = true := by
 decide +kernel
def cuts42780 : List PrefixCut := [⟨2,9380499,9380505⟩,
⟨64,291343980,291344149⟩]
theorem checked42780 : checkPrefixCuts (2^48) 5611192321 10 Manual.Count131072.C042780.packed 64 cuts42780 = true := by
 decide +kernel
def pointBounds42780 : List (Nat × Nat × Nat) := [(5611196416,109709389300642,109709775302616)]
theorem point_links_checked42780 : (cuts42780.take 1).map (fun c => (5611192321-1+2*2^10*c.k,109709379920143+c.lower,109709765922111+c.upper)) = pointBounds42780 := by
 decide +kernel
def cuts42781 : List PrefixCut := [⟨24,109452882,109452946⟩,
⟨64,294898610,294898782⟩]
theorem checked42781 : checkPrefixCuts (2^48) 5611323393 10 Manual.Count131072.C042781.packed 64 cuts42781 = true := by
 decide +kernel
def pointBounds42781 : List (Nat × Nat × Nat) := [(5611372544,109709780717005,109710166719206)]
theorem point_links_checked42781 : (cuts42781.take 1).map (fun c => (5611323393-1+2*2^10*c.k,109709671264123+c.lower,109710057266260+c.upper)) = pointBounds42781 := by
 decide +kernel
def cuts42782 : List PrefixCut := [⟨46,212128137,212128258⟩,
⟨64,296396545,296396714⟩]
theorem checked42782 : checkPrefixCuts (2^48) 5611454465 10 Manual.Count131072.C042782.packed 64 cuts42782 = true := by
 decide +kernel
def pointBounds42782 : List (Nat × Nat × Nat) := [(5611548672,109710178290870,109710564293300)]
theorem point_links_checked42782 : (cuts42782.take 1).map (fun c => (5611454465-1+2*2^10*c.k,109709966162733+c.lower,109710352165042+c.upper)) = pointBounds42782 := by
 decide +kernel
def cuts42783 : List PrefixCut := [⟨64,291825169,291825338⟩]
theorem checked42783 : checkPrefixCuts (2^48) 5611585537 10 Manual.Count131072.C042783.packed 64 cuts42783 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000086
