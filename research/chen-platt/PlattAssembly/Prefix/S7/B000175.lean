import PlattAssemblyKernel
import PlattCertificates.Count131072.C065600
import PlattCertificates.Count131072.C065601
import PlattCertificates.Count131072.C065602
import PlattCertificates.Count131072.C065603
import PlattCertificates.Count131072.C065604
import PlattCertificates.Count131072.C065605
import PlattCertificates.Count131072.C065606
import PlattCertificates.Count131072.C065607
import PlattCertificates.Count131072.C065608
import PlattCertificates.Count131072.C065609
import PlattCertificates.Count131072.C065610
import PlattCertificates.Count131072.C065611
import PlattCertificates.Count131072.C065612
import PlattCertificates.Count131072.C065613
import PlattCertificates.Count131072.C065614
import PlattCertificates.Count131072.C065615
import PlattCertificates.Count131072.C065616
import PlattCertificates.Count131072.C065617
import PlattCertificates.Count131072.C065618
import PlattCertificates.Count131072.C065619
import PlattCertificates.Count131072.C065620
import PlattCertificates.Count131072.C065621
import PlattCertificates.Count131072.C065622
import PlattCertificates.Count131072.C065623
import PlattCertificates.Count131072.C065624
import PlattCertificates.Count131072.C065625
import PlattCertificates.Count131072.C065626
import PlattCertificates.Count131072.C065627
import PlattCertificates.Count131072.C065628
import PlattCertificates.Count131072.C065629
import PlattCertificates.Count131072.C065630
import PlattCertificates.Count131072.C065631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000175
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65600 : List PrefixCut := [⟨64,188929942,188930054⟩]
theorem checked65600 : checkPrefixCuts (2^48) 8602255361 10 Manual.Count131072.C065600.packed 64 cuts65600 = true := by
 decide +kernel
def cuts65601 : List PrefixCut := [⟨47,138145427,138145506⟩,
⟨64,188207221,188207329⟩]
theorem checked65601 : checkPrefixCuts (2^48) 8602386433 10 Manual.Count131072.C065601.packed 64 cuts65601 = true := by
 decide +kernel
def pointBounds65601 : List (Nat × Nat × Nat) := [(8602482688,115016788000348,115017177040147)]
theorem point_links_checked65601 : (cuts65601.take 1).map (fun c => (8602386433-1+2*2^10*c.k,115016649854921+c.lower,115017038894641+c.upper)) = pointBounds65601 := by
 decide +kernel
def cuts65602 : List PrefixCut := [⟨64,186961000,186961112⟩]
theorem checked65602 : checkPrefixCuts (2^48) 8602517505 10 Manual.Count131072.C065602.packed 64 cuts65602 = true := by
 decide +kernel
def cuts65603 : List PrefixCut := [⟨51,150607228,150607315⟩,
⟨64,188594121,188594228⟩]
theorem checked65603 : checkPrefixCuts (2^48) 8602648577 10 Manual.Count131072.C065603.packed 64 cuts65603 = true := by
 decide +kernel
def pointBounds65603 : List (Nat × Nat × Nat) := [(8602753024,115017175630370,115017564670397)]
theorem point_links_checked65603 : (cuts65603.take 1).map (fun c => (8602648577-1+2*2^10*c.k,115017025023142+c.lower,115017414063082+c.upper)) = pointBounds65603 := by
 decide +kernel
def cuts65604 : List PrefixCut := [⟨64,184894030,184894136⟩]
theorem checked65604 : checkPrefixCuts (2^48) 8602779649 10 Manual.Count131072.C065604.packed 64 cuts65604 = true := by
 decide +kernel
def cuts65605 : List PrefixCut := [⟨55,160319911,160320008⟩,
⟨64,186265366,186265477⟩]
theorem checked65605 : checkPrefixCuts (2^48) 8602910721 10 Manual.Count131072.C065605.packed 64 cuts65605 = true := by
 decide +kernel
def pointBounds65605 : List (Nat × Nat × Nat) := [(8603023360,115017558831204,115017947871454)]
theorem point_links_checked65605 : (cuts65605.take 1).map (fun c => (8602910721-1+2*2^10*c.k,115017398511293+c.lower,115017787551446+c.upper)) = pointBounds65605 := by
 decide +kernel
def cuts65606 : List PrefixCut := [⟨64,188716364,188716473⟩]
theorem checked65606 : checkPrefixCuts (2^48) 8603041793 10 Manual.Count131072.C065606.packed 64 cuts65606 = true := by
 decide +kernel
def cuts65607 : List PrefixCut := [⟨59,173696346,173696444⟩,
⟨64,189302398,189302505⟩]
theorem checked65607 : checkPrefixCuts (2^48) 8603172865 10 Manual.Count131072.C065607.packed 64 cuts65607 = true := by
 decide +kernel
def pointBounds65607 : List (Nat × Nat × Nat) := [(8603293696,115017947189369,115018336229840)]
theorem point_links_checked65607 : (cuts65607.take 1).map (fun c => (8603172865-1+2*2^10*c.k,115017773493023+c.lower,115018162533396+c.upper)) = pointBounds65607 := by
 decide +kernel
def cuts65608 : List PrefixCut := [⟨64,184850032,184850136⟩]
theorem checked65608 : checkPrefixCuts (2^48) 8603303937 10 Manual.Count131072.C065608.packed 64 cuts65608 = true := by
 decide +kernel
def cuts65609 : List PrefixCut := [⟨63,187170102,187170213⟩,
⟨64,190081833,190081946⟩]
theorem checked65609 : checkPrefixCuts (2^48) 8603435009 10 Manual.Count131072.C065609.packed 64 cuts65609 = true := by
 decide +kernel
def pointBounds65609 : List (Nat × Nat × Nat) := [(8603564032,115018334815555,115018723856250)]
theorem point_links_checked65609 : (cuts65609.take 1).map (fun c => (8603435009-1+2*2^10*c.k,115018147645453+c.lower,115018536686037+c.upper)) = pointBounds65609 := by
 decide +kernel
def cuts65610 : List PrefixCut := [⟨64,187886970,187887083⟩]
theorem checked65610 : checkPrefixCuts (2^48) 8603566081 10 Manual.Count131072.C065610.packed 64 cuts65610 = true := by
 decide +kernel
def cuts65611 : List PrefixCut := [⟨64,188440288,188440403⟩]
theorem checked65611 : checkPrefixCuts (2^48) 8603697153 10 Manual.Count131072.C065611.packed 64 cuts65611 = true := by
 decide +kernel
def cuts65612 : List PrefixCut := [⟨3,8734922,8734927⟩,
⟨64,187259671,187259778⟩]
theorem checked65612 : checkPrefixCuts (2^48) 8603828225 10 Manual.Count131072.C065612.packed 64 cuts65612 = true := by
 decide +kernel
def pointBounds65612 : List (Nat × Nat × Nat) := [(8603834368,115018722789466,115019111830396)]
theorem point_links_checked65612 : (cuts65612.take 1).map (fun c => (8603828225-1+2*2^10*c.k,115018714054544+c.lower,115019103095469+c.upper)) = pointBounds65612 := by
 decide +kernel
def cuts65613 : List PrefixCut := [⟨64,186340807,186340912⟩]
theorem checked65613 : checkPrefixCuts (2^48) 8603959297 10 Manual.Count131072.C065613.packed 64 cuts65613 = true := by
 decide +kernel
def cuts65614 : List PrefixCut := [⟨7,20511712,20511723⟩,
⟨64,189151363,189151466⟩]
theorem checked65614 : checkPrefixCuts (2^48) 8604090369 10 Manual.Count131072.C065614.packed 64 cuts65614 = true := by
 decide +kernel
def pointBounds65614 : List (Nat × Nat × Nat) := [(8604104704,115019108166734,115019497207882)]
theorem point_links_checked65614 : (cuts65614.take 1).map (fun c => (8604090369-1+2*2^10*c.k,115019087655022+c.lower,115019476696159+c.upper)) = pointBounds65614 := by
 decide +kernel
def cuts65615 : List PrefixCut := [⟨64,189606477,189606590⟩]
theorem checked65615 : checkPrefixCuts (2^48) 8604221441 10 Manual.Count131072.C065615.packed 64 cuts65615 = true := by
 decide +kernel
def cuts65616 : List PrefixCut := [⟨11,34086987,34087006⟩,
⟨64,190552263,190552373⟩]
theorem checked65616 : checkPrefixCuts (2^48) 8604352513 10 Manual.Count131072.C065616.packed 64 cuts65616 = true := by
 decide +kernel
def pointBounds65616 : List (Nat × Nat × Nat) := [(8604375040,115019500499849,115019889541221)]
theorem point_links_checked65616 : (cuts65616.take 1).map (fun c => (8604352513-1+2*2^10*c.k,115019466412862+c.lower,115019855454215+c.upper)) = pointBounds65616 := by
 decide +kernel
def cuts65617 : List PrefixCut := [⟨64,185511639,185511749⟩]
theorem checked65617 : checkPrefixCuts (2^48) 8604483585 10 Manual.Count131072.C065617.packed 64 cuts65617 = true := by
 decide +kernel
def cuts65618 : List PrefixCut := [⟨15,45960397,45960423⟩,
⟨64,189466968,189467076⟩]
theorem checked65618 : checkPrefixCuts (2^48) 8604614657 10 Manual.Count131072.C065618.packed 64 cuts65618 = true := by
 decide +kernel
def pointBounds65618 : List (Nat × Nat × Nat) := [(8604645376,115019888437161,115020277478760)]
theorem point_links_checked65618 : (cuts65618.take 1).map (fun c => (8604614657-1+2*2^10*c.k,115019842476764+c.lower,115020231518337+c.upper)) = pointBounds65618 := by
 decide +kernel
def cuts65619 : List PrefixCut := [⟨64,185996665,185996772⟩]
theorem checked65619 : checkPrefixCuts (2^48) 8604745729 10 Manual.Count131072.C065619.packed 64 cuts65619 = true := by
 decide +kernel
def cuts65620 : List PrefixCut := [⟨19,54300285,54300317⟩,
⟨64,185601301,185601415⟩]
theorem checked65620 : checkPrefixCuts (2^48) 8604876801 10 Manual.Count131072.C065620.packed 64 cuts65620 = true := by
 decide +kernel
def pointBounds65620 : List (Nat × Nat × Nat) := [(8604915712,115020272240682,115020661282502)]
theorem point_links_checked65620 : (cuts65620.take 1).map (fun c => (8604876801-1+2*2^10*c.k,115020217940397+c.lower,115020606982185+c.upper)) = pointBounds65620 := by
 decide +kernel
def cuts65621 : List PrefixCut := [⟨64,189131196,189131305⟩]
theorem checked65621 : checkPrefixCuts (2^48) 8605007873 10 Manual.Count131072.C065621.packed 64 cuts65621 = true := by
 decide +kernel
def cuts65622 : List PrefixCut := [⟨23,66826540,66826577⟩,
⟨64,187950760,187950865⟩]
theorem checked65622 : checkPrefixCuts (2^48) 8605138945 10 Manual.Count131072.C065622.packed 64 cuts65622 = true := by
 decide +kernel
def pointBounds65622 : List (Nat × Nat × Nat) := [(8605186048,115020659499434,115021048541482)]
theorem point_links_checked65622 : (cuts65622.take 1).map (fun c => (8605138945-1+2*2^10*c.k,115020592672894+c.lower,115020981714905+c.upper)) = pointBounds65622 := by
 decide +kernel
def cuts65623 : List PrefixCut := [⟨64,184840523,184840628⟩]
theorem checked65623 : checkPrefixCuts (2^48) 8605270017 10 Manual.Count131072.C065623.packed 64 cuts65623 = true := by
 decide +kernel
def cuts65624 : List PrefixCut := [⟨27,79024925,79024969⟩,
⟨64,190463612,190463717⟩]
theorem checked65624 : checkPrefixCuts (2^48) 8605401089 10 Manual.Count131072.C065624.packed 64 cuts65624 = true := by
 decide +kernel
def pointBounds65624 : List (Nat × Nat × Nat) := [(8605456384,115021044489102,115021433531367)]
theorem point_links_checked65624 : (cuts65624.take 1).map (fun c => (8605401089-1+2*2^10*c.k,115020965464177+c.lower,115021354506398+c.upper)) = pointBounds65624 := by
 decide +kernel
def cuts65625 : List PrefixCut := [⟨64,185619886,185619998⟩]
theorem checked65625 : checkPrefixCuts (2^48) 8605532161 10 Manual.Count131072.C065625.packed 64 cuts65625 = true := by
 decide +kernel
def cuts65626 : List PrefixCut := [⟨31,89619866,89619917⟩,
⟨64,186402044,186402146⟩]
theorem checked65626 : checkPrefixCuts (2^48) 8605663233 10 Manual.Count131072.C065626.packed 64 cuts65626 = true := by
 decide +kernel
def pointBounds65626 : List (Nat × Nat × Nat) := [(8605726720,115021431167541,115021820210030)]
theorem point_links_checked65626 : (cuts65626.take 1).map (fun c => (8605663233-1+2*2^10*c.k,115021341547675+c.lower,115021730590113+c.upper)) = pointBounds65626 := by
 decide +kernel
def cuts65627 : List PrefixCut := [⟨64,188263521,188263630⟩]
theorem checked65627 : checkPrefixCuts (2^48) 8605794305 10 Manual.Count131072.C065627.packed 64 cuts65627 = true := by
 decide +kernel
def cuts65628 : List PrefixCut := [⟨35,102994241,102994302⟩,
⟨64,188391476,188391589⟩]
theorem checked65628 : checkPrefixCuts (2^48) 8605925377 10 Manual.Count131072.C065628.packed 64 cuts65628 = true := by
 decide +kernel
def pointBounds65628 : List (Nat × Nat × Nat) := [(8605997056,115021819207481,115022208250191)]
theorem point_links_checked65628 : (cuts65628.take 1).map (fun c => (8605925377-1+2*2^10*c.k,115021716213240+c.lower,115022105255889+c.upper)) = pointBounds65628 := by
 decide +kernel
def cuts65629 : List PrefixCut := [⟨64,188944616,188944728⟩]
theorem checked65629 : checkPrefixCuts (2^48) 8606056449 10 Manual.Count131072.C065629.packed 64 cuts65629 = true := by
 decide +kernel
def cuts65630 : List PrefixCut := [⟨39,113162602,113162665⟩,
⟨64,186129035,186129140⟩]
theorem checked65630 : checkPrefixCuts (2^48) 8606187521 10 Manual.Count131072.C065630.packed 64 cuts65630 = true := by
 decide +kernel
def pointBounds65630 : List (Nat × Nat × Nat) := [(8606267392,115022206711934,115022595754871)]
theorem point_links_checked65630 : (cuts65630.take 1).map (fun c => (8606187521-1+2*2^10*c.k,115022093549332+c.lower,115022482592206+c.upper)) = pointBounds65630 := by
 decide +kernel
def cuts65631 : List PrefixCut := [⟨64,184948812,184948920⟩]
theorem checked65631 : checkPrefixCuts (2^48) 8606318593 10 Manual.Count131072.C065631.packed 64 cuts65631 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000175
