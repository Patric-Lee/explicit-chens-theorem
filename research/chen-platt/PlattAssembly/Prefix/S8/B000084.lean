import PlattAssemblyKernel
import PlattCertificates.Count131072.C072688
import PlattCertificates.Count131072.C072689
import PlattCertificates.Count131072.C072690
import PlattCertificates.Count131072.C072691
import PlattCertificates.Count131072.C072692
import PlattCertificates.Count131072.C072693
import PlattCertificates.Count131072.C072694
import PlattCertificates.Count131072.C072695
import PlattCertificates.Count131072.C072696
import PlattCertificates.Count131072.C072697
import PlattCertificates.Count131072.C072698
import PlattCertificates.Count131072.C072699
import PlattCertificates.Count131072.C072700
import PlattCertificates.Count131072.C072701
import PlattCertificates.Count131072.C072702
import PlattCertificates.Count131072.C072703
import PlattCertificates.Count131072.C072704
import PlattCertificates.Count131072.C072705
import PlattCertificates.Count131072.C072706
import PlattCertificates.Count131072.C072707
import PlattCertificates.Count131072.C072708
import PlattCertificates.Count131072.C072709
import PlattCertificates.Count131072.C072710
import PlattCertificates.Count131072.C072711
import PlattCertificates.Count131072.C072712
import PlattCertificates.Count131072.C072713
import PlattCertificates.Count131072.C072714
import PlattCertificates.Count131072.C072715
import PlattCertificates.Count131072.C072716
import PlattCertificates.Count131072.C072717
import PlattCertificates.Count131072.C072718
import PlattCertificates.Count131072.C072719
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000084
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72688 : List PrefixCut := [⟨64,168772269,168772364⟩]
theorem checked72688 : checkPrefixCuts (2^48) 9531293697 10 Manual.Count131072.C072688.packed 64 cuts72688 = true := by
 decide +kernel
def cuts72689 : List PrefixCut := [⟨58,155215301,155215396⟩,
⟨64,171014313,171014417⟩]
theorem checked72689 : checkPrefixCuts (2^48) 9531424769 10 Manual.Count131072.C072689.packed 64 cuts72689 = true := by
 decide +kernel
def pointBounds72689 : List (Nat × Nat × Nat) := [(9531543552,116275849580125,116276239358728)]
theorem point_links_checked72689 : (cuts72689.take 1).map (fun c => (9531424769-1+2*2^10*c.k,116275694364824+c.lower,116276084143332+c.upper)) = pointBounds72689 := by
 decide +kernel
def cuts72690 : List PrefixCut := [⟨64,171071012,171071111⟩]
theorem checked72690 : checkPrefixCuts (2^48) 9531555841 10 Manual.Count131072.C072690.packed 64 cuts72690 = true := by
 decide +kernel
def cuts72691 : List PrefixCut := [⟨64,168529062,168529163⟩]
theorem checked72691 : checkPrefixCuts (2^48) 9531686913 10 Manual.Count131072.C072691.packed 64 cuts72691 = true := by
 decide +kernel
def cuts72692 : List PrefixCut := [⟨12,31360855,31360872⟩,
⟨64,166754947,166755045⟩]
theorem checked72692 : checkPrefixCuts (2^48) 9531817985 10 Manual.Count131072.C072692.packed 64 cuts72692 = true := by
 decide +kernel
def pointBounds72692 : List (Nat × Nat × Nat) := [(9531842560,116276236340066,116276626118895)]
theorem point_links_checked72692 : (cuts72692.take 1).map (fun c => (9531817985-1+2*2^10*c.k,116276204979211+c.lower,116276594758023+c.upper)) = pointBounds72692 := by
 decide +kernel
def cuts72693 : List PrefixCut := [⟨64,170857253,170857355⟩]
theorem checked72693 : checkPrefixCuts (2^48) 9531949057 10 Manual.Count131072.C072693.packed 64 cuts72693 = true := by
 decide +kernel
def cuts72694 : List PrefixCut := [⟨30,79433352,79433394⟩,
⟨64,168905987,168906080⟩]
theorem checked72694 : checkPrefixCuts (2^48) 9532080129 10 Manual.Count131072.C072694.packed 64 cuts72694 = true := by
 decide +kernel
def pointBounds72694 : List (Nat × Nat × Nat) := [(9532141568,116276622024763,116277011803817)]
theorem point_links_checked72694 : (cuts72694.take 1).map (fun c => (9532080129-1+2*2^10*c.k,116276542591411+c.lower,116276932370423+c.upper)) = pointBounds72694 := by
 decide +kernel
def cuts72695 : List PrefixCut := [⟨64,170084793,170084899⟩]
theorem checked72695 : checkPrefixCuts (2^48) 9532211201 10 Manual.Count131072.C072695.packed 64 cuts72695 = true := by
 decide +kernel
def cuts72696 : List PrefixCut := [⟨48,125642733,125642809⟩,
⟨64,167985961,167986062⟩]
theorem checked72696 : checkPrefixCuts (2^48) 9532342273 10 Manual.Count131072.C072696.packed 64 cuts72696 = true := by
 decide +kernel
def pointBounds72696 : List (Nat × Nat × Nat) := [(9532440576,116277007224924,116277397004211)]
theorem point_links_checked72696 : (cuts72696.take 1).map (fun c => (9532342273-1+2*2^10*c.k,116276881582191+c.lower,116277271361402+c.upper)) = pointBounds72696 := by
 decide +kernel
def cuts72697 : List PrefixCut := [⟨64,166950178,166950280⟩]
theorem checked72697 : checkPrefixCuts (2^48) 9532473345 10 Manual.Count131072.C072697.packed 64 cuts72697 = true := by
 decide +kernel
def cuts72698 : List PrefixCut := [⟨64,169428179,169428275⟩]
theorem checked72698 : checkPrefixCuts (2^48) 9532604417 10 Manual.Count131072.C072698.packed 64 cuts72698 = true := by
 decide +kernel
def cuts72699 : List PrefixCut := [⟨2,5462529,5462532⟩,
⟨64,168244770,168244871⟩]
theorem checked72699 : checkPrefixCuts (2^48) 9532735489 10 Manual.Count131072.C072699.packed 64 cuts72699 = true := by
 decide +kernel
def pointBounds72699 : List (Nat × Nat × Nat) := [(9532739584,116277391409038,116277781188551)]
theorem point_links_checked72699 : (cuts72699.take 1).map (fun c => (9532735489-1+2*2^10*c.k,116277385946509+c.lower,116277775726019+c.upper)) = pointBounds72699 := by
 decide +kernel
def cuts72700 : List PrefixCut := [⟨64,165378377,165378477⟩]
theorem checked72700 : checkPrefixCuts (2^48) 9532866561 10 Manual.Count131072.C072700.packed 64 cuts72700 = true := by
 decide +kernel
def cuts72701 : List PrefixCut := [⟨20,51316736,51316764⟩,
⟨64,166114265,166114362⟩]
theorem checked72701 : checkPrefixCuts (2^48) 9532997633 10 Manual.Count131072.C072701.packed 64 cuts72701 = true := by
 decide +kernel
def pointBounds72701 : List (Nat × Nat × Nat) := [(9533038592,116277770886392,116278160666131)]
theorem point_links_checked72701 : (cuts72701.take 1).map (fun c => (9532997633-1+2*2^10*c.k,116277719569656+c.lower,116278109349367+c.upper)) = pointBounds72701 := by
 decide +kernel
def cuts72702 : List PrefixCut := [⟨64,167765424,167765524⟩]
theorem checked72702 : checkPrefixCuts (2^48) 9533128705 10 Manual.Count131072.C072702.packed 64 cuts72702 = true := by
 decide +kernel
def cuts72703 : List PrefixCut := [⟨38,98969292,98969356⟩,
⟨64,168826012,168826117⟩]
theorem checked72703 : checkPrefixCuts (2^48) 9533259777 10 Manual.Count131072.C072703.packed 64 cuts72703 = true := by
 decide +kernel
def pointBounds72703 : List (Nat × Nat × Nat) := [(9533337600,116278152418637,116278542198609)]
theorem point_links_checked72703 : (cuts72703.take 1).map (fun c => (9533259777-1+2*2^10*c.k,116278053449345+c.lower,116278443229253+c.upper)) = pointBounds72703 := by
 decide +kernel
def cuts72704 : List PrefixCut := [⟨64,170329490,170329587⟩]
theorem checked72704 : checkPrefixCuts (2^48) 9533390849 10 Manual.Count131072.C072704.packed 64 cuts72704 = true := by
 decide +kernel
def cuts72705 : List PrefixCut := [⟨56,144818058,144818141⟩,
⟨64,166725143,166725239⟩]
theorem checked72705 : checkPrefixCuts (2^48) 9533521921 10 Manual.Count131072.C072705.packed 64 cuts72705 = true := by
 decide +kernel
def pointBounds72705 : List (Nat × Nat × Nat) := [(9533636608,116278537422905,116278927203098)]
theorem point_links_checked72705 : (cuts72705.take 1).map (fun c => (9533521921-1+2*2^10*c.k,116278392604847+c.lower,116278782384957+c.upper)) = pointBounds72705 := by
 decide +kernel
def cuts72706 : List PrefixCut := [⟨64,168700965,168701066⟩]
theorem checked72706 : checkPrefixCuts (2^48) 9533652993 10 Manual.Count131072.C072706.packed 64 cuts72706 = true := by
 decide +kernel
def cuts72707 : List PrefixCut := [⟨64,169082454,169082549⟩]
theorem checked72707 : checkPrefixCuts (2^48) 9533784065 10 Manual.Count131072.C072707.packed 64 cuts72707 = true := by
 decide +kernel
def cuts72708 : List PrefixCut := [⟨10,26777818,26777835⟩,
⟨64,167249694,167249792⟩]
theorem checked72708 : checkPrefixCuts (2^48) 9533915137 10 Manual.Count131072.C072708.packed 64 cuts72708 = true := by
 decide +kernel
def pointBounds72708 : List (Nat × Nat × Nat) := [(9533935616,116278923891227,116279313671646)]
theorem point_links_checked72708 : (cuts72708.take 1).map (fun c => (9533915137-1+2*2^10*c.k,116278897113409+c.lower,116279286893811+c.upper)) = pointBounds72708 := by
 decide +kernel
def cuts72709 : List PrefixCut := [⟨64,167394992,167395097⟩]
theorem checked72709 : checkPrefixCuts (2^48) 9534046209 10 Manual.Count131072.C072709.packed 64 cuts72709 = true := by
 decide +kernel
def cuts72710 : List PrefixCut := [⟨28,74013253,74013292⟩,
⟨64,168396471,168396563⟩]
theorem checked72710 : checkPrefixCuts (2^48) 9534177281 10 Manual.Count131072.C072710.packed 64 cuts72710 = true := by
 decide +kernel
def pointBounds72710 : List (Nat × Nat × Nat) := [(9534234624,116279305771348,116279695551992)]
theorem point_links_checked72710 : (cuts72710.take 1).map (fun c => (9534177281-1+2*2^10*c.k,116279231758095+c.lower,116279621538700+c.upper)) = pointBounds72710 := by
 decide +kernel
def cuts72711 : List PrefixCut := [⟨64,167656102,167656201⟩]
theorem checked72711 : checkPrefixCuts (2^48) 9534308353 10 Manual.Count131072.C072711.packed 64 cuts72711 = true := by
 decide +kernel
def cuts72712 : List PrefixCut := [⟨46,120566901,120566974⟩,
⟨64,168716574,168716674⟩]
theorem checked72712 : checkPrefixCuts (2^48) 9534439425 10 Manual.Count131072.C072712.packed 64 cuts72712 = true := by
 decide +kernel
def pointBounds72712 : List (Nat × Nat × Nat) := [(9534533632,116279688377569,116280078158438)]
theorem point_links_checked72712 : (cuts72712.take 1).map (fun c => (9534439425-1+2*2^10*c.k,116279567810668+c.lower,116279957591464+c.upper)) = pointBounds72712 := by
 decide +kernel
def cuts72713 : List PrefixCut := [⟨64,169895092,169895201⟩]
theorem checked72713 : checkPrefixCuts (2^48) 9534570497 10 Manual.Count131072.C072713.packed 64 cuts72713 = true := by
 decide +kernel
def cuts72714 : List PrefixCut := [⟨64,169627071,169627174⟩]
theorem checked72714 : checkPrefixCuts (2^48) 9534701569 10 Manual.Count131072.C072714.packed 64 cuts72714 = true := by
 decide +kernel
def pointBounds72714 : List (Nat × Nat × Nat) := [(9534832640,116280076049405,116280465830513)]
theorem point_links_checked72714 : (cuts72714.take 1).map (fun c => (9534701569-1+2*2^10*c.k,116279906422334+c.lower,116280296203339+c.upper)) = pointBounds72714 := by
 decide +kernel
def cuts72715 : List PrefixCut := [⟨64,166436545,166436641⟩]
theorem checked72715 : checkPrefixCuts (2^48) 9534832641 10 Manual.Count131072.C072715.packed 64 cuts72715 = true := by
 decide +kernel
def cuts72716 : List PrefixCut := [⟨64,168382580,168382679⟩]
theorem checked72716 : checkPrefixCuts (2^48) 9534963713 10 Manual.Count131072.C072716.packed 64 cuts72716 = true := by
 decide +kernel
def cuts72717 : List PrefixCut := [⟨18,46405166,46405196⟩,
⟨64,168557369,168557471⟩]
theorem checked72717 : checkPrefixCuts (2^48) 9535094785 10 Manual.Count131072.C072717.packed 64 cuts72717 = true := by
 decide +kernel
def pointBounds72717 : List (Nat × Nat × Nat) := [(9535131648,116280457273696,116280847055029)]
theorem point_links_checked72717 : (cuts72717.take 1).map (fun c => (9535094785-1+2*2^10*c.k,116280410868530+c.lower,116280800649833+c.upper)) = pointBounds72717 := by
 decide +kernel
def cuts72718 : List PrefixCut := [⟨64,167197180,167197278⟩]
theorem checked72718 : checkPrefixCuts (2^48) 9535225857 10 Manual.Count131072.C072718.packed 64 cuts72718 = true := by
 decide +kernel
def cuts72719 : List PrefixCut := [⟨36,95552868,95552928⟩,
⟨64,170117244,170117350⟩]
theorem checked72719 : checkPrefixCuts (2^48) 9535356929 10 Manual.Count131072.C072719.packed 64 cuts72719 = true := by
 decide +kernel
def pointBounds72719 : List (Nat × Nat × Nat) := [(9535430656,116280842175947,116281231957510)]
theorem point_links_checked72719 : (cuts72719.take 1).map (fun c => (9535356929-1+2*2^10*c.k,116280746623079+c.lower,116281136404582+c.upper)) = pointBounds72719 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000084
