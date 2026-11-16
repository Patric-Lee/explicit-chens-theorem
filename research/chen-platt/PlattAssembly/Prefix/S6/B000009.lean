import PlattAssemblyKernel
import PlattCertificates.Count131072.C050288
import PlattCertificates.Count131072.C050289
import PlattCertificates.Count131072.C050290
import PlattCertificates.Count131072.C050291
import PlattCertificates.Count131072.C050292
import PlattCertificates.Count131072.C050293
import PlattCertificates.Count131072.C050294
import PlattCertificates.Count131072.C050295
import PlattCertificates.Count131072.C050296
import PlattCertificates.Count131072.C050297
import PlattCertificates.Count131072.C050298
import PlattCertificates.Count131072.C050299
import PlattCertificates.Count131072.C050300
import PlattCertificates.Count131072.C050301
import PlattCertificates.Count131072.C050302
import PlattCertificates.Count131072.C050303
import PlattCertificates.Count131072.C050304
import PlattCertificates.Count131072.C050305
import PlattCertificates.Count131072.C050306
import PlattCertificates.Count131072.C050307
import PlattCertificates.Count131072.C050308
import PlattCertificates.Count131072.C050309
import PlattCertificates.Count131072.C050310
import PlattCertificates.Count131072.C050311
import PlattCertificates.Count131072.C050312
import PlattCertificates.Count131072.C050313
import PlattCertificates.Count131072.C050314
import PlattCertificates.Count131072.C050315
import PlattCertificates.Count131072.C050316
import PlattCertificates.Count131072.C050317
import PlattCertificates.Count131072.C050318
import PlattCertificates.Count131072.C050319
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50288 : List PrefixCut := [⟨63,242452613,242452750⟩,
⟨64,245866804,245866943⟩]
theorem checked50288 : checkPrefixCuts (2^48) 6595280897 10 Manual.Count131072.C050288.packed 64 cuts50288 = true := by
 decide +kernel
def pointBounds50288 : List (Nat × Nat × Nat) := [(6595409920,111728568494770,111728955657636)]
theorem point_links_checked50288 : (cuts50288.take 1).map (fun c => (6595280897-1+2*2^10*c.k,111728326042157+c.lower,111728713204886+c.upper)) = pointBounds50288 := by
 decide +kernel
def cuts50289 : List PrefixCut := [⟨64,247398306,247398451⟩]
theorem checked50289 : checkPrefixCuts (2^48) 6595411969 10 Manual.Count131072.C050289.packed 64 cuts50289 = true := by
 decide +kernel
def cuts50290 : List PrefixCut := [⟨36,139892883,139892960⟩,
⟨64,248033536,248033674⟩]
theorem checked50290 : checkPrefixCuts (2^48) 6595543041 10 Manual.Count131072.C050290.packed 64 cuts50290 = true := by
 decide +kernel
def pointBounds50290 : List (Nat × Nat × Nat) := [(6595616768,111728959200150,111729346363240)]
theorem point_links_checked50290 : (cuts50290.take 1).map (fun c => (6595543041-1+2*2^10*c.k,111728819307267+c.lower,111729206470280+c.upper)) = pointBounds50290 := by
 decide +kernel
def cuts50291 : List PrefixCut := [⟨64,248028625,248028764⟩]
theorem checked50291 : checkPrefixCuts (2^48) 6595674113 10 Manual.Count131072.C050291.packed 64 cuts50291 = true := by
 decide +kernel
def cuts50292 : List PrefixCut := [⟨9,34694592,34694611⟩,
⟨64,248365069,248365207⟩]
theorem checked50292 : checkPrefixCuts (2^48) 6595805185 10 Manual.Count131072.C050292.packed 64 cuts50292 = true := by
 decide +kernel
def pointBounds50292 : List (Nat × Nat × Nat) := [(6595823616,111729350064020,111729737227329)]
theorem point_links_checked50292 : (cuts50292.take 1).map (fun c => (6595805185-1+2*2^10*c.k,111729315369428+c.lower,111729702532718+c.upper)) = pointBounds50292 := by
 decide +kernel
def cuts50293 : List PrefixCut := [⟨46,177138456,177138554⟩,
⟨64,247805375,247805513⟩]
theorem checked50293 : checkPrefixCuts (2^48) 6595936257 10 Manual.Count131072.C050293.packed 64 cuts50293 = true := by
 decide +kernel
def pointBounds50293 : List (Nat × Nat × Nat) := [(6596030464,111729740872953,111730128036479)]
theorem point_links_checked50293 : (cuts50293.take 1).map (fun c => (6595936257-1+2*2^10*c.k,111729563734497+c.lower,111729950897925+c.upper)) = pointBounds50293 := by
 decide +kernel
def cuts50294 : List PrefixCut := [⟨64,248483220,248483358⟩]
theorem checked50294 : checkPrefixCuts (2^48) 6596067329 10 Manual.Count131072.C050294.packed 64 cuts50294 = true := by
 decide +kernel
def cuts50295 : List PrefixCut := [⟨19,74548270,74548315⟩,
⟨64,250953248,250953391⟩]
theorem checked50295 : checkPrefixCuts (2^48) 6596198401 10 Manual.Count131072.C050295.packed 64 cuts50295 = true := by
 decide +kernel
def pointBounds50295 : List (Nat × Nat × Nat) := [(6596237312,111730134571362,111730521735111)]
theorem point_links_checked50295 : (cuts50295.take 1).map (fun c => (6596198401-1+2*2^10*c.k,111730060023092+c.lower,111730447186796+c.upper)) = pointBounds50295 := by
 decide +kernel
def cuts50296 : List PrefixCut := [⟨56,218731924,218732047⟩,
⟨64,250393546,250393686⟩]
theorem checked50296 : checkPrefixCuts (2^48) 6596329473 10 Manual.Count131072.C050296.packed 64 cuts50296 = true := by
 decide +kernel
def pointBounds50296 : List (Nat × Nat × Nat) := [(6596444160,111730529708264,111730916872234)]
theorem point_links_checked50296 : (cuts50296.take 1).map (fun c => (6596329473-1+2*2^10*c.k,111730310976340+c.lower,111730698140187+c.upper)) = pointBounds50296 := by
 decide +kernel
def cuts50297 : List PrefixCut := [⟨64,246462905,246463050⟩]
theorem checked50297 : checkPrefixCuts (2^48) 6596460545 10 Manual.Count131072.C050297.packed 64 cuts50297 = true := by
 decide +kernel
def cuts50298 : List PrefixCut := [⟨29,112647621,112647682⟩,
⟨64,247354073,247354210⟩]
theorem checked50298 : checkPrefixCuts (2^48) 6596591617 10 Manual.Count131072.C050298.packed 64 cuts50298 = true := by
 decide +kernel
def pointBounds50298 : List (Nat × Nat × Nat) := [(6596651008,111730920480412,111731307644605)]
theorem point_links_checked50298 : (cuts50298.take 1).map (fun c => (6596591617-1+2*2^10*c.k,111730807832791+c.lower,111731194996923+c.upper)) = pointBounds50298 := by
 decide +kernel
def cuts50299 : List PrefixCut := [⟨64,248074513,248074654⟩]
theorem checked50299 : checkPrefixCuts (2^48) 6596722689 10 Manual.Count131072.C050299.packed 64 cuts50299 = true := by
 decide +kernel
def cuts50300 : List PrefixCut := [⟨2,8277600,8277604⟩,
⟨64,248240259,248240395⟩]
theorem checked50300 : checkPrefixCuts (2^48) 6596853761 10 Manual.Count131072.C050300.packed 64 cuts50300 = true := by
 decide +kernel
def pointBounds50300 : List (Nat × Nat × Nat) := [(6596857856,111731311538977,111731698703391)]
theorem point_links_checked50300 : (cuts50300.take 1).map (fun c => (6596853761-1+2*2^10*c.k,111731303261377+c.lower,111731690425787+c.upper)) = pointBounds50300 := by
 decide +kernel
def cuts50301 : List PrefixCut := [⟨39,150870328,150870413⟩,
⟨64,247510002,247510141⟩]
theorem checked50301 : checkPrefixCuts (2^48) 6596984833 10 Manual.Count131072.C050301.packed 64 cuts50301 = true := by
 decide +kernel
def pointBounds50301 : List (Nat × Nat × Nat) := [(6597064704,111731702371964,111732089536595)]
theorem point_links_checked50301 : (cuts50301.take 1).map (fun c => (6596984833-1+2*2^10*c.k,111731551501636+c.lower,111731938666182+c.upper)) = pointBounds50301 := by
 decide +kernel
def cuts50302 : List PrefixCut := [⟨64,248273048,248273188⟩]
theorem checked50302 : checkPrefixCuts (2^48) 6597115905 10 Manual.Count131072.C050302.packed 64 cuts50302 = true := by
 decide +kernel
def cuts50303 : List PrefixCut := [⟨12,48211933,48211962⟩,
⟨64,250230732,250230873⟩]
theorem checked50303 : checkPrefixCuts (2^48) 6597246977 10 Manual.Count131072.C050303.packed 64 cuts50303 = true := by
 decide +kernel
def pointBounds50303 : List (Nat × Nat × Nat) := [(6597271552,111732095496619,111732482661473)]
theorem point_links_checked50303 : (cuts50303.take 1).map (fun c => (6597246977-1+2*2^10*c.k,111732047284686+c.lower,111732434449511+c.upper)) = pointBounds50303 := by
 decide +kernel
def cuts50304 : List PrefixCut := [⟨49,190197617,190197724⟩,
⟨64,248433855,248433997⟩]
theorem checked50304 : checkPrefixCuts (2^48) 6597378049 10 Manual.Count131072.C050304.packed 64 cuts50304 = true := by
 decide +kernel
def pointBounds50304 : List (Nat × Nat × Nat) := [(6597478400,111732487713035,111732874878108)]
theorem point_links_checked50304 : (cuts50304.take 1).map (fun c => (6597378049-1+2*2^10*c.k,111732297515418+c.lower,111732684680384+c.upper)) = pointBounds50304 := by
 decide +kernel
def cuts50305 : List PrefixCut := [⟨64,247021035,247021176⟩]
theorem checked50305 : checkPrefixCuts (2^48) 6597509121 10 Manual.Count131072.C050305.packed 64 cuts50305 = true := by
 decide +kernel
def cuts50306 : List PrefixCut := [⟨22,85496292,85496341⟩,
⟨64,248765283,248765426⟩]
theorem checked50306 : checkPrefixCuts (2^48) 6597640193 10 Manual.Count131072.C050306.packed 64 cuts50306 = true := by
 decide +kernel
def pointBounds50306 : List (Nat × Nat × Nat) := [(6597685248,111732878466600,111733265631898)]
theorem point_links_checked50306 : (cuts50306.take 1).map (fun c => (6597640193-1+2*2^10*c.k,111732792970308+c.lower,111733180135557+c.upper)) = pointBounds50306 := by
 decide +kernel
def cuts50307 : List PrefixCut := [⟨59,228624202,228624330⟩,
⟨64,247608482,247608622⟩]
theorem checked50307 : checkPrefixCuts (2^48) 6597771265 10 Manual.Count131072.C050307.packed 64 cuts50307 = true := by
 decide +kernel
def pointBounds50307 : List (Nat × Nat × Nat) := [(6597892096,111733270359793,111733657525313)]
theorem point_links_checked50307 : (cuts50307.take 1).map (fun c => (6597771265-1+2*2^10*c.k,111733041735591+c.lower,111733428900983+c.upper)) = pointBounds50307 := by
 decide +kernel
def cuts50308 : List PrefixCut := [⟨64,246579690,246579835⟩]
theorem checked50308 : checkPrefixCuts (2^48) 6597902337 10 Manual.Count131072.C050308.packed 64 cuts50308 = true := by
 decide +kernel
def cuts50309 : List PrefixCut := [⟨32,125762300,125762372⟩,
⟨64,247129379,247129522⟩]
theorem checked50309 : checkPrefixCuts (2^48) 6598033409 10 Manual.Count131072.C050309.packed 64 cuts50309 = true := by
 decide +kernel
def pointBounds50309 : List (Nat × Nat × Nat) := [(6598098944,111733661686063,111734048851812)]
theorem point_links_checked50309 : (cuts50309.take 1).map (fun c => (6598033409-1+2*2^10*c.k,111733535923763+c.lower,111733923089440+c.upper)) = pointBounds50309 := by
 decide +kernel
def cuts50310 : List PrefixCut := [⟨64,249300086,249300226⟩]
theorem checked50310 : checkPrefixCuts (2^48) 6598164481 10 Manual.Count131072.C050310.packed 64 cuts50310 = true := by
 decide +kernel
def cuts50311 : List PrefixCut := [⟨5,18983120,18983130⟩,
⟨64,247844760,247844899⟩]
theorem checked50311 : checkPrefixCuts (2^48) 6598295553 10 Manual.Count131072.C050311.packed 64 cuts50311 = true := by
 decide +kernel
def pointBounds50311 : List (Nat × Nat × Nat) := [(6598305792,111734051336348,111734438502318)]
theorem point_links_checked50311 : (cuts50311.take 1).map (fun c => (6598295553-1+2*2^10*c.k,111734032353228+c.lower,111734419519188+c.upper)) = pointBounds50311 := by
 decide +kernel
def cuts50312 : List PrefixCut := [⟨42,163506594,163506689⟩,
⟨64,249119551,249119694⟩]
theorem checked50312 : checkPrefixCuts (2^48) 6598426625 10 Manual.Count131072.C050312.packed 64 cuts50312 = true := by
 decide +kernel
def pointBounds50312 : List (Nat × Nat × Nat) := [(6598512640,111734443704582,111734830870776)]
theorem point_links_checked50312 : (cuts50312.take 1).map (fun c => (6598426625-1+2*2^10*c.k,111734280197988+c.lower,111734667364087+c.upper)) = pointBounds50312 := by
 decide +kernel
def cuts50313 : List PrefixCut := [⟨64,250138373,250138517⟩]
theorem checked50313 : checkPrefixCuts (2^48) 6598557697 10 Manual.Count131072.C050313.packed 64 cuts50313 = true := by
 decide +kernel
def cuts50314 : List PrefixCut := [⟨15,57628374,57628405⟩,
⟨64,248725740,248725877⟩]
theorem checked50314 : checkPrefixCuts (2^48) 6598688769 10 Manual.Count131072.C050314.packed 64 cuts50314 = true := by
 decide +kernel
def pointBounds50314 : List (Nat × Nat × Nat) := [(6598719488,111734837084286,111735224250703)]
theorem point_links_checked50314 : (cuts50314.take 1).map (fun c => (6598688769-1+2*2^10*c.k,111734779455912+c.lower,111735166622298+c.upper)) = pointBounds50314 := by
 decide +kernel
def cuts50315 : List PrefixCut := [⟨52,201928750,201928868⟩,
⟨64,248464888,248465032⟩]
theorem checked50315 : checkPrefixCuts (2^48) 6598819841 10 Manual.Count131072.C050315.packed 64 cuts50315 = true := by
 decide +kernel
def pointBounds50315 : List (Nat × Nat × Nat) := [(6598926336,111735230110402,111735617277043)]
theorem point_links_checked50315 : (cuts50315.take 1).map (fun c => (6598819841-1+2*2^10*c.k,111735028181652+c.lower,111735415348175+c.upper)) = pointBounds50315 := by
 decide +kernel
def cuts50316 : List PrefixCut := [⟨64,245943348,245943493⟩]
theorem checked50316 : checkPrefixCuts (2^48) 6598950913 10 Manual.Count131072.C050316.packed 64 cuts50316 = true := by
 decide +kernel
def cuts50317 : List PrefixCut := [⟨25,96524819,96524875⟩,
⟨64,244872137,244872279⟩]
theorem checked50317 : checkPrefixCuts (2^48) 6599081985 10 Manual.Count131072.C050317.packed 64 cuts50317 = true := by
 decide +kernel
def pointBounds50317 : List (Nat × Nat × Nat) := [(6599133184,111735619114707,111736006281575)]
theorem point_links_checked50317 : (cuts50317.take 1).map (fun c => (6599081985-1+2*2^10*c.k,111735522589888+c.lower,111735909756700+c.upper)) = pointBounds50317 := by
 decide +kernel
def cuts50318 : List PrefixCut := [⟨62,237829686,237829826⟩,
⟨64,246274775,246274919⟩]
theorem checked50318 : checkPrefixCuts (2^48) 6599213057 10 Manual.Count131072.C050318.packed 64 cuts50318 = true := by
 decide +kernel
def pointBounds50318 : List (Nat × Nat × Nat) := [(6599340032,111736005291711,111736392458805)]
theorem point_links_checked50318 : (cuts50318.take 1).map (fun c => (6599213057-1+2*2^10*c.k,111735767462025+c.lower,111736154628979+c.upper)) = pointBounds50318 := by
 decide +kernel
def cuts50319 : List PrefixCut := [⟨64,248402496,248402637⟩]
theorem checked50319 : checkPrefixCuts (2^48) 6599344129 10 Manual.Count131072.C050319.packed 64 cuts50319 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000009
