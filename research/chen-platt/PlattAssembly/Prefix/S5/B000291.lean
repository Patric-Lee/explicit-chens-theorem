import PlattAssemblyKernel
import PlattCertificates.Count131072.C049312
import PlattCertificates.Count131072.C049313
import PlattCertificates.Count131072.C049314
import PlattCertificates.Count131072.C049315
import PlattCertificates.Count131072.C049316
import PlattCertificates.Count131072.C049317
import PlattCertificates.Count131072.C049318
import PlattCertificates.Count131072.C049319
import PlattCertificates.Count131072.C049320
import PlattCertificates.Count131072.C049321
import PlattCertificates.Count131072.C049322
import PlattCertificates.Count131072.C049323
import PlattCertificates.Count131072.C049324
import PlattCertificates.Count131072.C049325
import PlattCertificates.Count131072.C049326
import PlattCertificates.Count131072.C049327
import PlattCertificates.Count131072.C049328
import PlattCertificates.Count131072.C049329
import PlattCertificates.Count131072.C049330
import PlattCertificates.Count131072.C049331
import PlattCertificates.Count131072.C049332
import PlattCertificates.Count131072.C049333
import PlattCertificates.Count131072.C049334
import PlattCertificates.Count131072.C049335
import PlattCertificates.Count131072.C049336
import PlattCertificates.Count131072.C049337
import PlattCertificates.Count131072.C049338
import PlattCertificates.Count131072.C049339
import PlattCertificates.Count131072.C049340
import PlattCertificates.Count131072.C049341
import PlattCertificates.Count131072.C049342
import PlattCertificates.Count131072.C049343
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000291
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49312 : List PrefixCut := [⟨29,113592980,113593040⟩,
⟨64,252558007,252558144⟩]
theorem checked49312 : checkPrefixCuts (2^48) 6467354625 10 Manual.Count131072.C049312.packed 64 cuts49312 = true := by
 decide +kernel
def pointBounds49312 : List (Nat × Nat × Nat) := [(6467414016,111484430355629,111484817379474)]
theorem point_links_checked49312 : (cuts49312.take 1).map (fun c => (6467354625-1+2*2^10*c.k,111484316762649+c.lower,111484703786434+c.upper)) = pointBounds49312 := by
 decide +kernel
def cuts49313 : List PrefixCut := [⟨64,252639944,252640083⟩]
theorem checked49313 : checkPrefixCuts (2^48) 6467485697 10 Manual.Count131072.C049313.packed 64 cuts49313 = true := by
 decide +kernel
def pointBounds49313 : List (Nat × Nat × Nat) := [(6467616768,111484821960600,111485208984661)]
theorem point_links_checked49313 : (cuts49313.take 1).map (fun c => (6467485697-1+2*2^10*c.k,111484569320656+c.lower,111484956344578+c.upper)) = pointBounds49313 := by
 decide +kernel
def cuts49314 : List PrefixCut := [⟨64,251068094,251068240⟩]
theorem checked49314 : checkPrefixCuts (2^48) 6467616769 10 Manual.Count131072.C049314.packed 64 cuts49314 = true := by
 decide +kernel
def cuts49315 : List PrefixCut := [⟨35,136085565,136085640⟩,
⟨64,250366689,250366829⟩]
theorem checked49315 : checkPrefixCuts (2^48) 6467747841 10 Manual.Count131072.C049315.packed 64 cuts49315 = true := by
 decide +kernel
def pointBounds49315 : List (Nat × Nat × Nat) := [(6467819520,111485209114259,111485596138541)]
theorem point_links_checked49315 : (cuts49315.take 1).map (fun c => (6467747841-1+2*2^10*c.k,111485073028694+c.lower,111485460052901+c.upper)) = pointBounds49315 := by
 decide +kernel
def cuts49316 : List PrefixCut := [⟨64,256845878,256846021⟩]
theorem checked49316 : checkPrefixCuts (2^48) 6467878913 10 Manual.Count131072.C049316.packed 64 cuts49316 = true := by
 decide +kernel
def cuts49317 : List PrefixCut := [⟨6,24021916,24021929⟩,
⟨64,252271347,252271482⟩]
theorem checked49317 : checkPrefixCuts (2^48) 6468009985 10 Manual.Count131072.C049317.packed 64 cuts49317 = true := by
 decide +kernel
def pointBounds49317 : List (Nat × Nat × Nat) := [(6468022272,111485604263177,111485991287680)]
theorem point_links_checked49317 : (cuts49317.take 1).map (fun c => (6468009985-1+2*2^10*c.k,111485580241261+c.lower,111485967265751+c.upper)) = pointBounds49317 := by
 decide +kernel
def cuts49318 : List PrefixCut := [⟨41,164537191,164537281⟩,
⟨64,253049545,253049689⟩]
theorem checked49318 : checkPrefixCuts (2^48) 6468141057 10 Manual.Count131072.C049318.packed 64 cuts49318 = true := by
 decide +kernel
def pointBounds49318 : List (Nat × Nat × Nat) := [(6468225024,111485997049799,111486384074514)]
theorem point_links_checked49318 : (cuts49318.take 1).map (fun c => (6468141057-1+2*2^10*c.k,111485832512608+c.lower,111486219537233+c.upper)) = pointBounds49318 := by
 decide +kernel
def cuts49319 : List PrefixCut := [⟨64,254915557,254915702⟩]
theorem checked49319 : checkPrefixCuts (2^48) 6468272129 10 Manual.Count131072.C049319.packed 64 cuts49319 = true := by
 decide +kernel
def cuts49320 : List PrefixCut := [⟨12,45516979,45517005⟩,
⟨64,248992365,248992509⟩]
theorem checked49320 : checkPrefixCuts (2^48) 6468403201 10 Manual.Count131072.C049320.packed 64 cuts49320 = true := by
 decide +kernel
def pointBounds49320 : List (Nat × Nat × Nat) := [(6468427776,111486385994689,111486773019629)]
theorem point_links_checked49320 : (cuts49320.take 1).map (fun c => (6468403201-1+2*2^10*c.k,111486340477710+c.lower,111486727502624+c.upper)) = pointBounds49320 := by
 decide +kernel
def cuts49321 : List PrefixCut := [⟨47,184630559,184630667⟩,
⟨64,251641677,251641822⟩]
theorem checked49321 : checkPrefixCuts (2^48) 6468534273 10 Manual.Count131072.C049321.packed 64 cuts49321 = true := by
 decide +kernel
def pointBounds49321 : List (Nat × Nat × Nat) := [(6468630528,111486774100634,111487161125800)]
theorem point_links_checked49321 : (cuts49321.take 1).map (fun c => (6468534273-1+2*2^10*c.k,111486589470075+c.lower,111486976495133+c.upper)) = pointBounds49321 := by
 decide +kernel
def cuts49322 : List PrefixCut := [⟨64,251114422,251114562⟩]
theorem checked49322 : checkPrefixCuts (2^48) 6468665345 10 Manual.Count131072.C049322.packed 64 cuts49322 = true := by
 decide +kernel
def cuts49323 : List PrefixCut := [⟨18,70882011,70882054⟩,
⟨64,252197145,252197295⟩]
theorem checked49323 : checkPrefixCuts (2^48) 6468796417 10 Manual.Count131072.C049323.packed 64 cuts49323 = true := by
 decide +kernel
def pointBounds49323 : List (Nat × Nat × Nat) := [(6468833280,111487163108185,111487550133571)]
theorem point_links_checked49323 : (cuts49323.take 1).map (fun c => (6468796417-1+2*2^10*c.k,111487092226174+c.lower,111487479251517+c.upper)) = pointBounds49323 := by
 decide +kernel
def cuts49324 : List PrefixCut := [⟨53,208202380,208202501⟩,
⟨64,252888206,252888353⟩]
theorem checked49324 : checkPrefixCuts (2^48) 6468927489 10 Manual.Count131072.C049324.packed 64 cuts49324 = true := by
 decide +kernel
def pointBounds49324 : List (Nat × Nat × Nat) := [(6469036032,111487552625699,111487939651313)]
theorem point_links_checked49324 : (cuts49324.take 1).map (fun c => (6468927489-1+2*2^10*c.k,111487344423319+c.lower,111487731448812+c.upper)) = pointBounds49324 := by
 decide +kernel
def cuts49325 : List PrefixCut := [⟨64,252273941,252274080⟩]
theorem checked49325 : checkPrefixCuts (2^48) 6469058561 10 Manual.Count131072.C049325.packed 64 cuts49325 = true := by
 decide +kernel
def cuts49326 : List PrefixCut := [⟨24,93415767,93415819⟩,
⟨64,251050560,251050699⟩]
theorem checked49326 : checkPrefixCuts (2^48) 6469189633 10 Manual.Count131072.C049326.packed 64 cuts49326 = true := by
 decide +kernel
def pointBounds49326 : List (Nat × Nat × Nat) := [(6469238784,111487943001233,111488330027064)]
theorem point_links_checked49326 : (cuts49326.take 1).map (fun c => (6469189633-1+2*2^10*c.k,111487849585466+c.lower,111488236611245+c.upper)) = pointBounds49326 := by
 decide +kernel
def cuts49327 : List PrefixCut := [⟨59,235208474,235208609⟩,
⟨64,254265128,254265273⟩]
theorem checked49327 : checkPrefixCuts (2^48) 6469320705 10 Manual.Count131072.C049327.packed 64 cuts49327 = true := by
 decide +kernel
def pointBounds49327 : List (Nat × Nat × Nat) := [(6469441536,111488335844500,111488722870553)]
theorem point_links_checked49327 : (cuts49327.take 1).map (fun c => (6469320705-1+2*2^10*c.k,111488100636026+c.lower,111488487661944+c.upper)) = pointBounds49327 := by
 decide +kernel
def cuts49328 : List PrefixCut := [⟨64,249735153,249735297⟩]
theorem checked49328 : checkPrefixCuts (2^48) 6469451777 10 Manual.Count131072.C049328.packed 64 cuts49328 = true := by
 decide +kernel
def cuts49329 : List PrefixCut := [⟨30,117121438,117121499⟩,
⟨64,250774265,250774401⟩]
theorem checked49329 : checkPrefixCuts (2^48) 6469582849 10 Manual.Count131072.C049329.packed 64 cuts49329 = true := by
 decide +kernel
def pointBounds49329 : List (Nat × Nat × Nat) := [(6469644288,111488721757745,111489108784013)]
theorem point_links_checked49329 : (cuts49329.take 1).map (fun c => (6469582849-1+2*2^10*c.k,111488604636307+c.lower,111488991662514+c.upper)) = pointBounds49329 := by
 decide +kernel
def cuts49330 : List PrefixCut := [⟨64,248332837,248332982⟩]
theorem checked49330 : checkPrefixCuts (2^48) 6469713921 10 Manual.Count131072.C049330.packed 64 cuts49330 = true := by
 decide +kernel
def cuts49331 : List PrefixCut := [⟨1,4263554,4263557⟩,
⟨64,253200409,253200555⟩]
theorem checked49331 : checkPrefixCuts (2^48) 6469844993 10 Manual.Count131072.C049331.packed 64 cuts49331 = true := by
 decide +kernel
def pointBounds49331 : List (Nat × Nat × Nat) := [(6469847040,111489108006963,111489495033454)]
theorem point_links_checked49331 : (cuts49331.take 1).map (fun c => (6469844993-1+2*2^10*c.k,111489103743409+c.lower,111489490769897+c.upper)) = pointBounds49331 := by
 decide +kernel
def cuts49332 : List PrefixCut := [⟨36,142868884,142868966⟩,
⟨64,256675590,256675737⟩]
theorem checked49332 : checkPrefixCuts (2^48) 6469976065 10 Manual.Count131072.C049332.packed 64 cuts49332 = true := by
 decide +kernel
def pointBounds49332 : List (Nat × Nat × Nat) := [(6470049792,111489499812702,111489886839418)]
theorem point_links_checked49332 : (cuts49332.take 1).map (fun c => (6469976065-1+2*2^10*c.k,111489356943818+c.lower,111489743970452+c.upper)) = pointBounds49332 := by
 decide +kernel
def cuts49333 : List PrefixCut := [⟨64,247969748,247969888⟩]
theorem checked49333 : checkPrefixCuts (2^48) 6470107137 10 Manual.Count131072.C049333.packed 64 cuts49333 = true := by
 decide +kernel
def cuts49334 : List PrefixCut := [⟨7,27102352,27102366⟩,
⟨64,248269221,248269364⟩]
theorem checked49334 : checkPrefixCuts (2^48) 6470238209 10 Manual.Count131072.C049334.packed 64 cuts49334 = true := by
 decide +kernel
def pointBounds49334 : List (Nat × Nat × Nat) := [(6470252544,111489888691508,111490275718443)]
theorem point_links_checked49334 : (cuts49334.take 1).map (fun c => (6470238209-1+2*2^10*c.k,111489861589156+c.lower,111490248616077+c.upper)) = pointBounds49334 := by
 decide +kernel
def cuts49335 : List PrefixCut := [⟨42,166046548,166046642⟩,
⟨64,251439813,251439956⟩]
theorem checked49335 : checkPrefixCuts (2^48) 6470369281 10 Manual.Count131072.C049335.packed 64 cuts49335 = true := by
 decide +kernel
def pointBounds49335 : List (Nat × Nat × Nat) := [(6470455296,111490275904925,111490662932083)]
theorem point_links_checked49335 : (cuts49335.take 1).map (fun c => (6470369281-1+2*2^10*c.k,111490109858377+c.lower,111490496885441+c.upper)) = pointBounds49335 := by
 decide +kernel
def cuts49336 : List PrefixCut := [⟨64,251521720,251521859⟩]
theorem checked49336 : checkPrefixCuts (2^48) 6470500353 10 Manual.Count131072.C049336.packed 64 cuts49336 = true := by
 decide +kernel
def cuts49337 : List PrefixCut := [⟨13,53331351,53331378⟩,
⟨64,254170138,254170278⟩]
theorem checked49337 : checkPrefixCuts (2^48) 6470631425 10 Manual.Count131072.C049337.packed 64 cuts49337 = true := by
 decide +kernel
def pointBounds49337 : List (Nat × Nat × Nat) := [(6470658048,111490666151261,111491053178634)]
theorem point_links_checked49337 : (cuts49337.take 1).map (fun c => (6470631425-1+2*2^10*c.k,111490612819910+c.lower,111490999847256+c.upper)) = pointBounds49337 := by
 decide +kernel
def cuts49338 : List PrefixCut := [⟨48,187698897,187699007⟩,
⟨64,249510584,249510729⟩]
theorem checked49338 : checkPrefixCuts (2^48) 6470762497 10 Manual.Count131072.C049338.packed 64 cuts49338 = true := by
 decide +kernel
def pointBounds49338 : List (Nat × Nat × Nat) := [(6470860800,111491054688945,111491441716541)]
theorem point_links_checked49338 : (cuts49338.take 1).map (fun c => (6470762497-1+2*2^10*c.k,111490866990048+c.lower,111491254017534+c.upper)) = pointBounds49338 := by
 decide +kernel
def cuts49339 : List PrefixCut := [⟨64,252071924,252072067⟩]
theorem checked49339 : checkPrefixCuts (2^48) 6470893569 10 Manual.Count131072.C049339.packed 64 cuts49339 = true := by
 decide +kernel
def cuts49340 : List PrefixCut := [⟨19,75294351,75294394⟩,
⟨64,251805843,251805989⟩]
theorem checked49340 : checkPrefixCuts (2^48) 6471024641 10 Manual.Count131072.C049340.packed 64 cuts49340 = true := by
 decide +kernel
def pointBounds49340 : List (Nat × Nat × Nat) := [(6471063552,111491443866907,111491830894724)]
theorem point_links_checked49340 : (cuts49340.take 1).map (fun c => (6471024641-1+2*2^10*c.k,111491368572556+c.lower,111491755600330+c.upper)) = pointBounds49340 := by
 decide +kernel
def cuts49341 : List PrefixCut := [⟨54,213785186,213785305⟩,
⟨64,252409668,252409809⟩]
theorem checked49341 : checkPrefixCuts (2^48) 6471155713 10 Manual.Count131072.C049341.packed 64 cuts49341 = true := by
 decide +kernel
def pointBounds49341 : List (Nat × Nat × Nat) := [(6471266304,111491834163585,111492221191624)]
theorem point_links_checked49341 : (cuts49341.take 1).map (fun c => (6471155713-1+2*2^10*c.k,111491620378399+c.lower,111492007406319+c.upper)) = pointBounds49341 := by
 decide +kernel
def cuts49342 : List PrefixCut := [⟨64,251882604,251882751⟩]
theorem checked49342 : checkPrefixCuts (2^48) 6471286785 10 Manual.Count131072.C049342.packed 64 cuts49342 = true := by
 decide +kernel
def cuts49343 : List PrefixCut := [⟨25,97385119,97385177⟩,
⟨64,253399805,253399952⟩]
theorem checked49343 : checkPrefixCuts (2^48) 6471417857 10 Manual.Count131072.C049343.packed 64 cuts49343 = true := by
 decide +kernel
def pointBounds49343 : List (Nat × Nat × Nat) := [(6471469056,111492222055790,111492609084056)]
theorem point_links_checked49343 : (cuts49343.take 1).map (fun c => (6471417857-1+2*2^10*c.k,111492124670671+c.lower,111492511698879+c.upper)) = pointBounds49343 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000291
