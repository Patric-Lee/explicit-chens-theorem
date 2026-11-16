import PlattAssemblyKernel
import PlattCertificates.Count131072.C060288
import PlattCertificates.Count131072.C060289
import PlattCertificates.Count131072.C060290
import PlattCertificates.Count131072.C060291
import PlattCertificates.Count131072.C060292
import PlattCertificates.Count131072.C060293
import PlattCertificates.Count131072.C060294
import PlattCertificates.Count131072.C060295
import PlattCertificates.Count131072.C060296
import PlattCertificates.Count131072.C060297
import PlattCertificates.Count131072.C060298
import PlattCertificates.Count131072.C060299
import PlattCertificates.Count131072.C060300
import PlattCertificates.Count131072.C060301
import PlattCertificates.Count131072.C060302
import PlattCertificates.Count131072.C060303
import PlattCertificates.Count131072.C060304
import PlattCertificates.Count131072.C060305
import PlattCertificates.Count131072.C060306
import PlattCertificates.Count131072.C060307
import PlattCertificates.Count131072.C060308
import PlattCertificates.Count131072.C060309
import PlattCertificates.Count131072.C060310
import PlattCertificates.Count131072.C060311
import PlattCertificates.Count131072.C060312
import PlattCertificates.Count131072.C060313
import PlattCertificates.Count131072.C060314
import PlattCertificates.Count131072.C060315
import PlattCertificates.Count131072.C060316
import PlattCertificates.Count131072.C060317
import PlattCertificates.Count131072.C060318
import PlattCertificates.Count131072.C060319
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60288 : List PrefixCut := [⟨15,48027936,48027963⟩,
⟨64,202470823,202470942⟩]
theorem checked60288 : checkPrefixCuts (2^48) 7906000897 10 Manual.Count131072.C060288.packed 64 cuts60288 = true := by
 decide +kernel
def pointBounds60288 : List (Nat × Nat × Nat) := [(7906031616,113975959910840,113976348351880)]
theorem point_links_checked60288 : (cuts60288.take 1).map (fun c => (7906000897-1+2*2^10*c.k,113975911882904+c.lower,113976300323917+c.upper)) = pointBounds60288 := by
 decide +kernel
def cuts60289 : List PrefixCut := [⟨64,206917680,206917794⟩]
theorem checked60289 : checkPrefixCuts (2^48) 7906131969 10 Manual.Count131072.C060289.packed 64 cuts60289 = true := by
 decide +kernel
def cuts60290 : List PrefixCut := [⟨8,25312646,25312661⟩,
⟨64,207555057,207555171⟩]
theorem checked60290 : checkPrefixCuts (2^48) 7906263041 10 Manual.Count131072.C060290.packed 64 cuts60290 = true := by
 decide +kernel
def pointBounds60290 : List (Nat × Nat × Nat) := [(7906279424,113976346584053,113976735025314)]
theorem point_links_checked60290 : (cuts60290.take 1).map (fun c => (7906263041-1+2*2^10*c.k,113976321271407+c.lower,113976709712653+c.upper)) = pointBounds60290 := by
 decide +kernel
def cuts60291 : List PrefixCut := [⟨64,203991574,203991691⟩]
theorem checked60291 : checkPrefixCuts (2^48) 7906394113 10 Manual.Count131072.C060291.packed 64 cuts60291 = true := by
 decide +kernel
def cuts60292 : List PrefixCut := [⟨1,3488832,3488834⟩,
⟨64,203560991,203561112⟩]
theorem checked60292 : checkPrefixCuts (2^48) 7906525185 10 Manual.Count131072.C060292.packed 64 cuts60292 = true := by
 decide +kernel
def pointBounds60292 : List (Nat × Nat × Nat) := [(7906527232,113976736306870,113977124748349)]
theorem point_links_checked60292 : (cuts60292.take 1).map (fun c => (7906525185-1+2*2^10*c.k,113976732818038+c.lower,113977121259515+c.upper)) = pointBounds60292 := by
 decide +kernel
def cuts60293 : List PrefixCut := [⟨58,183622057,183622162⟩,
⟨64,202703216,202703332⟩]
theorem checked60293 : checkPrefixCuts (2^48) 7906656257 10 Manual.Count131072.C060293.packed 64 cuts60293 = true := by
 decide +kernel
def pointBounds60293 : List (Nat × Nat × Nat) := [(7906775040,113977120001086,113977508442789)]
theorem point_links_checked60293 : (cuts60293.take 1).map (fun c => (7906656257-1+2*2^10*c.k,113976936379029+c.lower,113977324820627+c.upper)) = pointBounds60293 := by
 decide +kernel
def cuts60294 : List PrefixCut := [⟨64,205476585,205476698⟩]
theorem checked60294 : checkPrefixCuts (2^48) 7906787329 10 Manual.Count131072.C060294.packed 64 cuts60294 = true := by
 decide +kernel
def cuts60295 : List PrefixCut := [⟨51,162470750,162470842⟩,
⟨64,204654412,204654528⟩]
theorem checked60295 : checkPrefixCuts (2^48) 7906918401 10 Manual.Count131072.C060295.packed 64 cuts60295 = true := by
 decide +kernel
def pointBounds60295 : List (Nat × Nat × Nat) := [(7907022848,113977507029580,113977895471499)]
theorem point_links_checked60295 : (cuts60295.take 1).map (fun c => (7906918401-1+2*2^10*c.k,113977344558830+c.lower,113977733000657+c.upper)) = pointBounds60295 := by
 decide +kernel
def cuts60296 : List PrefixCut := [⟨64,209705897,209706010⟩]
theorem checked60296 : checkPrefixCuts (2^48) 7907049473 10 Manual.Count131072.C060296.packed 64 cuts60296 = true := by
 decide +kernel
def cuts60297 : List PrefixCut := [⟨44,143243037,143243114⟩,
⟨64,205395189,205395302⟩]
theorem checked60297 : checkPrefixCuts (2^48) 7907180545 10 Manual.Count131072.C060297.packed 64 cuts60297 = true := by
 decide +kernel
def pointBounds60297 : List (Nat × Nat × Nat) := [(7907270656,113977902162176,113978290604309)]
theorem point_links_checked60297 : (cuts60297.take 1).map (fun c => (7907180545-1+2*2^10*c.k,113977758919139+c.lower,113978147361195+c.upper)) = pointBounds60297 := by
 decide +kernel
def cuts60298 : List PrefixCut := [⟨64,207741150,207741266⟩]
theorem checked60298 : checkPrefixCuts (2^48) 7907311617 10 Manual.Count131072.C060298.packed 64 cuts60298 = true := by
 decide +kernel
def cuts60299 : List PrefixCut := [⟨37,115259940,115260005⟩,
⟨64,203928910,203929026⟩]
theorem checked60299 : checkPrefixCuts (2^48) 7907442689 10 Manual.Count131072.C060299.packed 64 cuts60299 = true := by
 decide +kernel
def pointBounds60299 : List (Nat × Nat × Nat) := [(7907518464,113978287315418,113978675757768)]
theorem point_links_checked60299 : (cuts60299.take 1).map (fun c => (7907442689-1+2*2^10*c.k,113978172055478+c.lower,113978560497763+c.upper)) = pointBounds60299 := by
 decide +kernel
def cuts60300 : List PrefixCut := [⟨64,203961149,203961268⟩]
theorem checked60300 : checkPrefixCuts (2^48) 7907573761 10 Manual.Count131072.C060300.packed 64 cuts60300 = true := by
 decide +kernel
def cuts60301 : List PrefixCut := [⟨30,96604507,96604562⟩,
⟨64,206449396,206449513⟩]
theorem checked60301 : checkPrefixCuts (2^48) 7907704833 10 Manual.Count131072.C060301.packed 64 cuts60301 = true := by
 decide +kernel
def pointBounds60301 : List (Nat × Nat × Nat) := [(7907766272,113978676550044,113979064992619)]
theorem point_links_checked60301 : (cuts60301.take 1).map (fun c => (7907704833-1+2*2^10*c.k,113978579945537+c.lower,113978968388057+c.upper)) = pointBounds60301 := by
 decide +kernel
def cuts60302 : List PrefixCut := [⟨64,206018839,206018962⟩]
theorem checked60302 : checkPrefixCuts (2^48) 7907835905 10 Manual.Count131072.C060302.packed 64 cuts60302 = true := by
 decide +kernel
def cuts60303 : List PrefixCut := [⟨23,73465464,73465508⟩,
⟨64,205018811,205018930⟩]
theorem checked60303 : checkPrefixCuts (2^48) 7907966977 10 Manual.Count131072.C060303.packed 64 cuts60303 = true := by
 decide +kernel
def pointBounds60303 : List (Nat × Nat × Nat) := [(7908014080,113979065879236,113979454322040)]
theorem point_links_checked60303 : (cuts60303.take 1).map (fun c => (7907966977-1+2*2^10*c.k,113978992413772+c.lower,113979380856532+c.upper)) = pointBounds60303 := by
 decide +kernel
def cuts60304 : List PrefixCut := [⟨64,202025617,202025729⟩]
theorem checked60304 : checkPrefixCuts (2^48) 7908098049 10 Manual.Count131072.C060304.packed 64 cuts60304 = true := by
 decide +kernel
def cuts60305 : List PrefixCut := [⟨16,51288913,51288941⟩,
⟨64,205474704,205474823⟩]
theorem checked60305 : checkPrefixCuts (2^48) 7908229121 10 Manual.Count131072.C060305.packed 64 cuts60305 = true := by
 decide +kernel
def pointBounds60305 : List (Nat × Nat × Nat) := [(7908261888,113979450747113,113979839190132)]
theorem point_links_checked60305 : (cuts60305.take 1).map (fun c => (7908229121-1+2*2^10*c.k,113979399458200+c.lower,113979787901191+c.upper)) = pointBounds60305 := by
 decide +kernel
def cuts60306 : List PrefixCut := [⟨64,205898410,205898525⟩]
theorem checked60306 : checkPrefixCuts (2^48) 7908360193 10 Manual.Count131072.C060306.packed 64 cuts60306 = true := by
 decide +kernel
def cuts60307 : List PrefixCut := [⟨9,27476589,27476605⟩,
⟨64,200876629,200876748⟩]
theorem checked60307 : checkPrefixCuts (2^48) 7908491265 10 Manual.Count131072.C060307.packed 64 cuts60307 = true := by
 decide +kernel
def pointBounds60307 : List (Nat × Nat × Nat) := [(7908509696,113979838307903,113980226751144)]
theorem point_links_checked60307 : (cuts60307.take 1).map (fun c => (7908491265-1+2*2^10*c.k,113979810831314+c.lower,113980199274539+c.upper)) = pointBounds60307 := by
 decide +kernel
def cuts60308 : List PrefixCut := [⟨64,204361211,204361327⟩]
theorem checked60308 : checkPrefixCuts (2^48) 7908622337 10 Manual.Count131072.C060308.packed 64 cuts60308 = true := by
 decide +kernel
def cuts60309 : List PrefixCut := [⟨2,6441843,6441846⟩,
⟨64,205140788,205140908⟩]
theorem checked60309 : checkPrefixCuts (2^48) 7908753409 10 Manual.Count131072.C060309.packed 64 cuts60309 = true := by
 decide +kernel
def pointBounds60309 : List (Nat × Nat × Nat) := [(7908757504,113980222510997,113980610954460)]
theorem point_links_checked60309 : (cuts60309.take 1).map (fun c => (7908753409-1+2*2^10*c.k,113980216069154+c.lower,113980604512614+c.upper)) = pointBounds60309 := by
 decide +kernel
def cuts60310 : List PrefixCut := [⟨59,187841043,187841149⟩,
⟨64,204817064,204817179⟩]
theorem checked60310 : checkPrefixCuts (2^48) 7908884481 10 Manual.Count131072.C060310.packed 64 cuts60310 = true := by
 decide +kernel
def pointBounds60310 : List (Nat × Nat × Nat) := [(7909005312,113980609050985,113980997494671)]
theorem point_links_checked60310 : (cuts60310.take 1).map (fun c => (7908884481-1+2*2^10*c.k,113980421209942+c.lower,113980809653522+c.upper)) = pointBounds60310 := by
 decide +kernel
def cuts60311 : List PrefixCut := [⟨64,206842262,206842381⟩]
theorem checked60311 : checkPrefixCuts (2^48) 7909015553 10 Manual.Count131072.C060311.packed 64 cuts60311 = true := by
 decide +kernel
def cuts60312 : List PrefixCut := [⟨52,167585257,167585353⟩,
⟨64,207016756,207016873⟩]
theorem checked60312 : checkPrefixCuts (2^48) 7909146625 10 Manual.Count131072.C060312.packed 64 cuts60312 = true := by
 decide +kernel
def pointBounds60312 : List (Nat × Nat × Nat) := [(7909253120,113981000454525,113981388898435)]
theorem point_links_checked60312 : (cuts60312.take 1).map (fun c => (7909146625-1+2*2^10*c.k,113980832869268+c.lower,113981221313082+c.upper)) = pointBounds60312 := by
 decide +kernel
def cuts60313 : List PrefixCut := [⟨64,204735717,204735837⟩]
theorem checked60313 : checkPrefixCuts (2^48) 7909277697 10 Manual.Count131072.C060313.packed 64 cuts60313 = true := by
 decide +kernel
def cuts60314 : List PrefixCut := [⟨45,144412621,144412700⟩,
⟨64,205444065,205444179⟩]
theorem checked60314 : checkPrefixCuts (2^48) 7909408769 10 Manual.Count131072.C060314.packed 64 cuts60314 = true := by
 decide +kernel
def pointBounds60314 : List (Nat × Nat × Nat) := [(7909500928,113981389034362,113981777478492)]
theorem point_links_checked60314 : (cuts60314.take 1).map (fun c => (7909408769-1+2*2^10*c.k,113981244621741+c.lower,113981633065792+c.upper)) = pointBounds60314 := by
 decide +kernel
def cuts60315 : List PrefixCut := [⟨64,206543841,206543963⟩]
theorem checked60315 : checkPrefixCuts (2^48) 7909539841 10 Manual.Count131072.C060315.packed 64 cuts60315 = true := by
 decide +kernel
def cuts60316 : List PrefixCut := [⟨38,123163120,123163188⟩,
⟨64,206113383,206113497⟩]
theorem checked60316 : checkPrefixCuts (2^48) 7909670913 10 Manual.Count131072.C060316.packed 64 cuts60316 = true := by
 decide +kernel
def pointBounds60316 : List (Nat × Nat × Nat) := [(7909748736,113981779772767,113982168217122)]
theorem point_links_checked60316 : (cuts60316.take 1).map (fun c => (7909670913-1+2*2^10*c.k,113981656609647+c.lower,113982045053934+c.upper)) = pointBounds60316 := by
 decide +kernel
def cuts60317 : List PrefixCut := [⟨64,206608160,206608276⟩]
theorem checked60317 : checkPrefixCuts (2^48) 7909801985 10 Manual.Count131072.C060317.packed 64 cuts60317 = true := by
 decide +kernel
def cuts60318 : List PrefixCut := [⟨31,97324567,97324623⟩,
⟨64,202832769,202832887⟩]
theorem checked60318 : checkPrefixCuts (2^48) 7909933057 10 Manual.Count131072.C060318.packed 64 cuts60318 = true := by
 decide +kernel
def pointBounds60318 : List (Nat × Nat × Nat) := [(7909996544,113982166655757,113982555100330)]
theorem point_links_checked60318 : (cuts60318.take 1).map (fun c => (7909933057-1+2*2^10*c.k,113982069331190+c.lower,113982457775707+c.upper)) = pointBounds60318 := by
 decide +kernel
def cuts60319 : List PrefixCut := [⟨64,205711718,205711831⟩]
theorem checked60319 : checkPrefixCuts (2^48) 7910064129 10 Manual.Count131072.C060319.packed 64 cuts60319 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000009
