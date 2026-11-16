import PlattAssemblyKernel
import PlattCertificates.Count131072.C051248
import PlattCertificates.Count131072.C051249
import PlattCertificates.Count131072.C051250
import PlattCertificates.Count131072.C051251
import PlattCertificates.Count131072.C051252
import PlattCertificates.Count131072.C051253
import PlattCertificates.Count131072.C051254
import PlattCertificates.Count131072.C051255
import PlattCertificates.Count131072.C051256
import PlattCertificates.Count131072.C051257
import PlattCertificates.Count131072.C051258
import PlattCertificates.Count131072.C051259
import PlattCertificates.Count131072.C051260
import PlattCertificates.Count131072.C051261
import PlattCertificates.Count131072.C051262
import PlattCertificates.Count131072.C051263
import PlattCertificates.Count131072.C051264
import PlattCertificates.Count131072.C051265
import PlattCertificates.Count131072.C051266
import PlattCertificates.Count131072.C051267
import PlattCertificates.Count131072.C051268
import PlattCertificates.Count131072.C051269
import PlattCertificates.Count131072.C051270
import PlattCertificates.Count131072.C051271
import PlattCertificates.Count131072.C051272
import PlattCertificates.Count131072.C051273
import PlattCertificates.Count131072.C051274
import PlattCertificates.Count131072.C051275
import PlattCertificates.Count131072.C051276
import PlattCertificates.Count131072.C051277
import PlattCertificates.Count131072.C051278
import PlattCertificates.Count131072.C051279
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51248 : List PrefixCut := [⟨64,240510042,240510185⟩]
theorem checked51248 : checkPrefixCuts (2^48) 6721110017 10 Manual.Count131072.C051248.packed 64 cuts51248 = true := by
 decide +kernel
def cuts51249 : List PrefixCut := [⟨21,81076338,81076386⟩,
⟨64,246326417,246326559⟩]
theorem checked51249 : checkPrefixCuts (2^48) 6721241089 10 Manual.Count131072.C051249.packed 64 cuts51249 = true := by
 decide +kernel
def pointBounds51249 : List (Nat × Nat × Nat) := [(6721284096,111963825822408,111964213119008)]
theorem point_links_checked51249 : (cuts51249.take 1).map (fun c => (6721241089-1+2*2^10*c.k,111963744746070+c.lower,111964132042622+c.upper)) = pointBounds51249 := by
 decide +kernel
def cuts51250 : List PrefixCut := [⟨60,225341270,225341401⟩,
⟨64,240919442,240919581⟩]
theorem checked51250 : checkPrefixCuts (2^48) 6721372161 10 Manual.Count131072.C051250.packed 64 cuts51250 = true := by
 decide +kernel
def pointBounds51250 : List (Nat × Nat × Nat) := [(6721495040,111964216413757,111964603710582)]
theorem point_links_checked51250 : (cuts51250.take 1).map (fun c => (6721372161-1+2*2^10*c.k,111963991072487+c.lower,111964378369181+c.upper)) = pointBounds51250 := by
 decide +kernel
def cuts51251 : List PrefixCut := [⟨64,246316799,246316935⟩]
theorem checked51251 : checkPrefixCuts (2^48) 6721503233 10 Manual.Count131072.C051251.packed 64 cuts51251 = true := by
 decide +kernel
def cuts51252 : List PrefixCut := [⟨35,135509888,135509961⟩,
⟨64,247358892,247359027⟩]
theorem checked51252 : checkPrefixCuts (2^48) 6721634305 10 Manual.Count131072.C051252.packed 64 cuts51252 = true := by
 decide +kernel
def pointBounds51252 : List (Nat × Nat × Nat) := [(6721705984,111964613818616,111965001115658)]
theorem point_links_checked51252 : (cuts51252.take 1).map (fun c => (6721634305-1+2*2^10*c.k,111964478308728+c.lower,111964865605697+c.upper)) = pointBounds51252 := by
 decide +kernel
def cuts51253 : List PrefixCut := [⟨64,241324094,241324232⟩]
theorem checked51253 : checkPrefixCuts (2^48) 6721765377 10 Manual.Count131072.C051253.packed 64 cuts51253 = true := by
 decide +kernel
def cuts51254 : List PrefixCut := [⟨10,36681853,36681874⟩,
⟨64,240607548,240607681⟩]
theorem checked51254 : checkPrefixCuts (2^48) 6721896449 10 Manual.Count131072.C051254.packed 64 cuts51254 = true := by
 decide +kernel
def pointBounds51254 : List (Nat × Nat × Nat) := [(6721916928,111965003673567,111965390970830)]
theorem point_links_checked51254 : (cuts51254.take 1).map (fun c => (6721896449-1+2*2^10*c.k,111964966991714+c.lower,111965354288956+c.upper)) = pointBounds51254 := by
 decide +kernel
def cuts51255 : List PrefixCut := [⟨49,182232149,182232255⟩,
⟨64,238341685,238341821⟩]
theorem checked51255 : checkPrefixCuts (2^48) 6722027521 10 Manual.Count131072.C051255.packed 64 cuts51255 = true := by
 decide +kernel
def pointBounds51255 : List (Nat × Nat × Nat) := [(6722127872,111965389831411,111965777128892)]
theorem point_links_checked51255 : (cuts51255.take 1).map (fun c => (6722027521-1+2*2^10*c.k,111965207599262+c.lower,111965594896637+c.upper)) = pointBounds51255 := by
 decide +kernel
def cuts51256 : List PrefixCut := [⟨64,242859274,242859415⟩]
theorem checked51256 : checkPrefixCuts (2^48) 6722158593 10 Manual.Count131072.C051256.packed 64 cuts51256 = true := by
 decide +kernel
def cuts51257 : List PrefixCut := [⟨24,91699077,91699131⟩,
⟨64,242896405,242896547⟩]
theorem checked51257 : checkPrefixCuts (2^48) 6722289665 10 Manual.Count131072.C051257.packed 64 cuts51257 = true := by
 decide +kernel
def pointBounds51257 : List (Nat × Nat × Nat) := [(6722338816,111965780499298,111966167797004)]
theorem point_links_checked51257 : (cuts51257.take 1).map (fun c => (6722289665-1+2*2^10*c.k,111965688800221+c.lower,111966076097873+c.upper)) = pointBounds51257 := by
 decide +kernel
def cuts51258 : List PrefixCut := [⟨63,239039607,239039742⟩,
⟨64,243184762,243184899⟩]
theorem checked51258 : checkPrefixCuts (2^48) 6722420737 10 Manual.Count131072.C051258.packed 64 cuts51258 = true := by
 decide +kernel
def pointBounds51258 : List (Nat × Nat × Nat) := [(6722549760,111966170736233,111966558034162)]
theorem point_links_checked51258 : (cuts51258.take 1).map (fun c => (6722420737-1+2*2^10*c.k,111965931696626+c.lower,111966318994420+c.upper)) = pointBounds51258 := by
 decide +kernel
def cuts51259 : List PrefixCut := [⟨64,244310507,244310646⟩]
theorem checked51259 : checkPrefixCuts (2^48) 6722551809 10 Manual.Count131072.C051259.packed 64 cuts51259 = true := by
 decide +kernel
def cuts51260 : List PrefixCut := [⟨38,141308508,141308587⟩,
⟨64,239742009,239742143⟩]
theorem checked51260 : checkPrefixCuts (2^48) 6722682881 10 Manual.Count131072.C051260.packed 64 cuts51260 = true := by
 decide +kernel
def pointBounds51260 : List (Nat × Nat × Nat) := [(6722760704,111966560500403,111966947798552)]
theorem point_links_checked51260 : (cuts51260.take 1).map (fun c => (6722682881-1+2*2^10*c.k,111966419191895+c.lower,111966806489965+c.upper)) = pointBounds51260 := by
 decide +kernel
def cuts51261 : List PrefixCut := [⟨64,239695467,239695605⟩]
theorem checked51261 : checkPrefixCuts (2^48) 6722813953 10 Manual.Count131072.C051261.packed 64 cuts51261 = true := by
 decide +kernel
def cuts51262 : List PrefixCut := [⟨13,49571375,49571401⟩,
⟨64,243165800,243165936⟩]
theorem checked51262 : checkPrefixCuts (2^48) 6722945025 10 Manual.Count131072.C051262.packed 64 cuts51262 = true := by
 decide +kernel
def pointBounds51262 : List (Nat × Nat × Nat) := [(6722971648,111966948200746,111967335499114)]
theorem point_links_checked51262 : (cuts51262.take 1).map (fun c => (6722945025-1+2*2^10*c.k,111966898629371+c.lower,111967285927713+c.upper)) = pointBounds51262 := by
 decide +kernel
def cuts51263 : List PrefixCut := [⟨52,199662047,199662163⟩,
⟨64,244668255,244668397⟩]
theorem checked51263 : checkPrefixCuts (2^48) 6723076097 10 Manual.Count131072.C051263.packed 64 cuts51263 = true := by
 decide +kernel
def pointBounds51263 : List (Nat × Nat × Nat) := [(6723182592,111967341457218,111967728755812)]
theorem point_links_checked51263 : (cuts51263.take 1).map (fun c => (6723076097-1+2*2^10*c.k,111967141795171+c.lower,111967529093649+c.upper)) = pointBounds51263 := by
 decide +kernel
def cuts51264 : List PrefixCut := [⟨64,242109680,242109818⟩]
theorem checked51264 : checkPrefixCuts (2^48) 6723207169 10 Manual.Count131072.C051264.packed 64 cuts51264 = true := by
 decide +kernel
def cuts51265 : List PrefixCut := [⟨27,103281397,103281454⟩,
⟨64,243402769,243402906⟩]
theorem checked51265 : checkPrefixCuts (2^48) 6723338241 10 Manual.Count131072.C051265.packed 64 cuts51265 = true := by
 decide +kernel
def pointBounds51265 : List (Nat × Nat × Nat) := [(6723393536,111967731854503,111968119153318)]
theorem point_links_checked51265 : (cuts51265.take 1).map (fun c => (6723338241-1+2*2^10*c.k,111967628573106+c.lower,111968015871864+c.upper)) = pointBounds51265 := by
 decide +kernel
def cuts51266 : List PrefixCut := [⟨64,240802436,240802577⟩]
theorem checked51266 : checkPrefixCuts (2^48) 6723469313 10 Manual.Count131072.C051266.packed 64 cuts51266 = true := by
 decide +kernel
def cuts51267 : List PrefixCut := [⟨2,7828513,7828517⟩,
⟨64,243435162,243435296⟩]
theorem checked51267 : checkPrefixCuts (2^48) 6723600385 10 Manual.Count131072.C051267.packed 64 cuts51267 = true := by
 decide +kernel
def pointBounds51267 : List (Nat × Nat × Nat) := [(6723604480,111968120606824,111968507905864)]
theorem point_links_checked51267 : (cuts51267.take 1).map (fun c => (6723600385-1+2*2^10*c.k,111968112778311+c.lower,111968500077347+c.upper)) = pointBounds51267 := by
 decide +kernel
def cuts51268 : List PrefixCut := [⟨41,157529108,157529195⟩,
⟨64,247198006,247198142⟩]
theorem checked51268 : checkPrefixCuts (2^48) 6723731457 10 Manual.Count131072.C051268.packed 64 cuts51268 = true := by
 decide +kernel
def pointBounds51268 : List (Nat × Nat × Nat) := [(6723815424,111968513742581,111968901041838)]
theorem point_links_checked51268 : (cuts51268.take 1).map (fun c => (6723731457-1+2*2^10*c.k,111968356213473+c.lower,111968743512643+c.upper)) = pointBounds51268 := by
 decide +kernel
def cuts51269 : List PrefixCut := [⟨64,239909278,239909418⟩]
theorem checked51269 : checkPrefixCuts (2^48) 6723862529 10 Manual.Count131072.C051269.packed 64 cuts51269 = true := by
 decide +kernel
def cuts51270 : List PrefixCut := [⟨16,60112636,60112671⟩,
⟨64,243839510,243839649⟩]
theorem checked51270 : checkPrefixCuts (2^48) 6723993601 10 Manual.Count131072.C051270.packed 64 cuts51270 = true := by
 decide +kernel
def pointBounds51270 : List (Nat × Nat × Nat) := [(6724026368,111968903433393,111969290732874)]
theorem point_links_checked51270 : (cuts51270.take 1).map (fun c => (6723993601-1+2*2^10*c.k,111968843320757+c.lower,111969230620203+c.upper)) = pointBounds51270 := by
 decide +kernel
def cuts51271 : List PrefixCut := [⟨55,209635405,209635525⟩,
⟨64,243541757,243541896⟩]
theorem checked51271 : checkPrefixCuts (2^48) 6724124673 10 Manual.Count131072.C051271.packed 64 cuts51271 = true := by
 decide +kernel
def pointBounds51271 : List (Nat × Nat × Nat) := [(6724237312,111969296795672,111969684095377)]
theorem point_links_checked51271 : (cuts51271.take 1).map (fun c => (6724124673-1+2*2^10*c.k,111969087160267+c.lower,111969474459852+c.upper)) = pointBounds51271 := by
 decide +kernel
def cuts51272 : List PrefixCut := [⟨64,243369558,243369694⟩]
theorem checked51272 : checkPrefixCuts (2^48) 6724255745 10 Manual.Count131072.C051272.packed 64 cuts51272 = true := by
 decide +kernel
def cuts51273 : List PrefixCut := [⟨30,111888109,111888171⟩,
⟨64,240643995,240644134⟩]
theorem checked51273 : checkPrefixCuts (2^48) 6724386817 10 Manual.Count131072.C051273.packed 64 cuts51273 = true := by
 decide +kernel
def pointBounds51273 : List (Nat × Nat × Nat) := [(6724448256,111969685959691,111970073259613)]
theorem point_links_checked51273 : (cuts51273.take 1).map (fun c => (6724386817-1+2*2^10*c.k,111969574071582+c.lower,111969961371442+c.upper)) = pointBounds51273 := by
 decide +kernel
def cuts51274 : List PrefixCut := [⟨64,241309049,241309185⟩]
theorem checked51274 : checkPrefixCuts (2^48) 6724517889 10 Manual.Count131072.C051274.packed 64 cuts51274 = true := by
 decide +kernel
def cuts51275 : List PrefixCut := [⟨5,18710148,18710161⟩,
⟨64,241764762,241764906⟩]
theorem checked51275 : checkPrefixCuts (2^48) 6724648961 10 Manual.Count131072.C051275.packed 64 cuts51275 = true := by
 decide +kernel
def pointBounds51275 : List (Nat × Nat × Nat) := [(6724659200,111970074734774,111970462034922)]
theorem point_links_checked51275 : (cuts51275.take 1).map (fun c => (6724648961-1+2*2^10*c.k,111970056024626+c.lower,111970443324761+c.upper)) = pointBounds51275 := by
 decide +kernel
def cuts51276 : List PrefixCut := [⟨44,167926649,167926744⟩,
⟨64,242932034,242932173⟩]
theorem checked51276 : checkPrefixCuts (2^48) 6724780033 10 Manual.Count131072.C051276.packed 64 cuts51276 = true := by
 decide +kernel
def pointBounds51276 : List (Nat × Nat × Nat) := [(6724870144,111970465716037,111970853016411)]
theorem point_links_checked51276 : (cuts51276.take 1).map (fun c => (6724780033-1+2*2^10*c.k,111970297789388+c.lower,111970685089667+c.upper)) = pointBounds51276 := by
 decide +kernel
def cuts51277 : List PrefixCut := [⟨64,241797195,241797334⟩]
theorem checked51277 : checkPrefixCuts (2^48) 6724911105 10 Manual.Count131072.C051277.packed 64 cuts51277 = true := by
 decide +kernel
def cuts51278 : List PrefixCut := [⟨19,71487690,71487731⟩,
⟨64,242462138,242462277⟩]
theorem checked51278 : checkPrefixCuts (2^48) 6725042177 10 Manual.Count131072.C051278.packed 64 cuts51278 = true := by
 decide +kernel
def pointBounds51278 : List (Nat × Nat × Nat) := [(6725081088,111970854006307,111971241306905)]
theorem point_links_checked51278 : (cuts51278.take 1).map (fun c => (6725042177-1+2*2^10*c.k,111970782518617+c.lower,111971169819174+c.upper)) = pointBounds51278 := by
 decide +kernel
def cuts51279 : List PrefixCut := [⟨58,219312626,219312751⟩,
⟨64,241913327,241913464⟩]
theorem checked51279 : checkPrefixCuts (2^48) 6725173249 10 Manual.Count131072.C051279.packed 64 cuts51279 = true := by
 decide +kernel
def pointBounds51279 : List (Nat × Nat × Nat) := [(6725292032,111971244293381,111971631594202)]
theorem point_links_checked51279 : (cuts51279.take 1).map (fun c => (6725173249-1+2*2^10*c.k,111971024980755+c.lower,111971412281451+c.upper)) = pointBounds51279 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000039
