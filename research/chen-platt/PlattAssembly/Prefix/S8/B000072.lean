import PlattAssemblyKernel
import PlattCertificates.Count131072.C072304
import PlattCertificates.Count131072.C072305
import PlattCertificates.Count131072.C072306
import PlattCertificates.Count131072.C072307
import PlattCertificates.Count131072.C072308
import PlattCertificates.Count131072.C072309
import PlattCertificates.Count131072.C072310
import PlattCertificates.Count131072.C072311
import PlattCertificates.Count131072.C072312
import PlattCertificates.Count131072.C072313
import PlattCertificates.Count131072.C072314
import PlattCertificates.Count131072.C072315
import PlattCertificates.Count131072.C072316
import PlattCertificates.Count131072.C072317
import PlattCertificates.Count131072.C072318
import PlattCertificates.Count131072.C072319
import PlattCertificates.Count131072.C072320
import PlattCertificates.Count131072.C072321
import PlattCertificates.Count131072.C072322
import PlattCertificates.Count131072.C072323
import PlattCertificates.Count131072.C072324
import PlattCertificates.Count131072.C072325
import PlattCertificates.Count131072.C072326
import PlattCertificates.Count131072.C072327
import PlattCertificates.Count131072.C072328
import PlattCertificates.Count131072.C072329
import PlattCertificates.Count131072.C072330
import PlattCertificates.Count131072.C072331
import PlattCertificates.Count131072.C072332
import PlattCertificates.Count131072.C072333
import PlattCertificates.Count131072.C072334
import PlattCertificates.Count131072.C072335
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000072
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72304 : List PrefixCut := [⟨64,169460389,169460491⟩]
theorem checked72304 : checkPrefixCuts (2^48) 9480962049 10 Manual.Count131072.C072304.packed 64 cuts72304 = true := by
 decide +kernel
def cuts72305 : List PrefixCut := [⟨33,87668414,87668467⟩,
⟨64,171031506,171031608⟩]
theorem checked72305 : checkPrefixCuts (2^48) 9481093121 10 Manual.Count131072.C072305.packed 64 cuts72305 = true := by
 decide +kernel
def pointBounds72305 : List (Nat × Nat × Nat) := [(9481160704,116210916681989,116211306421966)]
theorem point_links_checked72305 : (cuts72305.take 1).map (fun c => (9481093121-1+2*2^10*c.k,116210829013575+c.lower,116211218753499+c.upper)) = pointBounds72305 := by
 decide +kernel
def cuts72306 : List PrefixCut := [⟨64,168772895,168772996⟩]
theorem checked72306 : checkPrefixCuts (2^48) 9481224193 10 Manual.Count131072.C072306.packed 64 cuts72306 = true := by
 decide +kernel
def cuts72307 : List PrefixCut := [⟨50,131068276,131068353⟩,
⟨64,168325252,168325353⟩]
theorem checked72307 : checkPrefixCuts (2^48) 9481355265 10 Manual.Count131072.C072307.packed 64 cuts72307 = true := by
 decide +kernel
def pointBounds72307 : List (Nat × Nat × Nat) := [(9481457664,116211299886252,116211689626456)]
theorem point_links_checked72307 : (cuts72307.take 1).map (fun c => (9481355265-1+2*2^10*c.k,116211168817976+c.lower,116211558558103+c.upper)) = pointBounds72307 := by
 decide +kernel
def cuts72308 : List PrefixCut := [⟨64,168174496,168174599⟩]
theorem checked72308 : checkPrefixCuts (2^48) 9481486337 10 Manual.Count131072.C072308.packed 64 cuts72308 = true := by
 decide +kernel
def cuts72309 : List PrefixCut := [⟨64,169804919,169805016⟩]
theorem checked72309 : checkPrefixCuts (2^48) 9481617409 10 Manual.Count131072.C072309.packed 64 cuts72309 = true := by
 decide +kernel
def cuts72310 : List PrefixCut := [⟨3,7629292,7629296⟩,
⟨64,168496392,168496488⟩]
theorem checked72310 : checkPrefixCuts (2^48) 9481748481 10 Manual.Count131072.C072310.packed 64 cuts72310 = true := by
 decide +kernel
def pointBounds72310 : List (Nat × Nat × Nat) := [(9481754624,116211682751935,116212072492367)]
theorem point_links_checked72310 : (cuts72310.take 1).map (fun c => (9481748481-1+2*2^10*c.k,116211675122643+c.lower,116212064863071+c.upper)) = pointBounds72310 := by
 decide +kernel
def cuts72311 : List PrefixCut := [⟨64,169058088,169058184⟩]
theorem checked72311 : checkPrefixCuts (2^48) 9481879553 10 Manual.Count131072.C072311.packed 64 cuts72311 = true := by
 decide +kernel
def cuts72312 : List PrefixCut := [⟨20,52275432,52275464⟩,
⟨64,170629048,170629148⟩]
theorem checked72312 : checkPrefixCuts (2^48) 9482010625 10 Manual.Count131072.C072312.packed 64 cuts72312 = true := by
 decide +kernel
def pointBounds72312 : List (Nat × Nat × Nat) := [(9482051584,116212064952555,116212454693207)]
theorem point_links_checked72312 : (cuts72312.take 1).map (fun c => (9482010625-1+2*2^10*c.k,116212012677123+c.lower,116212402417743+c.upper)) = pointBounds72312 := by
 decide +kernel
def cuts72313 : List PrefixCut := [⟨64,170122058,170122167⟩]
theorem checked72313 : checkPrefixCuts (2^48) 9482141697 10 Manual.Count131072.C072313.packed 64 cuts72313 = true := by
 decide +kernel
def cuts72314 : List PrefixCut := [⟨37,96948628,96948682⟩,
⟨64,168071503,168071599⟩]
theorem checked72314 : checkPrefixCuts (2^48) 9482272769 10 Manual.Count131072.C072314.packed 64 cuts72314 = true := by
 decide +kernel
def pointBounds72314 : List (Nat × Nat × Nat) := [(9482348544,116212450376857,116212840117740)]
theorem point_links_checked72314 : (cuts72314.take 1).map (fun c => (9482272769-1+2*2^10*c.k,116212353428229+c.lower,116212743169058+c.upper)) = pointBounds72314 := by
 decide +kernel
def cuts72315 : List PrefixCut := [⟨64,169404957,169405061⟩]
theorem checked72315 : checkPrefixCuts (2^48) 9482403841 10 Manual.Count131072.C072315.packed 64 cuts72315 = true := by
 decide +kernel
def cuts72316 : List PrefixCut := [⟨54,143043991,143044069⟩,
⟨64,169877537,169877634⟩]
theorem checked72316 : checkPrefixCuts (2^48) 9482534913 10 Manual.Count131072.C072316.packed 64 cuts72316 = true := by
 decide +kernel
def pointBounds72316 : List (Nat × Nat × Nat) := [(9482645504,116212833948680,116213223689787)]
theorem point_links_checked72316 : (cuts72316.take 1).map (fun c => (9482534913-1+2*2^10*c.k,116212690904689+c.lower,116213080645718+c.upper)) = pointBounds72316 := by
 decide +kernel
def cuts72317 : List PrefixCut := [⟨64,169133122,169133221⟩]
theorem checked72317 : checkPrefixCuts (2^48) 9482665985 10 Manual.Count131072.C072317.packed 64 cuts72317 = true := by
 decide +kernel
def cuts72318 : List PrefixCut := [⟨64,168121578,168121677⟩]
theorem checked72318 : checkPrefixCuts (2^48) 9482797057 10 Manual.Count131072.C072318.packed 64 cuts72318 = true := by
 decide +kernel
def cuts72319 : List PrefixCut := [⟨7,18640456,18640466⟩,
⟨64,170078273,170078376⟩]
theorem checked72319 : checkPrefixCuts (2^48) 9482928129 10 Manual.Count131072.C072319.packed 64 cuts72319 = true := by
 decide +kernel
def pointBounds72319 : List (Nat × Nat × Nat) := [(9482942464,116213216677382,116213606418716)]
theorem point_links_checked72319 : (cuts72319.take 1).map (fun c => (9482928129-1+2*2^10*c.k,116213198036926+c.lower,116213587778250+c.upper)) = pointBounds72319 := by
 decide +kernel
def cuts72320 : List PrefixCut := [⟨64,169126114,169126211⟩]
theorem checked72320 : checkPrefixCuts (2^48) 9483059201 10 Manual.Count131072.C072320.packed 64 cuts72320 = true := by
 decide +kernel
def cuts72321 : List PrefixCut := [⟨24,65328715,65328752⟩,
⟨64,171112417,171112516⟩]
theorem checked72321 : checkPrefixCuts (2^48) 9483190273 10 Manual.Count131072.C072321.packed 64 cuts72321 = true := by
 decide +kernel
def pointBounds72321 : List (Nat × Nat × Nat) := [(9483239424,116213602570028,116213992311589)]
theorem point_links_checked72321 : (cuts72321.take 1).map (fun c => (9483190273-1+2*2^10*c.k,116213537241313+c.lower,116213926982837+c.upper)) = pointBounds72321 := by
 decide +kernel
def cuts72322 : List PrefixCut := [⟨64,167518656,167518762⟩]
theorem checked72322 : checkPrefixCuts (2^48) 9483321345 10 Manual.Count131072.C072322.packed 64 cuts72322 = true := by
 decide +kernel
def cuts72323 : List PrefixCut := [⟨41,109313297,109313359⟩,
⟨64,169683025,169683120⟩]
theorem checked72323 : checkPrefixCuts (2^48) 9483452417 10 Manual.Count131072.C072323.packed 64 cuts72323 = true := by
 decide +kernel
def pointBounds72323 : List (Nat × Nat × Nat) := [(9483536384,116213985185683,116214374927474)]
theorem point_links_checked72323 : (cuts72323.take 1).map (fun c => (9483452417-1+2*2^10*c.k,116213875872386+c.lower,116214265614115+c.upper)) = pointBounds72323 := by
 decide +kernel
def cuts72324 : List PrefixCut := [⟨64,171847312,171847417⟩]
theorem checked72324 : checkPrefixCuts (2^48) 9483583489 10 Manual.Count131072.C072324.packed 64 cuts72324 = true := by
 decide +kernel
def cuts72325 : List PrefixCut := [⟨58,152612643,152612736⟩,
⟨64,168431776,168431879⟩]
theorem checked72325 : checkPrefixCuts (2^48) 9483714561 10 Manual.Count131072.C072325.packed 64 cuts72325 = true := by
 decide +kernel
def pointBounds72325 : List (Nat × Nat × Nat) := [(9483833344,116214370015366,116214759757388)]
theorem point_links_checked72325 : (cuts72325.take 1).map (fun c => (9483714561-1+2*2^10*c.k,116214217402723+c.lower,116214607144652+c.upper)) = pointBounds72325 := by
 decide +kernel
def cuts72326 : List PrefixCut := [⟨64,167539086,167539184⟩]
theorem checked72326 : checkPrefixCuts (2^48) 9483845633 10 Manual.Count131072.C072326.packed 64 cuts72326 = true := by
 decide +kernel
def cuts72327 : List PrefixCut := [⟨64,166854153,166854263⟩]
theorem checked72327 : checkPrefixCuts (2^48) 9483976705 10 Manual.Count131072.C072327.packed 64 cuts72327 = true := by
 decide +kernel
def cuts72328 : List PrefixCut := [⟨11,30568905,30568922⟩,
⟨64,168098353,168098450⟩]
theorem checked72328 : checkPrefixCuts (2^48) 9484107777 10 Manual.Count131072.C072328.packed 64 cuts72328 = true := by
 decide +kernel
def pointBounds72328 : List (Nat × Nat × Nat) := [(9484130304,116214750796643,116215140538900)]
theorem point_links_checked72328 : (cuts72328.take 1).map (fun c => (9484107777-1+2*2^10*c.k,116214720227738+c.lower,116215109969978+c.upper)) = pointBounds72328 := by
 decide +kernel
def cuts72329 : List PrefixCut := [⟨64,170203147,170203250⟩]
theorem checked72329 : checkPrefixCuts (2^48) 9484238849 10 Manual.Count131072.C072329.packed 64 cuts72329 = true := by
 decide +kernel
def cuts72330 : List PrefixCut := [⟨28,74965804,74965851⟩,
⟨64,170853709,170853814⟩]
theorem checked72330 : checkPrefixCuts (2^48) 9484369921 10 Manual.Count131072.C072330.packed 64 cuts72330 = true := by
 decide +kernel
def pointBounds72330 : List (Nat × Nat × Nat) := [(9484427264,116215133495042,116215523237529)]
theorem point_links_checked72330 : (cuts72330.take 1).map (fun c => (9484369921-1+2*2^10*c.k,116215058529238+c.lower,116215448271678+c.upper)) = pointBounds72330 := by
 decide +kernel
def cuts72331 : List PrefixCut := [⟨64,169782964,169783063⟩]
theorem checked72331 : checkPrefixCuts (2^48) 9484500993 10 Manual.Count131072.C072331.packed 64 cuts72331 = true := by
 decide +kernel
def cuts72332 : List PrefixCut := [⟨45,118232378,118232449⟩,
⟨64,168534207,168534307⟩]
theorem checked72332 : checkPrefixCuts (2^48) 9484632065 10 Manual.Count131072.C072332.packed 64 cuts72332 = true := by
 decide +kernel
def pointBounds72332 : List (Nat × Nat × Nat) := [(9484724224,116215517398289,116215907141004)]
theorem point_links_checked72332 : (cuts72332.take 1).map (fun c => (9484632065-1+2*2^10*c.k,116215399165911+c.lower,116215788908555+c.upper)) = pointBounds72332 := by
 decide +kernel
def cuts72333 : List PrefixCut := [⟨64,170490510,170490609⟩]
theorem checked72333 : checkPrefixCuts (2^48) 9484763137 10 Manual.Count131072.C072333.packed 64 cuts72333 = true := by
 decide +kernel
def cuts72334 : List PrefixCut := [⟨62,165977451,165977550⟩,
⟨64,171467459,171467562⟩]
theorem checked72334 : checkPrefixCuts (2^48) 9484894209 10 Manual.Count131072.C072334.packed 64 cuts72334 = true := by
 decide +kernel
def pointBounds72334 : List (Nat × Nat × Nat) := [(9485021184,116215904168079,116216293911021)]
theorem point_links_checked72334 : (cuts72334.take 1).map (fun c => (9484894209-1+2*2^10*c.k,116215738190628+c.lower,116216127933471+c.upper)) = pointBounds72334 := by
 decide +kernel
def cuts72335 : List PrefixCut := [⟨64,168527208,168527309⟩]
theorem checked72335 : checkPrefixCuts (2^48) 9485025281 10 Manual.Count131072.C072335.packed 64 cuts72335 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000072
