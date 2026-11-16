import PlattAssemblyKernel
import PlattCertificates.Count131072.C025280
import PlattCertificates.Count131072.C025281
import PlattCertificates.Count131072.C025282
import PlattCertificates.Count131072.C025283
import PlattCertificates.Count131072.C025284
import PlattCertificates.Count131072.C025285
import PlattCertificates.Count131072.C025286
import PlattCertificates.Count131072.C025287
import PlattCertificates.Count131072.C025288
import PlattCertificates.Count131072.C025289
import PlattCertificates.Count131072.C025290
import PlattCertificates.Count131072.C025291
import PlattCertificates.Count131072.C025292
import PlattCertificates.Count131072.C025293
import PlattCertificates.Count131072.C025294
import PlattCertificates.Count131072.C025295
import PlattCertificates.Count131072.C025296
import PlattCertificates.Count131072.C025297
import PlattCertificates.Count131072.C025298
import PlattCertificates.Count131072.C025299
import PlattCertificates.Count131072.C025300
import PlattCertificates.Count131072.C025301
import PlattCertificates.Count131072.C025302
import PlattCertificates.Count131072.C025303
import PlattCertificates.Count131072.C025304
import PlattCertificates.Count131072.C025305
import PlattCertificates.Count131072.C025306
import PlattCertificates.Count131072.C025307
import PlattCertificates.Count131072.C025308
import PlattCertificates.Count131072.C025309
import PlattCertificates.Count131072.C025310
import PlattCertificates.Count131072.C025311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000165
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25280 : List PrefixCut := [⟨50,199983313,199983427⟩,
⟨128,510430737,510431026⟩]
theorem checked25280 : checkPrefixCuts (2^48) 3317432321 9 Manual.Count131072.C025280.packed 128 cuts25280 = true := by
 decide +kernel
def pointBounds25280 : List (Nat × Nat × Nat) := [(3317483520,103041064772755,103041446869567)]
theorem point_links_checked25280 : (cuts25280.take 1).map (fun c => (3317432321-1+2*2^9*c.k,103040864789442+c.lower,103041246886140+c.upper)) = pointBounds25280 := by
 decide +kernel
def cuts25281 : List PrefixCut := [⟨24,94006649,94006700⟩,
⟨126,495223870,495224154⟩,
⟨128,502265635,502265923⟩]
theorem checked25281 : checkPrefixCuts (2^48) 3317563393 9 Manual.Count131072.C025281.packed 128 cuts25281 = true := by
 decide +kernel
def pointBounds25281 : List (Nat × Nat × Nat) := [(3317587968,103041469226828,103041851323866),(3317692416,103041870444049,103042252541320)]
theorem point_links_checked25281 : (cuts25281.take 2).map (fun c => (3317563393-1+2*2^9*c.k,103041375220179+c.lower,103041757317166+c.upper)) = pointBounds25281 := by
 decide +kernel
def cuts25282 : List PrefixCut := [⟨100,391702580,391702797⟩,
⟨128,502754909,502755189⟩]
theorem checked25282 : checkPrefixCuts (2^48) 3317694465 9 Manual.Count131072.C025282.packed 128 cuts25282 = true := by
 decide +kernel
def pointBounds25282 : List (Nat × Nat × Nat) := [(3317796864,103042269188394,103042651285886)]
theorem point_links_checked25282 : (cuts25282.take 1).map (fun c => (3317694465-1+2*2^9*c.k,103041877485814+c.lower,103042259583089+c.upper)) = pointBounds25282 := by
 decide +kernel
def cuts25283 : List PrefixCut := [⟨74,294466429,294466596⟩,
⟨128,511048938,511049229⟩]
theorem checked25283 : checkPrefixCuts (2^48) 3317825537 9 Manual.Count131072.C025283.packed 128 cuts25283 = true := by
 decide +kernel
def pointBounds25283 : List (Nat × Nat × Nat) := [(3317901312,103042674707152,103043056804874)]
theorem point_links_checked25283 : (cuts25283.take 1).map (fun c => (3317825537-1+2*2^9*c.k,103042380240723+c.lower,103042762338278+c.upper)) = pointBounds25283 := by
 decide +kernel
def cuts25284 : List PrefixCut := [⟨48,187057170,187057274⟩,
⟨128,506532602,506532882⟩]
theorem checked25284 : checkPrefixCuts (2^48) 3317956609 9 Manual.Count131072.C025284.packed 128 cuts25284 = true := by
 decide +kernel
def pointBounds25284 : List (Nat × Nat × Nat) := [(3318005760,103043078346831,103043460444781)]
theorem point_links_checked25284 : (cuts25284.take 1).map (fun c => (3317956609-1+2*2^9*c.k,103042891289661+c.lower,103043273387507+c.upper)) = pointBounds25284 := by
 decide +kernel
def cuts25285 : List PrefixCut := [⟨22,86272285,86272335⟩,
⟨124,490989287,490989566⟩,
⟨128,508124373,508124661⟩]
theorem checked25285 : checkPrefixCuts (2^48) 3318087681 9 Manual.Count131072.C025285.packed 128 cuts25285 = true := by
 decide +kernel
def pointBounds25285 : List (Nat × Nat × Nat) := [(3318110208,103043484094548,103043866192724),(3318214656,103043888811550,103044270909955)]
theorem point_links_checked25285 : (cuts25285.take 2).map (fun c => (3318087681-1+2*2^9*c.k,103043397822263+c.lower,103043779920389+c.upper)) = pointBounds25285 := by
 decide +kernel
def cuts25286 : List PrefixCut := [⟨98,382988607,382988819⟩,
⟨128,505389852,505390129⟩]
theorem checked25286 : checkPrefixCuts (2^48) 3318218753 9 Manual.Count131072.C025286.packed 128 cuts25286 = true := by
 decide +kernel
def pointBounds25286 : List (Nat × Nat × Nat) := [(3318319104,103044288935243,103044671033869)]
theorem point_links_checked25286 : (cuts25286.take 1).map (fun c => (3318218753-1+2*2^9*c.k,103043905946636+c.lower,103044288045050+c.upper)) = pointBounds25286 := by
 decide +kernel
def cuts25287 : List PrefixCut := [⟨72,288058289,288058449⟩,
⟨128,508423598,508423881⟩]
theorem checked25287 : checkPrefixCuts (2^48) 3318349825 9 Manual.Count131072.C025287.packed 128 cuts25287 = true := by
 decide +kernel
def pointBounds25287 : List (Nat × Nat × Nat) := [(3318423552,103044699394777,103045081493628)]
theorem point_links_checked25287 : (cuts25287.take 1).map (fun c => (3318349825-1+2*2^9*c.k,103044411336488+c.lower,103044793435179+c.upper)) = pointBounds25287 := by
 decide +kernel
def cuts25288 : List PrefixCut := [⟨46,186942843,186942946⟩,
⟨128,511032870,511033152⟩]
theorem checked25288 : checkPrefixCuts (2^48) 3318480897 9 Manual.Count131072.C025288.packed 128 cuts25288 = true := by
 decide +kernel
def pointBounds25288 : List (Nat × Nat × Nat) := [(3318528000,103045106702929,103045488802006)]
theorem point_links_checked25288 : (cuts25288.take 1).map (fun c => (3318480897-1+2*2^9*c.k,103044919760086+c.lower,103045301859060+c.upper)) = pointBounds25288 := by
 decide +kernel
def cuts25289 : List PrefixCut := [⟨20,79727785,79727830⟩,
⟨122,488537001,488537268⟩,
⟨128,512030418,512030699⟩]
theorem checked25289 : checkPrefixCuts (2^48) 3318611969 9 Manual.Count131072.C025289.packed 128 cuts25289 = true := by
 decide +kernel
def pointBounds25289 : List (Nat × Nat × Nat) := [(3318632448,103045510520741,103045892620042),(3318736896,103045919329957,103046301429480)]
theorem point_links_checked25289 : (cuts25289.take 2).map (fun c => (3318611969-1+2*2^9*c.k,103045430792956+c.lower,103045812892212+c.upper)) = pointBounds25289 := by
 decide +kernel
def cuts25290 : List PrefixCut := [⟨96,386235840,386236054⟩,
⟨128,510822866,510823156⟩]
theorem checked25290 : checkPrefixCuts (2^48) 3318743041 9 Manual.Count131072.C025290.packed 128 cuts25290 = true := by
 decide +kernel
def pointBounds25290 : List (Nat × Nat × Nat) := [(3318841344,103046329059214,103046711158965)]
theorem point_links_checked25290 : (cuts25290.take 1).map (fun c => (3318743041-1+2*2^9*c.k,103045942823374+c.lower,103046324922911+c.upper)) = pointBounds25290 := by
 decide +kernel
def cuts25291 : List PrefixCut := [⟨70,271559856,271560009⟩,
⟨128,503593903,503594190⟩]
theorem checked25291 : checkPrefixCuts (2^48) 3318874113 9 Manual.Count131072.C025291.packed 128 cuts25291 = true := by
 decide +kernel
def pointBounds25291 : List (Nat × Nat × Nat) := [(3318945792,103046725206096,103047107306076)]
theorem point_links_checked25291 : (cuts25291.take 1).map (fun c => (3318874113-1+2*2^9*c.k,103046453646240+c.lower,103046835746067+c.upper)) = pointBounds25291 := by
 decide +kernel
def cuts25292 : List PrefixCut := [⟨44,173598758,173598856⟩,
⟨128,506287863,506288151⟩]
theorem checked25292 : checkPrefixCuts (2^48) 3319005185 9 Manual.Count131072.C025292.packed 128 cuts25292 = true := by
 decide +kernel
def pointBounds25292 : List (Nat × Nat × Nat) := [(3319050240,103047130838901,103047512939113)]
theorem point_links_checked25292 : (cuts25292.take 1).map (fun c => (3319005185-1+2*2^9*c.k,103046957240143+c.lower,103047339340257+c.upper)) = pointBounds25292 := by
 decide +kernel
def cuts25293 : List PrefixCut := [⟨18,74202996,74203037⟩,
⟨120,481675823,481676092⟩,
⟨128,513730379,513730665⟩]
theorem checked25293 : checkPrefixCuts (2^48) 3319136257 9 Manual.Count131072.C025293.packed 128 cuts25293 = true := by
 decide +kernel
def pointBounds25293 : List (Nat × Nat × Nat) := [(3319154688,103047537731002,103047919831445),(3319259136,103047945203829,103048327304500)]
theorem point_links_checked25293 : (cuts25293.take 2).map (fun c => (3319136257-1+2*2^9*c.k,103047463528006+c.lower,103047845628408+c.upper)) = pointBounds25293 := by
 decide +kernel
def cuts25294 : List PrefixCut := [⟨94,379306287,379306493⟩,
⟨128,516423691,516423972⟩]
theorem checked25294 : checkPrefixCuts (2^48) 3319267329 9 Manual.Count131072.C025294.packed 128 cuts25294 = true := by
 decide +kernel
def pointBounds25294 : List (Nat × Nat × Nat) := [(3319363584,103048356564672,103048738665566)]
theorem point_links_checked25294 : (cuts25294.take 1).map (fun c => (3319267329-1+2*2^9*c.k,103047977258385+c.lower,103048359359073+c.upper)) = pointBounds25294 := by
 decide +kernel
def cuts25295 : List PrefixCut := [⟨68,267362030,267362180⟩,
⟨128,506821429,506821708⟩]
theorem checked25295 : checkPrefixCuts (2^48) 3319398401 9 Manual.Count131072.C025295.packed 128 cuts25295 = true := by
 decide +kernel
def pointBounds25295 : List (Nat × Nat × Nat) := [(3319468032,103048761044106,103049143145225)]
theorem point_links_checked25295 : (cuts25295.take 1).map (fun c => (3319398401-1+2*2^9*c.k,103048493682076+c.lower,103048875783045+c.upper)) = pointBounds25295 := by
 decide +kernel
def cuts25296 : List PrefixCut := [⟨42,166363999,166364092⟩,
⟨128,509599481,509599763⟩]
theorem checked25296 : checkPrefixCuts (2^48) 3319529473 9 Manual.Count131072.C025296.packed 128 cuts25296 = true := by
 decide +kernel
def pointBounds25296 : List (Nat × Nat × Nat) := [(3319572480,103049166867504,103049548968845)]
theorem point_links_checked25296 : (cuts25296.take 1).map (fun c => (3319529473-1+2*2^9*c.k,103049000503505+c.lower,103049382604753+c.upper)) = pointBounds25296 := by
 decide +kernel
def cuts25297 : List PrefixCut := [⟨16,63846917,63846953⟩,
⟨118,463200812,463201070⟩,
⟨128,502372430,502372710⟩]
theorem checked25297 : checkPrefixCuts (2^48) 3319660545 9 Manual.Count131072.C025297.packed 128 cuts25297 = true := by
 decide +kernel
def pointBounds25297 : List (Nat × Nat × Nat) := [(3319676928,103049573949903,103049956051469),(3319781376,103049973303798,103050355405586)]
theorem point_links_checked25297 : (cuts25297.take 2).map (fun c => (3319660545-1+2*2^9*c.k,103049510102986+c.lower,103049892204516+c.upper)) = pointBounds25297 := by
 decide +kernel
def cuts25298 : List PrefixCut := [⟨92,364493728,364493929⟩,
⟨128,510661418,510661700⟩]
theorem checked25298 : checkPrefixCuts (2^48) 3319791617 9 Manual.Count131072.C025298.packed 128 cuts25298 = true := by
 decide +kernel
def pointBounds25298 : List (Nat × Nat × Nat) := [(3319885824,103050376969144,103050759071155)]
theorem point_links_checked25298 : (cuts25298.take 1).map (fun c => (3319791617-1+2*2^9*c.k,103050012475416+c.lower,103050394577226+c.upper)) = pointBounds25298 := by
 decide +kernel
def cuts25299 : List PrefixCut := [⟨66,268676377,268676528⟩,
⟨128,513354442,513354730⟩]
theorem checked25299 : checkPrefixCuts (2^48) 3319922689 9 Manual.Count131072.C025299.packed 128 cuts25299 = true := by
 decide +kernel
def pointBounds25299 : List (Nat × Nat × Nat) := [(3319990272,103050791813211,103051173915454)]
theorem point_links_checked25299 : (cuts25299.take 1).map (fun c => (3319922689-1+2*2^9*c.k,103050523136834+c.lower,103050905238926+c.upper)) = pointBounds25299 := by
 decide +kernel
def cuts25300 : List PrefixCut := [⟨40,158453258,158453346⟩,
⟨128,503754188,503754470⟩]
theorem checked25300 : checkPrefixCuts (2^48) 3320053761 9 Manual.Count131072.C025300.packed 128 cuts25300 = true := by
 decide +kernel
def pointBounds25300 : List (Nat × Nat × Nat) := [(3320094720,103051194944534,103051577047002)]
theorem point_links_checked25300 : (cuts25300.take 1).map (fun c => (3320053761-1+2*2^9*c.k,103051036491276+c.lower,103051418593656+c.upper)) = pointBounds25300 := by
 decide +kernel
def cuts25301 : List PrefixCut := [⟨14,54850522,54850554⟩,
⟨116,461601834,461602098⟩,
⟨128,509159873,509160165⟩]
theorem checked25301 : checkPrefixCuts (2^48) 3320184833 9 Manual.Count131072.C025301.packed 128 cuts25301 = true := by
 decide +kernel
def pointBounds25301 : List (Nat × Nat × Nat) := [(3320199168,103051595095986,103051977198680),(3320303616,103052001847298,103052383950224)]
theorem point_links_checked25301 : (cuts25301.take 2).map (fun c => (3320184833-1+2*2^9*c.k,103051540245464+c.lower,103051922348126+c.upper)) = pointBounds25301 := by
 decide +kernel
def cuts25302 : List PrefixCut := [⟨90,357315468,357315664⟩,
⟨128,502697174,502697452⟩]
theorem checked25302 : checkPrefixCuts (2^48) 3320315905 9 Manual.Count131072.C025302.packed 128 cuts25302 = true := by
 decide +kernel
def pointBounds25302 : List (Nat × Nat × Nat) := [(3320408064,103052406720805,103052788823955)]
theorem point_links_checked25302 : (cuts25302.take 1).map (fun c => (3320315905-1+2*2^9*c.k,103052049405337+c.lower,103052431508291+c.upper)) = pointBounds25302 := by
 decide +kernel
def cuts25303 : List PrefixCut := [⟨64,249391412,249391560⟩,
⟨128,505220273,505220561⟩]
theorem checked25303 : checkPrefixCuts (2^48) 3320446977 9 Manual.Count131072.C025303.packed 128 cuts25303 = true := by
 decide +kernel
def pointBounds25303 : List (Nat × Nat × Nat) := [(3320512512,103052801493923,103053183597303)]
theorem point_links_checked25303 : (cuts25303.take 1).map (fun c => (3320446977-1+2*2^9*c.k,103052552102511+c.lower,103052934205743+c.upper)) = pointBounds25303 := by
 decide +kernel
def cuts25304 : List PrefixCut := [⟨38,152070811,152070894⟩,
⟨128,505115599,505115874⟩]
theorem checked25304 : checkPrefixCuts (2^48) 3320578049 9 Manual.Count131072.C025304.packed 128 cuts25304 = true := by
 decide +kernel
def pointBounds25304 : List (Nat × Nat × Nat) := [(3320616960,103053209393595,103053591497198)]
theorem point_links_checked25304 : (cuts25304.take 1).map (fun c => (3320578049-1+2*2^9*c.k,103053057322784+c.lower,103053439426304+c.upper)) = pointBounds25304 := by
 decide +kernel
def cuts25305 : List PrefixCut := [⟨12,49586552,49586578⟩,
⟨114,448645320,448645573⟩,
⟨128,502722409,502722695⟩]
theorem checked25305 : checkPrefixCuts (2^48) 3320709121 9 Manual.Count131072.C025305.packed 128 cuts25305 = true := by
 decide +kernel
def pointBounds25305 : List (Nat × Nat × Nat) := [(3320721408,103053612024935,103053994128756),(3320825856,103054011083703,103054393187751)]
theorem point_links_checked25305 : (cuts25305.take 2).map (fun c => (3320709121-1+2*2^9*c.k,103053562438383+c.lower,103053944542178+c.upper)) = pointBounds25305 := by
 decide +kernel
def cuts25306 : List PrefixCut := [⟨88,351834545,351834747⟩,
⟨128,510245976,510246268⟩]
theorem checked25306 : checkPrefixCuts (2^48) 3320840193 9 Manual.Count131072.C025306.packed 128 cuts25306 = true := by
 decide +kernel
def pointBounds25306 : List (Nat × Nat × Nat) := [(3320930304,103054416995337,103054799099620)]
theorem point_links_checked25306 : (cuts25306.take 1).map (fun c => (3320840193-1+2*2^9*c.k,103054065160792+c.lower,103054447264873+c.upper)) = pointBounds25306 := by
 decide +kernel
def cuts25307 : List PrefixCut := [⟨62,245453360,245453496⟩,
⟨128,508191739,508192023⟩]
theorem checked25307 : checkPrefixCuts (2^48) 3320971265 9 Manual.Count131072.C025307.packed 128 cuts25307 = true := by
 decide +kernel
def pointBounds25307 : List (Nat × Nat × Nat) := [(3321034752,103054820860128,103055202964637)]
theorem point_links_checked25307 : (cuts25307.take 1).map (fun c => (3320971265-1+2*2^9*c.k,103054575406768+c.lower,103054957511141+c.upper)) = pointBounds25307 := by
 decide +kernel
def cuts25308 : List PrefixCut := [⟨36,141283218,141283299⟩,
⟨128,505290121,505290404⟩]
theorem checked25308 : checkPrefixCuts (2^48) 3321102337 9 Manual.Count131072.C025308.packed 128 cuts25308 = true := by
 decide +kernel
def pointBounds25308 : List (Nat × Nat × Nat) := [(3321139200,103055224881725,103055606986463)]
theorem point_links_checked25308 : (cuts25308.take 1).map (fun c => (3321102337-1+2*2^9*c.k,103055083598507+c.lower,103055465703164+c.upper)) = pointBounds25308 := by
 decide +kernel
def cuts25309 : List PrefixCut := [⟨10,41527492,41527514⟩,
⟨112,444591467,444591720⟩,
⟨128,508405941,508406228⟩]
theorem checked25309 : checkPrefixCuts (2^48) 3321233409 9 Manual.Count131072.C025309.packed 128 cuts25309 = true := by
 decide +kernel
def pointBounds25309 : List (Nat × Nat × Nat) := [(3321243648,103055630416120,103056012521082),(3321348096,103056033480095,103056415585288)]
theorem point_links_checked25309 : (cuts25309.take 2).map (fun c => (3321233409-1+2*2^9*c.k,103055588888628+c.lower,103055970993568+c.upper)) = pointBounds25309 := by
 decide +kernel
def cuts25310 : List PrefixCut := [⟨86,337372433,337372627⟩,
⟨128,503724834,503725123⟩]
theorem checked25310 : checkPrefixCuts (2^48) 3321364481 9 Manual.Count131072.C025310.packed 128 cuts25310 = true := by
 decide +kernel
def pointBounds25310 : List (Nat × Nat × Nat) := [(3321452544,103056434667002,103056816772423)]
theorem point_links_checked25310 : (cuts25310.take 1).map (fun c => (3321364481-1+2*2^9*c.k,103056097294569+c.lower,103056479399796+c.upper)) = pointBounds25310 := by
 decide +kernel
def cuts25311 : List PrefixCut := [⟨60,238381066,238381198⟩,
⟨128,508535258,508535541⟩]
theorem checked25311 : checkPrefixCuts (2^48) 3321495553 9 Manual.Count131072.C025311.packed 128 cuts25311 = true := by
 decide +kernel
def pointBounds25311 : List (Nat × Nat × Nat) := [(3321556992,103056839400469,103057221506117)]
theorem point_links_checked25311 : (cuts25311.take 1).map (fun c => (3321495553-1+2*2^9*c.k,103056601019403+c.lower,103056983124919+c.upper)) = pointBounds25311 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000165
