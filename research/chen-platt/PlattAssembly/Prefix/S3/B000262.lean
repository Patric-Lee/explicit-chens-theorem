import PlattAssemblyKernel
import PlattCertificates.Count131072.C028384
import PlattCertificates.Count131072.C028385
import PlattCertificates.Count131072.C028386
import PlattCertificates.Count131072.C028387
import PlattCertificates.Count131072.C028388
import PlattCertificates.Count131072.C028389
import PlattCertificates.Count131072.C028390
import PlattCertificates.Count131072.C028391
import PlattCertificates.Count131072.C028392
import PlattCertificates.Count131072.C028393
import PlattCertificates.Count131072.C028394
import PlattCertificates.Count131072.C028395
import PlattCertificates.Count131072.C028396
import PlattCertificates.Count131072.C028397
import PlattCertificates.Count131072.C028398
import PlattCertificates.Count131072.C028399
import PlattCertificates.Count131072.C028400
import PlattCertificates.Count131072.C028401
import PlattCertificates.Count131072.C028402
import PlattCertificates.Count131072.C028403
import PlattCertificates.Count131072.C028404
import PlattCertificates.Count131072.C028405
import PlattCertificates.Count131072.C028406
import PlattCertificates.Count131072.C028407
import PlattCertificates.Count131072.C028408
import PlattCertificates.Count131072.C028409
import PlattCertificates.Count131072.C028410
import PlattCertificates.Count131072.C028411
import PlattCertificates.Count131072.C028412
import PlattCertificates.Count131072.C028413
import PlattCertificates.Count131072.C028414
import PlattCertificates.Count131072.C028415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000262
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28384 : List PrefixCut := [⟨87,301856270,301856439⟩,
⟨128,443788207,443788456⟩]
theorem checked28384 : checkPrefixCuts (2^48) 3724279809 9 Manual.Count131072.C028384.packed 128 cuts28384 = true := by
 decide +kernel
def pointBounds28384 : List (Nat × Nat × Nat) := [(3724368896,104522720899647,104523103825604)]
theorem point_links_checked28384 : (cuts28384.take 1).map (fun c => (3724279809-1+2*2^9*c.k,104522419043377+c.lower,104522801969165+c.upper)) = pointBounds28384 := by
 decide +kernel
def cuts28385 : List PrefixCut := [⟨73,258692963,258693109⟩,
⟨128,451783523,451783776⟩]
theorem checked28385 : checkPrefixCuts (2^48) 3724410881 9 Manual.Count131072.C028385.packed 128 cuts28385 = true := by
 decide +kernel
def pointBounds28385 : List (Nat × Nat × Nat) := [(3724485632,104523121524547,104523504450730)]
theorem point_links_checked28385 : (cuts28385.take 1).map (fun c => (3724410881-1+2*2^9*c.k,104522862831584+c.lower,104523245757621+c.upper)) = pointBounds28385 := by
 decide +kernel
def cuts28386 : List PrefixCut := [⟨59,207143971,207144088⟩,
⟨128,449575997,449576249⟩]
theorem checked28386 : checkPrefixCuts (2^48) 3724541953 9 Manual.Count131072.C028386.packed 128 cuts28386 = true := by
 decide +kernel
def pointBounds28386 : List (Nat × Nat × Nat) := [(3724602368,104523521759078,104523904685485)]
theorem point_links_checked28386 : (cuts28386.take 1).map (fun c => (3724541953-1+2*2^9*c.k,104523314615107+c.lower,104523697541397+c.upper)) = pointBounds28386 := by
 decide +kernel
def cuts28387 : List PrefixCut := [⟨45,156278535,156278621⟩,
⟨128,453489704,453489952⟩]
theorem checked28387 : checkPrefixCuts (2^48) 3724673025 9 Manual.Count131072.C028387.packed 128 cuts28387 = true := by
 decide +kernel
def pointBounds28387 : List (Nat × Nat × Nat) := [(3724719104,104523920469639,104524303396267)]
theorem point_links_checked28387 : (cuts28387.take 1).map (fun c => (3724673025-1+2*2^9*c.k,104523764191104+c.lower,104524147117646+c.upper)) = pointBounds28387 := by
 decide +kernel
def cuts28388 : List PrefixCut := [⟨31,111537456,111537519⟩,
⟨128,454607327,454607584⟩]
theorem checked28388 : checkPrefixCuts (2^48) 3724804097 9 Manual.Count131072.C028388.packed 128 cuts28388 = true := by
 decide +kernel
def pointBounds28388 : List (Nat × Nat × Nat) := [(3724835840,104524329218264,104524712145117)]
theorem point_links_checked28388 : (cuts28388.take 1).map (fun c => (3724804097-1+2*2^9*c.k,104524217680808+c.lower,104524600607598+c.upper)) = pointBounds28388 := by
 decide +kernel
def cuts28389 : List PrefixCut := [⟨17,60527460,60527493⟩,
⟨128,446354891,446355146⟩]
theorem checked28389 : checkPrefixCuts (2^48) 3724935169 9 Manual.Count131072.C028389.packed 128 cuts28389 = true := by
 decide +kernel
def pointBounds28389 : List (Nat × Nat × Nat) := [(3724952576,104524732815595,104525115742675)]
theorem point_links_checked28389 : (cuts28389.take 1).map (fun c => (3724935169-1+2*2^9*c.k,104524672288135+c.lower,104525055215182+c.upper)) = pointBounds28389 := by
 decide +kernel
def cuts28390 : List PrefixCut := [⟨3,11032104,11032110⟩,
⟨117,407199171,407199398⟩,
⟨128,444601294,444601543⟩]
theorem checked28390 : checkPrefixCuts (2^48) 3725066241 9 Manual.Count131072.C028390.packed 128 cuts28390 = true := by
 decide +kernel
def pointBounds28390 : List (Nat × Nat × Nat) := [(3725069312,104525129675130,104525512602438),(3725186048,104525525842197,104525908769726)]
theorem point_links_checked28390 : (cuts28390.take 2).map (fun c => (3725066241-1+2*2^9*c.k,104525118643026+c.lower,104525501570328+c.upper)) = pointBounds28390 := by
 decide +kernel
def cuts28391 : List PrefixCut := [⟨103,361094792,361094991⟩,
⟨128,449043528,449043776⟩]
theorem checked28391 : checkPrefixCuts (2^48) 3725197313 9 Manual.Count131072.C028391.packed 128 cuts28391 = true := by
 decide +kernel
def pointBounds28391 : List (Nat × Nat × Nat) := [(3725302784,104525924339112,104526307266862)]
theorem point_links_checked28391 : (cuts28391.take 1).map (fun c => (3725197313-1+2*2^9*c.k,104525563244320+c.lower,104525946171871+c.upper)) = pointBounds28391 := by
 decide +kernel
def cuts28392 : List PrefixCut := [⟨89,310838021,310838197⟩,
⟨128,451521087,451521338⟩]
theorem checked28392 : checkPrefixCuts (2^48) 3725328385 9 Manual.Count131072.C028392.packed 128 cuts28392 = true := by
 decide +kernel
def pointBounds28392 : List (Nat × Nat × Nat) := [(3725419520,104526323125869,104526706053844)]
theorem point_links_checked28392 : (cuts28392.take 1).map (fun c => (3725328385-1+2*2^9*c.k,104526012287848+c.lower,104526395215647+c.upper)) = pointBounds28392 := by
 decide +kernel
def cuts28393 : List PrefixCut := [⟨75,268593159,268593310⟩,
⟨128,457473935,457474192⟩]
theorem checked28393 : checkPrefixCuts (2^48) 3725459457 9 Manual.Count131072.C028393.packed 128 cuts28393 = true := by
 decide +kernel
def pointBounds28393 : List (Nat × Nat × Nat) := [(3725536256,104526732402094,104527115330295)]
theorem point_links_checked28393 : (cuts28393.take 1).map (fun c => (3725459457-1+2*2^9*c.k,104526463808935+c.lower,104526846736985+c.upper)) = pointBounds28393 := by
 decide +kernel
def cuts28394 : List PrefixCut := [⟨61,215925083,215925205⟩,
⟨128,447938526,447938778⟩]
theorem checked28394 : checkPrefixCuts (2^48) 3725590529 9 Manual.Count131072.C028394.packed 128 cuts28394 = true := by
 decide +kernel
def pointBounds28394 : List (Nat × Nat × Nat) := [(3725652992,104527137207953,104527520136382)]
theorem point_links_checked28394 : (cuts28394.take 1).map (fun c => (3725590529-1+2*2^9*c.k,104526921282870+c.lower,104527304211177+c.upper)) = pointBounds28394 := by
 decide +kernel
def cuts28395 : List PrefixCut := [⟨47,164016018,164016107⟩,
⟨128,449811402,449811652⟩]
theorem checked28395 : checkPrefixCuts (2^48) 3725721601 9 Manual.Count131072.C028395.packed 128 cuts28395 = true := by
 decide +kernel
def pointBounds28395 : List (Nat × Nat × Nat) := [(3725769728,104527533237414,104527916166062)]
theorem point_links_checked28395 : (cuts28395.take 1).map (fun c => (3725721601-1+2*2^9*c.k,104527369221396+c.lower,104527752149955+c.upper)) = pointBounds28395 := by
 decide +kernel
def cuts28396 : List PrefixCut := [⟨33,115585522,115585587⟩,
⟨128,448133588,448133838⟩]
theorem checked28396 : checkPrefixCuts (2^48) 3725852673 9 Manual.Count131072.C028396.packed 128 cuts28396 = true := by
 decide +kernel
def pointBounds28396 : List (Nat × Nat × Nat) := [(3725886464,104527934618320,104528317547194)]
theorem point_links_checked28396 : (cuts28396.take 1).map (fun c => (3725852673-1+2*2^9*c.k,104527819032798+c.lower,104528201961607+c.upper)) = pointBounds28396 := by
 decide +kernel
def cuts28397 : List PrefixCut := [⟨19,65798463,65798500⟩,
⟨128,448646598,448646854⟩]
theorem checked28397 : checkPrefixCuts (2^48) 3725983745 9 Manual.Count131072.C028397.packed 128 cuts28397 = true := by
 decide +kernel
def pointBounds28397 : List (Nat × Nat × Nat) := [(3726003200,104528332964849,104528715893945)]
theorem point_links_checked28397 : (cuts28397.take 1).map (fun c => (3725983745-1+2*2^9*c.k,104528267166386+c.lower,104528650095445+c.upper)) = pointBounds28397 := by
 decide +kernel
def cuts28398 : List PrefixCut := [⟨5,16996741,16996752⟩,
⟨119,416678012,416678244⟩,
⟨128,447422205,447422456⟩]
theorem checked28398 : checkPrefixCuts (2^48) 3726114817 9 Manual.Count131072.C028398.packed 128 cuts28398 = true := by
 decide +kernel
def pointBounds28398 : List (Nat × Nat × Nat) := [(3726119936,104528732809725,104529115739051),(3726236672,104529132490996,104529515420543)]
theorem point_links_checked28398 : (cuts28398.take 2).map (fun c => (3726114817-1+2*2^9*c.k,104528715812984+c.lower,104529098742299+c.upper)) = pointBounds28398 := by
 decide +kernel
def cuts28399 : List PrefixCut := [⟨105,369755461,369755666⟩,
⟨128,450050280,450050529⟩]
theorem checked28399 : checkPrefixCuts (2^48) 3726245889 9 Manual.Count131072.C028399.packed 128 cuts28399 = true := by
 decide +kernel
def pointBounds28399 : List (Nat × Nat × Nat) := [(3726353408,104529532990650,104529915920421)]
theorem point_links_checked28399 : (cuts28399.take 1).map (fun c => (3726245889-1+2*2^9*c.k,104529163235189+c.lower,104529546164755+c.upper)) = pointBounds28399 := by
 decide +kernel
def cuts28400 : List PrefixCut := [⟨91,320116773,320116957⟩,
⟨128,450412111,450412368⟩]
theorem checked28400 : checkPrefixCuts (2^48) 3726376961 9 Manual.Count131072.C028400.packed 128 cuts28400 = true := by
 decide +kernel
def pointBounds28400 : List (Nat × Nat × Nat) := [(3726470144,104529933402242,104530316332241)]
theorem point_links_checked28400 : (cuts28400.take 1).map (fun c => (3726376961-1+2*2^9*c.k,104529613285469+c.lower,104529996215284+c.upper)) = pointBounds28400 := by
 decide +kernel
def cuts28401 : List PrefixCut := [⟨77,266780249,266780398⟩,
⟨128,449263183,449263432⟩]
theorem checked28401 : checkPrefixCuts (2^48) 3726508033 9 Manual.Count131072.C028401.packed 128 cuts28401 = true := by
 decide +kernel
def pointBounds28401 : List (Nat × Nat × Nat) := [(3726586880,104530330477829,104530713408050)]
theorem point_links_checked28401 : (cuts28401.take 1).map (fun c => (3726508033-1+2*2^9*c.k,104530063697580+c.lower,104530446627652+c.upper)) = pointBounds28401 := by
 decide +kernel
def cuts28402 : List PrefixCut := [⟨63,215562172,215562292⟩,
⟨128,445999684,445999935⟩]
theorem checked28402 : checkPrefixCuts (2^48) 3726639105 9 Manual.Count131072.C028402.packed 128 cuts28402 = true := by
 decide +kernel
def pointBounds28402 : List (Nat × Nat × Nat) := [(3726703616,104530728522935,104531111453376)]
theorem point_links_checked28402 : (cuts28402.take 1).map (fun c => (3726639105-1+2*2^9*c.k,104530512960763+c.lower,104530895891084+c.upper)) = pointBounds28402 := by
 decide +kernel
def cuts28403 : List PrefixCut := [⟨49,172428906,172429002⟩,
⟨128,446588326,446588576⟩]
theorem checked28403 : checkPrefixCuts (2^48) 3726770177 9 Manual.Count131072.C028403.packed 128 cuts28403 = true := by
 decide +kernel
def pointBounds28403 : List (Nat × Nat × Nat) := [(3726820352,104531131389353,104531514320021)]
theorem point_links_checked28403 : (cuts28403.take 1).map (fun c => (3726770177-1+2*2^9*c.k,104530958960447+c.lower,104531341891019+c.upper)) = pointBounds28403 := by
 decide +kernel
def cuts28404 : List PrefixCut := [⟨35,120386553,120386623⟩,
⟨128,447327749,447328004⟩]
theorem checked28404 : checkPrefixCuts (2^48) 3726901249 9 Manual.Count131072.C028404.packed 128 cuts28404 = true := by
 decide +kernel
def pointBounds28404 : List (Nat × Nat × Nat) := [(3726937088,104531525935326,104531908866218)]
theorem point_links_checked28404 : (cuts28404.take 1).map (fun c => (3726901249-1+2*2^9*c.k,104531405548773+c.lower,104531788479595+c.upper)) = pointBounds28404 := by
 decide +kernel
def cuts28405 : List PrefixCut := [⟨21,71066490,71066529⟩,
⟨128,446783365,446783609⟩]
theorem checked28405 : checkPrefixCuts (2^48) 3727032321 9 Manual.Count131072.C028405.packed 128 cuts28405 = true := by
 decide +kernel
def pointBounds28405 : List (Nat × Nat × Nat) := [(3727053824,104531923943012,104532306874128)]
theorem point_links_checked28405 : (cuts28405.take 1).map (fun c => (3727032321-1+2*2^9*c.k,104531852876522+c.lower,104532235807599+c.upper)) = pointBounds28405 := by
 decide +kernel
def cuts28406 : List PrefixCut := [⟨7,23562179,23562191⟩,
⟨121,421393785,421394021⟩,
⟨128,446616559,446616809⟩]
theorem checked28406 : checkPrefixCuts (2^48) 3727163393 9 Manual.Count131072.C028406.packed 128 cuts28406 = true := by
 decide +kernel
def pointBounds28406 : List (Nat × Nat × Nat) := [(3727170560,104532323222066,104532706153399),(3727287296,104532721053672,104533103985229)]
theorem point_links_checked28406 : (cuts28406.take 2).map (fun c => (3727163393-1+2*2^9*c.k,104532299659887+c.lower,104532682591208+c.upper)) = pointBounds28406 := by
 decide +kernel
def cuts28407 : List PrefixCut := [⟨107,379015299,379015512⟩,
⟨128,449772648,449772898⟩]
theorem checked28407 : checkPrefixCuts (2^48) 3727294465 9 Manual.Count131072.C028407.packed 128 cuts28407 = true := by
 decide +kernel
def pointBounds28407 : List (Nat × Nat × Nat) := [(3727404032,104533125291745,104533508223529)]
theorem point_links_checked28407 : (cuts28407.take 1).map (fun c => (3727294465-1+2*2^9*c.k,104532746276446+c.lower,104533129208017+c.upper)) = pointBounds28407 := by
 decide +kernel
def cuts28408 : List PrefixCut := [⟨93,331655667,331655852⟩,
⟨128,452701839,452702092⟩]
theorem checked28408 : checkPrefixCuts (2^48) 3727425537 9 Manual.Count131072.C028408.packed 128 cuts28408 = true := by
 decide +kernel
def pointBounds28408 : List (Nat × Nat × Nat) := [(3727520768,104533527704761,104533910636767)]
theorem point_links_checked28408 : (cuts28408.take 1).map (fun c => (3727425537-1+2*2^9*c.k,104533196049094+c.lower,104533578980915+c.upper)) = pointBounds28408 := by
 decide +kernel
def cuts28409 : List PrefixCut := [⟨79,275464420,275464577⟩,
⟨128,448306239,448306491⟩]
theorem checked28409 : checkPrefixCuts (2^48) 3727556609 9 Manual.Count131072.C028409.packed 128 cuts28409 = true := by
 decide +kernel
def pointBounds28409 : List (Nat × Nat × Nat) := [(3727637504,104533924215353,104534307147584)]
theorem point_links_checked28409 : (cuts28409.take 1).map (fun c => (3727556609-1+2*2^9*c.k,104533648750933+c.lower,104534031683007+c.upper)) = pointBounds28409 := by
 decide +kernel
def cuts28410 : List PrefixCut := [⟨65,222674780,222674907⟩,
⟨128,441796807,441797057⟩]
theorem checked28410 : checkPrefixCuts (2^48) 3727687681 9 Manual.Count131072.C028410.packed 128 cuts28410 = true := by
 decide +kernel
def pointBounds28410 : List (Nat × Nat × Nat) := [(3727754240,104534319731952,104534702664405)]
theorem point_links_checked28410 : (cuts28410.take 1).map (fun c => (3727687681-1+2*2^9*c.k,104534097057172+c.lower,104534479989498+c.upper)) = pointBounds28410 := by
 decide +kernel
def cuts28411 : List PrefixCut := [⟨51,180988047,180988148⟩,
⟨128,445632141,445632388⟩]
theorem checked28411 : checkPrefixCuts (2^48) 3727818753 9 Manual.Count131072.C028411.packed 128 cuts28411 = true := by
 decide +kernel
def pointBounds28411 : List (Nat × Nat × Nat) := [(3727870976,104534719842026,104535102774703)]
theorem point_links_checked28411 : (cuts28411.take 1).map (fun c => (3727818753-1+2*2^9*c.k,104534538853979+c.lower,104534921786555+c.upper)) = pointBounds28411 := by
 decide +kernel
def cuts28412 : List PrefixCut := [⟨37,130319139,130319210⟩,
⟨128,451505626,451505878⟩]
theorem checked28412 : checkPrefixCuts (2^48) 3727949825 9 Manual.Count131072.C028412.packed 128 cuts28412 = true := by
 decide +kernel
def pointBounds28412 : List (Nat × Nat × Nat) := [(3727987712,104535114805259,104535497738153)]
theorem point_links_checked28412 : (cuts28412.take 1).map (fun c => (3727949825-1+2*2^9*c.k,104534984486120+c.lower,104535367418943+c.upper)) = pointBounds28412 := by
 decide +kernel
def cuts28413 : List PrefixCut := [⟨23,79955610,79955655⟩,
⟨128,445525251,445525499⟩]
theorem checked28413 : checkPrefixCuts (2^48) 3728080897 9 Manual.Count131072.C028413.packed 128 cuts28413 = true := by
 decide +kernel
def pointBounds28413 : List (Nat × Nat × Nat) := [(3728104448,104535515947356,104535898880476)]
theorem point_links_checked28413 : (cuts28413.take 1).map (fun c => (3728080897-1+2*2^9*c.k,104535435991746+c.lower,104535818924821+c.upper)) = pointBounds28413 := by
 decide +kernel
def cuts28414 : List PrefixCut := [⟨9,32841863,32841881⟩,
⟨123,433807807,433808053⟩,
⟨128,451020900,451021157⟩]
theorem checked28414 : checkPrefixCuts (2^48) 3728211969 9 Manual.Count131072.C028414.packed 128 cuts28414 = true := by
 decide +kernel
def pointBounds28414 : List (Nat × Nat × Nat) := [(3728221184,104535914358860,104536297292201),(3728337920,104536315324804,104536698258373)]
theorem point_links_checked28414 : (cuts28414.take 2).map (fun c => (3728211969-1+2*2^9*c.k,104535881516997+c.lower,104536264450320+c.upper)) = pointBounds28414 := by
 decide +kernel
def cuts28415 : List PrefixCut := [⟨109,377398761,377398970⟩,
⟨128,448362666,448362915⟩]
theorem checked28415 : checkPrefixCuts (2^48) 3728343041 9 Manual.Count131072.C028415.packed 128 cuts28415 = true := by
 decide +kernel
def pointBounds28415 : List (Nat × Nat × Nat) := [(3728454656,104536709936658,104537092870447)]
theorem point_links_checked28415 : (cuts28415.take 1).map (fun c => (3728343041-1+2*2^9*c.k,104536332537897+c.lower,104536715471477+c.upper)) = pointBounds28415 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000262
