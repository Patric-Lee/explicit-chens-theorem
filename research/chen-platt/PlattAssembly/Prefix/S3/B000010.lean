import PlattAssemblyKernel
import PlattCertificates.Count131072.C020320
import PlattCertificates.Count131072.C020321
import PlattCertificates.Count131072.C020322
import PlattCertificates.Count131072.C020323
import PlattCertificates.Count131072.C020324
import PlattCertificates.Count131072.C020325
import PlattCertificates.Count131072.C020326
import PlattCertificates.Count131072.C020327
import PlattCertificates.Count131072.C020328
import PlattCertificates.Count131072.C020329
import PlattCertificates.Count131072.C020330
import PlattCertificates.Count131072.C020331
import PlattCertificates.Count131072.C020332
import PlattCertificates.Count131072.C020333
import PlattCertificates.Count131072.C020334
import PlattCertificates.Count131072.C020335
import PlattCertificates.Count131072.C020336
import PlattCertificates.Count131072.C020337
import PlattCertificates.Count131072.C020338
import PlattCertificates.Count131072.C020339
import PlattCertificates.Count131072.C020340
import PlattCertificates.Count131072.C020341
import PlattCertificates.Count131072.C020342
import PlattCertificates.Count131072.C020343
import PlattCertificates.Count131072.C020344
import PlattCertificates.Count131072.C020345
import PlattCertificates.Count131072.C020346
import PlattCertificates.Count131072.C020347
import PlattCertificates.Count131072.C020348
import PlattCertificates.Count131072.C020349
import PlattCertificates.Count131072.C020350
import PlattCertificates.Count131072.C020351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20320 : List PrefixCut := [⟨32,158290166,158290256⟩,
⟨114,558966587,558966918⟩,
⟨128,628189360,628189731⟩]
theorem checked20320 : checkPrefixCuts (2^48) 2667315201 9 Manual.Count131072.C020320.packed 128 cuts20320 = true := by
 decide +kernel
def pointBounds20320 : List (Nat × Nat × Nat) := [(2667347968,100226583057660,100226963548079),(2667431936,100226983734081,100227364224741)]
theorem point_links_checked20320 : (cuts20320.take 2).map (fun c => (2667315201-1+2*2^9*c.k,100226424767494+c.lower,100226805257823+c.upper)) = pointBounds20320 := by
 decide +kernel
def cuts20321 : List PrefixCut := [⟨68,344314515,344314717⟩,
⟨128,639343569,639343946⟩]
theorem checked20321 : checkPrefixCuts (2^48) 2667446273 9 Manual.Count131072.C020321.packed 128 cuts20321 = true := by
 decide +kernel
def pointBounds20321 : List (Nat × Nat × Nat) := [(2667515904,100227397271369,100227777762271)]
theorem point_links_checked20321 : (cuts20321.take 1).map (fun c => (2667446273-1+2*2^9*c.k,100227052956854+c.lower,100227433447554+c.upper)) = pointBounds20321 := by
 decide +kernel
def cuts20322 : List PrefixCut := [⟨22,107732452,107732516⟩,
⟨104,513963266,513963569⟩,
⟨128,635619013,635619388⟩]
theorem checked20322 : checkPrefixCuts (2^48) 2667577345 9 Manual.Count131072.C020322.packed 128 cuts20322 = true := by
 decide +kernel
def pointBounds20322 : List (Nat × Nat × Nat) := [(2667599872,100227800032875,100228180524016),(2667683840,100228206263689,100228586755069)]
theorem point_links_checked20322 : (cuts20322.take 2).map (fun c => (2667577345-1+2*2^9*c.k,100227692300423+c.lower,100228072791500+c.upper)) = pointBounds20322 := by
 decide +kernel
def cuts20323 : List PrefixCut := [⟨58,295535439,295535611⟩,
⟨128,635377011,635377382⟩]
theorem checked20323 : checkPrefixCuts (2^48) 2667708417 9 Manual.Count131072.C020323.packed 128 cuts20323 = true := by
 decide +kernel
def pointBounds20323 : List (Nat × Nat × Nat) := [(2667767808,100228623454875,100229003946499)]
theorem point_links_checked20323 : (cuts20323.take 1).map (fun c => (2667708417-1+2*2^9*c.k,100228327919436+c.lower,100228708410888+c.upper)) = pointBounds20323 := by
 decide +kernel
def cuts20324 : List PrefixCut := [⟨12,61932282,61932318⟩,
⟨94,472133898,472134171⟩,
⟨128,641359413,641359781⟩]
theorem checked20324 : checkPrefixCuts (2^48) 2667839489 9 Manual.Count131072.C020324.packed 128 cuts20324 = true := by
 decide +kernel
def pointBounds20324 : List (Nat × Nat × Nat) := [(2667851776,100229025228729,100229405720588),(2667935744,100229435430345,100229815922441)]
theorem point_links_checked20324 : (cuts20324.take 2).map (fun c => (2667839489-1+2*2^9*c.k,100228963296447+c.lower,100229343788270+c.upper)) = pointBounds20324 := by
 decide +kernel
def cuts20325 : List PrefixCut := [⟨48,239802666,239802805⟩,
⟨128,641749791,641750161⟩]
theorem checked20325 : checkPrefixCuts (2^48) 2667970561 9 Manual.Count131072.C020325.packed 128 cuts20325 = true := by
 decide +kernel
def pointBounds20325 : List (Nat × Nat × Nat) := [(2668019712,100229844458526,100230224950856)]
theorem point_links_checked20325 : (cuts20325.take 1).map (fun c => (2667970561-1+2*2^9*c.k,100229604655860+c.lower,100229985148051+c.upper)) = pointBounds20325 := by
 decide +kernel
def cuts20326 : List PrefixCut := [⟨2,9389169,9389174⟩,
⟨84,414277328,414277566⟩,
⟨128,634755674,634756041⟩]
theorem checked20326 : checkPrefixCuts (2^48) 2668101633 9 Manual.Count131072.C020326.packed 128 cuts20326 = true := by
 decide +kernel
def pointBounds20326 : List (Nat × Nat × Nat) := [(2668103680,100230255794820,100230636287386),(2668187648,100230660682979,100231041175778)]
theorem point_links_checked20326 : (cuts20326.take 2).map (fun c => (2668101633-1+2*2^9*c.k,100230246405651+c.lower,100230626898212+c.upper)) = pointBounds20326 := by
 decide +kernel
def cuts20327 : List PrefixCut := [⟨38,189777173,189777284⟩,
⟨120,601391189,601391541⟩,
⟨128,640421051,640421424⟩]
theorem checked20327 : checkPrefixCuts (2^48) 2668232705 9 Manual.Count131072.C020327.packed 128 cuts20327 = true := by
 decide +kernel
def pointBounds20327 : List (Nat × Nat × Nat) := [(2668271616,100231070938498,100231451431537),(2668355584,100231482552514,100231863045794)]
theorem point_links_checked20327 : (cuts20327.take 2).map (fun c => (2668232705-1+2*2^9*c.k,100230881161325+c.lower,100231261654253+c.upper)) = pointBounds20327 := by
 decide +kernel
def cuts20328 : List PrefixCut := [⟨74,369828534,369828747⟩,
⟨128,644608777,644609147⟩]
theorem checked20328 : checkPrefixCuts (2^48) 2668363777 9 Manual.Count131072.C020328.packed 128 cuts20328 = true := by
 decide +kernel
def pointBounds20328 : List (Nat × Nat × Nat) := [(2668439552,100231891410910,100232271904424)]
theorem point_links_checked20328 : (cuts20328.take 1).map (fun c => (2668363777-1+2*2^9*c.k,100231521582376+c.lower,100231902075677+c.upper)) = pointBounds20328 := by
 decide +kernel
def cuts20329 : List PrefixCut := [⟨28,136596861,136596944⟩,
⟨110,549754106,549754428⟩,
⟨128,642572940,642573317⟩]
theorem checked20329 : checkPrefixCuts (2^48) 2668494849 9 Manual.Count131072.C020329.packed 128 cuts20329 = true := by
 decide +kernel
def pointBounds20329 : List (Nat × Nat × Nat) := [(2668523520,100232302788014,100232683281768),(2668607488,100232715945259,100233096439252)]
theorem point_links_checked20329 : (cuts20329.take 2).map (fun c => (2668494849-1+2*2^9*c.k,100232166191153+c.lower,100232546684824+c.upper)) = pointBounds20329 := by
 decide +kernel
def cuts20330 : List PrefixCut := [⟨64,311465627,311465809⟩,
⟨128,631150385,631150754⟩]
theorem checked20330 : checkPrefixCuts (2^48) 2668625921 9 Manual.Count131072.C020330.packed 128 cuts20330 = true := by
 decide +kernel
def pointBounds20330 : List (Nat × Nat × Nat) := [(2668691456,100233120229720,100233500723950)]
theorem point_links_checked20330 : (cuts20330.take 1).map (fun c => (2668625921-1+2*2^9*c.k,100232808764093+c.lower,100233189258141+c.upper)) = pointBounds20330 := by
 decide +kernel
def cuts20331 : List PrefixCut := [⟨18,90493297,90493349⟩,
⟨100,497916292,497916583⟩,
⟨128,637236605,637236981⟩]
theorem checked20331 : checkPrefixCuts (2^48) 2668756993 9 Manual.Count131072.C020331.packed 128 cuts20331 = true := by
 decide +kernel
def pointBounds20331 : List (Nat × Nat × Nat) := [(2668775424,100233530407775,100233910902244),(2668859392,100233937830770,100234318325478)]
theorem point_links_checked20331 : (cuts20331.take 2).map (fun c => (2668756993-1+2*2^9*c.k,100233439914478+c.lower,100233820408895+c.upper)) = pointBounds20331 := by
 decide +kernel
def cuts20332 : List PrefixCut := [⟨54,268828112,268828269⟩,
⟨128,631932208,631932579⟩]
theorem checked20332 : checkPrefixCuts (2^48) 2668888065 9 Manual.Count131072.C020332.packed 128 cuts20332 = true := by
 decide +kernel
def pointBounds20332 : List (Nat × Nat × Nat) := [(2668943360,100234345979195,100234726474145)]
theorem point_links_checked20332 : (cuts20332.take 1).map (fun c => (2668888065-1+2*2^9*c.k,100234077151083+c.lower,100234457645876+c.upper)) = pointBounds20332 := by
 decide +kernel
def cuts20333 : List PrefixCut := [⟨8,39547458,39547481⟩,
⟨90,445982820,445983082⟩,
⟨128,634326598,634326969⟩]
theorem checked20333 : checkPrefixCuts (2^48) 2669019137 9 Manual.Count131072.C020333.packed 128 cuts20333 = true := by
 decide +kernel
def pointBounds20333 : List (Nat × Nat × Nat) := [(2669027328,100234748630749,100235129125936),(2669111296,100235155066111,100235535561537)]
theorem point_links_checked20333 : (cuts20333.take 2).map (fun c => (2669019137-1+2*2^9*c.k,100234709083291+c.lower,100235089578455+c.upper)) = pointBounds20333 := by
 decide +kernel
def cuts20334 : List PrefixCut := [⟨44,218289765,218289897⟩,
⟨126,622590520,622590891⟩,
⟨128,633346393,633346771⟩]
theorem checked20334 : checkPrefixCuts (2^48) 2669150209 9 Manual.Count131072.C020334.packed 128 cuts20334 = true := by
 decide +kernel
def pointBounds20334 : List (Nat × Nat × Nat) := [(2669195264,100235561699654,100235942195321),(2669279232,100235966000409,100236346496315)]
theorem point_links_checked20334 : (cuts20334.take 2).map (fun c => (2669150209-1+2*2^9*c.k,100235343409889+c.lower,100235723905424+c.upper)) = pointBounds20334 := by
 decide +kernel
def cuts20335 : List PrefixCut := [⟨80,396168394,396168625⟩,
⟨128,642067280,642067653⟩]
theorem checked20335 : checkPrefixCuts (2^48) 2669281281 9 Manual.Count131072.C020335.packed 128 cuts20335 = true := by
 decide +kernel
def pointBounds20335 : List (Nat × Nat × Nat) := [(2669363200,100236372924676,100236753420820)]
theorem point_links_checked20335 : (cuts20335.take 1).map (fun c => (2669281281-1+2*2^9*c.k,100235976756282+c.lower,100236357252195+c.upper)) = pointBounds20335 := by
 decide +kernel
def cuts20336 : List PrefixCut := [⟨34,169342779,169342881⟩,
⟨116,567278885,567279221⟩,
⟨128,626641371,626641743⟩]
theorem checked20336 : checkPrefixCuts (2^48) 2669412353 9 Manual.Count131072.C020336.packed 128 cuts20336 = true := by
 decide +kernel
def pointBounds20336 : List (Nat × Nat × Nat) := [(2669447168,100236788166341,100237168662729),(2669531136,100237186102447,100237566599069)]
theorem point_links_checked20336 : (cuts20336.take 2).map (fun c => (2669412353-1+2*2^9*c.k,100236618823562+c.lower,100236999319848+c.upper)) = pointBounds20336 := by
 decide +kernel
def cuts20337 : List PrefixCut := [⟨70,346996239,346996441⟩,
⟨128,638314062,638314437⟩]
theorem checked20337 : checkPrefixCuts (2^48) 2669543425 9 Manual.Count131072.C020337.packed 128 cuts20337 = true := by
 decide +kernel
def pointBounds20337 : List (Nat × Nat × Nat) := [(2669615104,100237592461172,100237972958032)]
theorem point_links_checked20337 : (cuts20337.take 1).map (fun c => (2669543425-1+2*2^9*c.k,100237245464933+c.lower,100237625961591+c.upper)) = pointBounds20337 := by
 decide +kernel
def cuts20338 : List PrefixCut := [⟨24,117874850,117874918⟩,
⟨106,531271904,531272209⟩,
⟨128,641129380,641129747⟩]
theorem checked20338 : checkPrefixCuts (2^48) 2669674497 9 Manual.Count131072.C020338.packed 128 cuts20338 = true := by
 decide +kernel
def pointBounds20338 : List (Nat × Nat × Nat) := [(2669699072,100238001653845,100238382150946),(2669783040,100238415050899,100238795548237)]
theorem point_links_checked20338 : (cuts20338.take 2).map (fun c => (2669674497-1+2*2^9*c.k,100237883778995+c.lower,100238264276028+c.upper)) = pointBounds20338 := by
 decide +kernel
def cuts20339 : List PrefixCut := [⟨60,296673740,296673913⟩,
⟨128,636775396,636775763⟩]
theorem checked20339 : checkPrefixCuts (2^48) 2669805569 9 Manual.Count131072.C020339.packed 128 cuts20339 = true := by
 decide +kernel
def pointBounds20339 : List (Nat × Nat × Nat) := [(2669867008,100238821582115,100239202079688)]
theorem point_links_checked20339 : (cuts20339.take 1).map (fun c => (2669805569-1+2*2^9*c.k,100238524908375+c.lower,100238905405775+c.upper)) = pointBounds20339 := by
 decide +kernel
def cuts20340 : List PrefixCut := [⟨14,71160878,71160918⟩,
⟨96,480829177,480829450⟩,
⟨128,638325586,638325951⟩]
theorem checked20340 : checkPrefixCuts (2^48) 2669936641 9 Manual.Count131072.C020340.packed 128 cuts20340 = true := by
 decide +kernel
def pointBounds20340 : List (Nat × Nat × Nat) := [(2669950976,100239232844649,100239613342456),(2670034944,100239642512948,100240023010988)]
theorem point_links_checked20340 : (cuts20340.take 2).map (fun c => (2669936641-1+2*2^9*c.k,100239161683771+c.lower,100239542181538+c.upper)) = pointBounds20340 := by
 decide +kernel
def cuts20341 : List PrefixCut := [⟨50,256481081,256481226⟩,
⟨128,645778781,645779153⟩]
theorem checked20341 : checkPrefixCuts (2^48) 2670067713 9 Manual.Count131072.C020341.packed 128 cuts20341 = true := by
 decide +kernel
def pointBounds20341 : List (Nat × Nat × Nat) := [(2670118912,100240056490438,100240436988715)]
theorem point_links_checked20341 : (cuts20341.take 1).map (fun c => (2670067713-1+2*2^9*c.k,100239800009357+c.lower,100240180507489+c.upper)) = pointBounds20341 := by
 decide +kernel
def cuts20342 : List PrefixCut := [⟨4,20555609,20555621⟩,
⟨86,429763636,429763883⟩,
⟨128,638473739,638474105⟩]
theorem checked20342 : checkPrefixCuts (2^48) 2670198785 9 Manual.Count131072.C020342.packed 128 cuts20342 = true := by
 decide +kernel
def pointBounds20342 : List (Nat × Nat × Nat) := [(2670202880,100240466343747,100240846842263),(2670286848,100240875551774,100241256050525)]
theorem point_links_checked20342 : (cuts20342.take 2).map (fun c => (2670198785-1+2*2^9*c.k,100240445788138+c.lower,100240826286642+c.upper)) = pointBounds20342 := by
 decide +kernel
def cuts20343 : List PrefixCut := [⟨40,202487764,202487883⟩,
⟨122,603764611,603764969⟩,
⟨128,632434289,632434664⟩]
theorem checked20343 : checkPrefixCuts (2^48) 2670329857 9 Manual.Count131072.C020343.packed 128 cuts20343 = true := by
 decide +kernel
def pointBounds20343 : List (Nat × Nat × Nat) := [(2670370816,100241286749641,100241667248630),(2670454784,100241688026488,100242068525716)]
theorem point_links_checked20343 : (cuts20343.take 2).map (fun c => (2670329857-1+2*2^9*c.k,100241084261877+c.lower,100241464760747+c.upper)) = pointBounds20343 := by
 decide +kernel
def cuts20344 : List PrefixCut := [⟨76,376494440,376494661⟩,
⟨128,637040742,637041110⟩]
theorem checked20344 : checkPrefixCuts (2^48) 2670460929 9 Manual.Count131072.C020344.packed 128 cuts20344 = true := by
 decide +kernel
def pointBounds20344 : List (Nat × Nat × Nat) := [(2670538752,100242093190606,100242473690072)]
theorem point_links_checked20344 : (cuts20344.take 1).map (fun c => (2670460929-1+2*2^9*c.k,100241716696166+c.lower,100242097195411+c.upper)) = pointBounds20344 := by
 decide +kernel
def cuts20345 : List PrefixCut := [⟨30,145448308,145448395⟩,
⟨112,558913184,558913516⟩,
⟨128,636693288,636693665⟩]
theorem checked20345 : checkPrefixCuts (2^48) 2670592001 9 Manual.Count131072.C020345.packed 128 cuts20345 = true := by
 decide +kernel
def pointBounds20345 : List (Nat × Nat × Nat) := [(2670622720,100242499185216,100242879684916),(2670706688,100242912650092,100243293150037)]
theorem point_links_checked20345 : (cuts20345.take 2).map (fun c => (2670592001-1+2*2^9*c.k,100242353736908+c.lower,100242734236521+c.upper)) = pointBounds20345 := by
 decide +kernel
def cuts20346 : List PrefixCut := [⟨66,324184064,324184255⟩,
⟨128,628230924,628231294⟩]
theorem checked20346 : checkPrefixCuts (2^48) 2670723073 9 Manual.Count131072.C020346.packed 128 cuts20346 = true := by
 decide +kernel
def pointBounds20346 : List (Nat × Nat × Nat) := [(2670790656,100243314614260,100243695114441)]
theorem point_links_checked20346 : (cuts20346.take 1).map (fun c => (2670723073-1+2*2^9*c.k,100242990430196+c.lower,100243370930186+c.upper)) = pointBounds20346 := by
 decide +kernel
def cuts20347 : List PrefixCut := [⟨20,101487874,101487932⟩,
⟨102,512911420,512911714⟩,
⟨128,637474066,637474433⟩]
theorem checked20347 : checkPrefixCuts (2^48) 2670854145 9 Manual.Count131072.C020347.packed 128 cuts20347 = true := by
 decide +kernel
def pointBounds20347 : List (Nat × Nat × Nat) := [(2670874624,100243720148994,100244100649412),(2670958592,100244131572540,100244512073194)]
theorem point_links_checked20347 : (cuts20347.take 2).map (fun c => (2670854145-1+2*2^9*c.k,100243618661120+c.lower,100243999161480+c.upper)) = pointBounds20347 := by
 decide +kernel
def cuts20348 : List PrefixCut := [⟨56,285056402,285056569⟩,
⟨128,642184845,642185219⟩]
theorem checked20348 : checkPrefixCuts (2^48) 2670985217 9 Manual.Count131072.C020348.packed 128 cuts20348 = true := by
 decide +kernel
def pointBounds20348 : List (Nat × Nat × Nat) := [(2671042560,100244541191588,100244921692482)]
theorem point_links_checked20348 : (cuts20348.take 1).map (fun c => (2670985217-1+2*2^9*c.k,100244256135186+c.lower,100244636635913+c.upper)) = pointBounds20348 := by
 decide +kernel
def cuts20349 : List PrefixCut := [⟨10,49105702,49105732⟩,
⟨92,455221669,455221940⟩,
⟨128,634039301,634039678⟩]
theorem checked20349 : checkPrefixCuts (2^48) 2671116289 9 Manual.Count131072.C020349.packed 128 cuts20349 = true := by
 decide +kernel
def pointBounds20349 : List (Nat × Nat × Nat) := [(2671126528,100244947425733,100245327926864),(2671210496,100245353541700,100245734043072)]
theorem point_links_checked20349 : (cuts20349.take 2).map (fun c => (2671116289-1+2*2^9*c.k,100244898320031+c.lower,100245278821132+c.upper)) = pointBounds20349 := by
 decide +kernel
def cuts20350 : List PrefixCut := [⟨46,230657472,230657612⟩,
⟨128,639066065,639066443⟩]
theorem checked20350 : checkPrefixCuts (2^48) 2671247361 9 Manual.Count131072.C020350.packed 128 cuts20350 = true := by
 decide +kernel
def pointBounds20350 : List (Nat × Nat × Nat) := [(2671294464,100245763016804,100246143518422),(2671378432,100246171425397,100246551927253)]
theorem point_links_checked20350 : (cuts20350.take 2).map (fun c => (2671247361-1+2*2^9*c.k,100245532359332+c.lower,100245912860810+c.upper)) = pointBounds20350 := by
 decide +kernel
def cuts20351 : List PrefixCut := [⟨82,409449399,409449640⟩,
⟨128,641141933,641142308⟩]
theorem checked20351 : checkPrefixCuts (2^48) 2671378433 9 Manual.Count131072.C020351.packed 128 cuts20351 = true := by
 decide +kernel
def pointBounds20351 : List (Nat × Nat × Nat) := [(2671462400,100246580874796,100246961376893)]
theorem point_links_checked20351 : (cuts20351.take 1).map (fun c => (2671378433-1+2*2^9*c.k,100246171425397+c.lower,100246551927253+c.upper)) = pointBounds20351 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000010
