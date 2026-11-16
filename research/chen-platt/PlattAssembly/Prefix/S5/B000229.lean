import PlattAssemblyKernel
import PlattCertificates.Count131072.C047328
import PlattCertificates.Count131072.C047329
import PlattCertificates.Count131072.C047330
import PlattCertificates.Count131072.C047331
import PlattCertificates.Count131072.C047332
import PlattCertificates.Count131072.C047333
import PlattCertificates.Count131072.C047334
import PlattCertificates.Count131072.C047335
import PlattCertificates.Count131072.C047336
import PlattCertificates.Count131072.C047337
import PlattCertificates.Count131072.C047338
import PlattCertificates.Count131072.C047339
import PlattCertificates.Count131072.C047340
import PlattCertificates.Count131072.C047341
import PlattCertificates.Count131072.C047342
import PlattCertificates.Count131072.C047343
import PlattCertificates.Count131072.C047344
import PlattCertificates.Count131072.C047345
import PlattCertificates.Count131072.C047346
import PlattCertificates.Count131072.C047347
import PlattCertificates.Count131072.C047348
import PlattCertificates.Count131072.C047349
import PlattCertificates.Count131072.C047350
import PlattCertificates.Count131072.C047351
import PlattCertificates.Count131072.C047352
import PlattCertificates.Count131072.C047353
import PlattCertificates.Count131072.C047354
import PlattCertificates.Count131072.C047355
import PlattCertificates.Count131072.C047356
import PlattCertificates.Count131072.C047357
import PlattCertificates.Count131072.C047358
import PlattCertificates.Count131072.C047359
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000229
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts47328 : List PrefixCut := [⟨64,261188651,261188801⟩]
theorem checked47328 : checkPrefixCuts (2^48) 6207307777 10 Manual.Count131072.C047328.packed 64 cuts47328 = true := by
 decide +kernel
def cuts47329 : List PrefixCut := [⟨15,61714081,61714116⟩,
⟨64,263450342,263450493⟩]
theorem checked47329 : checkPrefixCuts (2^48) 6207438849 10 Manual.Count131072.C047329.packed 64 cuts47329 = true := by
 decide +kernel
def pointBounds47329 : List (Nat × Nat × Nat) := [(6207469568,110972916570325,110973303301680)]
theorem point_links_checked47329 : (cuts47329.take 1).map (fun c => (6207438849-1+2*2^10*c.k,110972854856244+c.lower,110973241587564+c.upper)) = pointBounds47329 := by
 decide +kernel
def cuts47330 : List PrefixCut := [⟨46,186089591,186089696⟩,
⟨64,260270725,260270872⟩]
theorem checked47330 : checkPrefixCuts (2^48) 6207569921 10 Manual.Count131072.C047330.packed 64 cuts47330 = true := by
 decide +kernel
def pointBounds47330 : List (Nat × Nat × Nat) := [(6207664128,110973304396177,110973691127753)]
theorem point_links_checked47330 : (cuts47330.take 1).map (fun c => (6207569921-1+2*2^10*c.k,110973118306586+c.lower,110973505038057+c.upper)) = pointBounds47330 := by
 decide +kernel
def cuts47331 : List PrefixCut := [⟨64,263756605,263756752⟩]
theorem checked47331 : checkPrefixCuts (2^48) 6207700993 10 Manual.Count131072.C047331.packed 64 cuts47331 = true := by
 decide +kernel
def cuts47332 : List PrefixCut := [⟨13,53911403,53911432⟩,
⟨64,263297646,263297798⟩]
theorem checked47332 : checkPrefixCuts (2^48) 6207832065 10 Manual.Count131072.C047332.packed 64 cuts47332 = true := by
 decide +kernel
def pointBounds47332 : List (Nat × Nat × Nat) := [(6207858688,110973696245319,110974082977113)]
theorem point_links_checked47332 : (cuts47332.take 1).map (fun c => (6207832065-1+2*2^10*c.k,110973642333916+c.lower,110974029065681+c.upper)) = pointBounds47332 := by
 decide +kernel
def cuts47333 : List PrefixCut := [⟨44,178914053,178914152⟩,
⟨64,260843673,260843821⟩]
theorem checked47333 : checkPrefixCuts (2^48) 6207963137 10 Manual.Count131072.C047333.packed 64 cuts47333 = true := by
 decide +kernel
def pointBounds47333 : List (Nat × Nat × Nat) := [(6208053248,110974084545615,110974471277631)]
theorem point_links_checked47333 : (cuts47333.take 1).map (fun c => (6207963137-1+2*2^10*c.k,110973905631562+c.lower,110974292363479+c.upper)) = pointBounds47333 := by
 decide +kernel
def cuts47334 : List PrefixCut := [⟨64,265553479,265553627⟩]
theorem checked47334 : checkPrefixCuts (2^48) 6208094209 10 Manual.Count131072.C047334.packed 64 cuts47334 = true := by
 decide +kernel
def cuts47335 : List PrefixCut := [⟨11,44477505,44477530⟩,
⟨64,266499984,266500136⟩]
theorem checked47335 : checkPrefixCuts (2^48) 6208225281 10 Manual.Count131072.C047335.packed 64 cuts47335 = true := by
 decide +kernel
def pointBounds47335 : List (Nat × Nat × Nat) := [(6208247808,110974476506219,110974863238457)]
theorem point_links_checked47335 : (cuts47335.take 1).map (fun c => (6208225281-1+2*2^10*c.k,110974432028714+c.lower,110974818760927+c.upper)) = pointBounds47335 := by
 decide +kernel
def cuts47336 : List PrefixCut := [⟨42,170197947,170198042⟩,
⟨64,260555139,260555285⟩]
theorem checked47336 : checkPrefixCuts (2^48) 6208356353 10 Manual.Count131072.C047336.packed 64 cuts47336 = true := by
 decide +kernel
def pointBounds47336 : List (Nat × Nat × Nat) := [(6208442368,110974868726645,110975255459105)]
theorem point_links_checked47336 : (cuts47336.take 1).map (fun c => (6208356353-1+2*2^10*c.k,110974698528698+c.lower,110975085261063+c.upper)) = pointBounds47336 := by
 decide +kernel
def cuts47337 : List PrefixCut := [⟨64,265445993,265446151⟩]
theorem checked47337 : checkPrefixCuts (2^48) 6208487425 10 Manual.Count131072.C047337.packed 64 cuts47337 = true := by
 decide +kernel
def cuts47338 : List PrefixCut := [⟨9,36495552,36495571⟩,
⟨64,264352341,264352485⟩]
theorem checked47338 : checkPrefixCuts (2^48) 6208618497 10 Manual.Count131072.C047338.packed 64 cuts47338 = true := by
 decide +kernel
def pointBounds47338 : List (Nat × Nat × Nat) := [(6208636928,110975261025382,110975647758070)]
theorem point_links_checked47338 : (cuts47338.take 1).map (fun c => (6208618497-1+2*2^10*c.k,110975224529830+c.lower,110975611262499+c.upper)) = pointBounds47338 := by
 decide +kernel
def cuts47339 : List PrefixCut := [⟨40,167920461,167920553⟩,
⟨64,265752135,265752286⟩]
theorem checked47339 : checkPrefixCuts (2^48) 6208749569 10 Manual.Count131072.C047339.packed 64 cuts47339 = true := by
 decide +kernel
def pointBounds47339 : List (Nat × Nat × Nat) := [(6208831488,110975656802632,110976043535537)]
theorem point_links_checked47339 : (cuts47339.take 1).map (fun c => (6208749569-1+2*2^10*c.k,110975488882171+c.lower,110975875614984+c.upper)) = pointBounds47339 := by
 decide +kernel
def cuts47340 : List PrefixCut := [⟨64,267877239,267877393⟩]
theorem checked47340 : checkPrefixCuts (2^48) 6208880641 10 Manual.Count131072.C047340.packed 64 cuts47340 = true := by
 decide +kernel
def cuts47341 : List PrefixCut := [⟨7,28605268,28605287⟩,
⟨64,264154245,264154396⟩]
theorem checked47341 : checkPrefixCuts (2^48) 6209011713 10 Manual.Count131072.C047341.packed 64 cuts47341 = true := by
 decide +kernel
def pointBounds47341 : List (Nat × Nat × Nat) := [(6209026048,110976051116813,110976437849950)]
theorem point_links_checked47341 : (cuts47341.take 1).map (fun c => (6209011713-1+2*2^10*c.k,110976022511545+c.lower,110976409244663+c.upper)) = pointBounds47341 := by
 decide +kernel
def cuts47342 : List PrefixCut := [⟨38,153856950,153857035⟩,
⟨64,260612785,260612931⟩]
theorem checked47342 : checkPrefixCuts (2^48) 6209142785 10 Manual.Count131072.C047342.packed 64 cuts47342 = true := by
 decide +kernel
def pointBounds47342 : List (Nat × Nat × Nat) := [(6209220608,110976440522740,110976827256094)]
theorem point_links_checked47342 : (cuts47342.take 1).map (fun c => (6209142785-1+2*2^10*c.k,110976286665790+c.lower,110976673399059+c.upper)) = pointBounds47342 := by
 decide +kernel
def cuts47343 : List PrefixCut := [⟨64,264551076,264551226⟩]
theorem checked47343 : checkPrefixCuts (2^48) 6209273857 10 Manual.Count131072.C047343.packed 64 cuts47343 = true := by
 decide +kernel
def cuts47344 : List PrefixCut := [⟨5,19446732,19446743⟩,
⟨64,260783111,260783258⟩]
theorem checked47344 : checkPrefixCuts (2^48) 6209404929 10 Manual.Count131072.C047344.packed 64 cuts47344 = true := by
 decide +kernel
def pointBounds47344 : List (Nat × Nat × Nat) := [(6209415168,110976831276383,110977218009959)]
theorem point_links_checked47344 : (cuts47344.take 1).map (fun c => (6209404929-1+2*2^10*c.k,110976811829651+c.lower,110977198563216+c.upper)) = pointBounds47344 := by
 decide +kernel
def cuts47345 : List PrefixCut := [⟨36,149495666,149495753⟩,
⟨64,267712944,267713100⟩]
theorem checked47345 : checkPrefixCuts (2^48) 6209536001 10 Manual.Count131072.C047345.packed 64 cuts47345 = true := by
 decide +kernel
def pointBounds47345 : List (Nat × Nat × Nat) := [(6209609728,110977222108428,110977608842227)]
theorem point_links_checked47345 : (cuts47345.take 1).map (fun c => (6209536001-1+2*2^10*c.k,110977072612762+c.lower,110977459346474+c.upper)) = pointBounds47345 := by
 decide +kernel
def cuts47346 : List PrefixCut := [⟨64,266891384,266891538⟩]
theorem checked47346 : checkPrefixCuts (2^48) 6209667073 10 Manual.Count131072.C047346.packed 64 cuts47346 = true := by
 decide +kernel
def cuts47347 : List PrefixCut := [⟨3,12057121,12057127⟩,
⟨64,260494648,260494795⟩]
theorem checked47347 : checkPrefixCuts (2^48) 6209798145 10 Manual.Count131072.C047347.packed 64 cuts47347 = true := by
 decide +kernel
def pointBounds47347 : List (Nat × Nat × Nat) := [(6209804288,110977619274211,110978006008239)]
theorem point_links_checked47347 : (cuts47347.take 1).map (fun c => (6209798145-1+2*2^10*c.k,110977607217090+c.lower,110977993951112+c.upper)) = pointBounds47347 := by
 decide +kernel
def cuts47348 : List PrefixCut := [⟨34,137837368,137837450⟩,
⟨64,262120860,262121013⟩]
theorem checked47348 : checkPrefixCuts (2^48) 6209929217 10 Manual.Count131072.C047348.packed 64 cuts47348 = true := by
 decide +kernel
def pointBounds47348 : List (Nat × Nat × Nat) := [(6209998848,110978005549106,110978392283357)]
theorem point_links_checked47348 : (cuts47348.take 1).map (fun c => (6209929217-1+2*2^10*c.k,110977867711738+c.lower,110978254445907+c.upper)) = pointBounds47348 := by
 decide +kernel
def cuts47349 : List PrefixCut := [⟨64,263248482,263248629⟩]
theorem checked47349 : checkPrefixCuts (2^48) 6210060289 10 Manual.Count131072.C047349.packed 64 cuts47349 = true := by
 decide +kernel
def cuts47350 : List PrefixCut := [⟨1,3988571,3988573⟩,
⟨64,265055906,265056057⟩]
theorem checked47350 : checkPrefixCuts (2^48) 6210191361 10 Manual.Count131072.C047350.packed 64 cuts47350 = true := by
 decide +kernel
def pointBounds47350 : List (Nat × Nat × Nat) := [(6210193408,110978397069651,110978783804122)]
theorem point_links_checked47350 : (cuts47350.take 1).map (fun c => (6210191361-1+2*2^10*c.k,110978393081080+c.lower,110978779815549+c.upper)) = pointBounds47350 := by
 decide +kernel
def cuts47351 : List PrefixCut := [⟨32,129489175,129489245⟩,
⟨64,261922981,261923124⟩]
theorem checked47351 : checkPrefixCuts (2^48) 6210322433 10 Manual.Count131072.C047351.packed 64 cuts47351 = true := by
 decide +kernel
def pointBounds47351 : List (Nat × Nat × Nat) := [(6210387968,110978787626161,110979174360851)]
theorem point_links_checked47351 : (cuts47351.take 1).map (fun c => (6210322433-1+2*2^10*c.k,110978658136986+c.lower,110979044871606+c.upper)) = pointBounds47351 := by
 decide +kernel
def cuts47352 : List PrefixCut := [⟨63,257929157,257929311⟩,
⟨64,262189407,262189564⟩]
theorem checked47352 : checkPrefixCuts (2^48) 6210453505 10 Manual.Count131072.C047352.packed 64 cuts47352 = true := by
 decide +kernel
def pointBounds47352 : List (Nat × Nat × Nat) := [(6210582528,110979177989124,110979564724041)]
theorem point_links_checked47352 : (cuts47352.take 1).map (fun c => (6210453505-1+2*2^10*c.k,110978920059967+c.lower,110979306794730+c.upper)) = pointBounds47352 := by
 decide +kernel
def cuts47353 : List PrefixCut := [⟨64,265809575,265809734⟩]
theorem checked47353 : checkPrefixCuts (2^48) 6210584577 10 Manual.Count131072.C047353.packed 64 cuts47353 = true := by
 decide +kernel
def cuts47354 : List PrefixCut := [⟨30,120598174,120598246⟩,
⟨64,262858113,262858264⟩]
theorem checked47354 : checkPrefixCuts (2^48) 6210715649 10 Manual.Count131072.C047354.packed 64 cuts47354 = true := by
 decide +kernel
def pointBounds47354 : List (Nat × Nat × Nat) := [(6210777088,110979568657123,110979955392274)]
theorem point_links_checked47354 : (cuts47354.take 1).map (fun c => (6210715649-1+2*2^10*c.k,110979448058949+c.lower,110979834794028+c.upper)) = pointBounds47354 := by
 decide +kernel
def cuts47355 : List PrefixCut := [⟨61,250571147,250571288⟩,
⟨64,262988541,262988689⟩]
theorem checked47355 : checkPrefixCuts (2^48) 6210846721 10 Manual.Count131072.C047355.packed 64 cuts47355 = true := by
 decide +kernel
def pointBounds47355 : List (Nat × Nat × Nat) := [(6210971648,110979961488209,110980348223580)]
theorem point_links_checked47355 : (cuts47355.take 1).map (fun c => (6210846721-1+2*2^10*c.k,110979710917062+c.lower,110980097652292+c.upper)) = pointBounds47355 := by
 decide +kernel
def cuts47356 : List PrefixCut := [⟨64,264478505,264478654⟩]
theorem checked47356 : checkPrefixCuts (2^48) 6210977793 10 Manual.Count131072.C047356.packed 64 cuts47356 = true := by
 decide +kernel
def cuts47357 : List PrefixCut := [⟨28,115968170,115968237⟩,
⟨64,265152695,265152844⟩]
theorem checked47357 : checkPrefixCuts (2^48) 6211108865 10 Manual.Count131072.C047357.packed 64 cuts47357 = true := by
 decide +kernel
def pointBounds47357 : List (Nat × Nat × Nat) := [(6211166208,110980354352278,110980741087872)]
theorem point_links_checked47357 : (cuts47357.take 1).map (fun c => (6211108865-1+2*2^10*c.k,110980238384108+c.lower,110980625119635+c.upper)) = pointBounds47357 := by
 decide +kernel
def cuts47358 : List PrefixCut := [⟨59,242171806,242171946⟩,
⟨64,264331380,264331533⟩]
theorem checked47358 : checkPrefixCuts (2^48) 6211239937 10 Manual.Count131072.C047358.packed 64 cuts47358 = true := by
 decide +kernel
def pointBounds47358 : List (Nat × Nat × Nat) := [(6211360768,110980745708609,110981132444425)]
theorem point_links_checked47358 : (cuts47358.take 1).map (fun c => (6211239937-1+2*2^10*c.k,110980503536803+c.lower,110980890272479+c.upper)) = pointBounds47358 := by
 decide +kernel
def cuts47359 : List PrefixCut := [⟨64,267044744,267044893⟩]
theorem checked47359 : checkPrefixCuts (2^48) 6211371009 10 Manual.Count131072.C047359.packed 64 cuts47359 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000229
