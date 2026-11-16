import PlattAssemblyKernel
import PlattCertificates.Count131072.C028320
import PlattCertificates.Count131072.C028321
import PlattCertificates.Count131072.C028322
import PlattCertificates.Count131072.C028323
import PlattCertificates.Count131072.C028324
import PlattCertificates.Count131072.C028325
import PlattCertificates.Count131072.C028326
import PlattCertificates.Count131072.C028327
import PlattCertificates.Count131072.C028328
import PlattCertificates.Count131072.C028329
import PlattCertificates.Count131072.C028330
import PlattCertificates.Count131072.C028331
import PlattCertificates.Count131072.C028332
import PlattCertificates.Count131072.C028333
import PlattCertificates.Count131072.C028334
import PlattCertificates.Count131072.C028335
import PlattCertificates.Count131072.C028336
import PlattCertificates.Count131072.C028337
import PlattCertificates.Count131072.C028338
import PlattCertificates.Count131072.C028339
import PlattCertificates.Count131072.C028340
import PlattCertificates.Count131072.C028341
import PlattCertificates.Count131072.C028342
import PlattCertificates.Count131072.C028343
import PlattCertificates.Count131072.C028344
import PlattCertificates.Count131072.C028345
import PlattCertificates.Count131072.C028346
import PlattCertificates.Count131072.C028347
import PlattCertificates.Count131072.C028348
import PlattCertificates.Count131072.C028349
import PlattCertificates.Count131072.C028350
import PlattCertificates.Count131072.C028351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000260
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28320 : List PrefixCut := [⟨71,255650258,255650399⟩,
⟨128,454182819,454183071⟩]
theorem checked28320 : checkPrefixCuts (2^48) 3715891201 9 Manual.Count131072.C028320.packed 128 cuts28320 = true := by
 decide +kernel
def pointBounds28320 : List (Nat × Nat × Nat) := [(3715963904,104493831428895,104494214338731)]
theorem point_links_checked28320 : (cuts28320.take 1).map (fun c => (3715891201-1+2*2^9*c.k,104493575778637+c.lower,104493958688332+c.upper)) = pointBounds28320 := by
 decide +kernel
def cuts28321 : List PrefixCut := [⟨57,195878358,195878468⟩,
⟨128,444547082,444547329⟩]
theorem checked28321 : checkPrefixCuts (2^48) 3716022273 9 Manual.Count131072.C028321.packed 128 cuts28321 = true := by
 decide +kernel
def pointBounds28321 : List (Nat × Nat × Nat) := [(3716080640,104494225839814,104494608749871)]
theorem point_links_checked28321 : (cuts28321.take 1).map (fun c => (3716022273-1+2*2^9*c.k,104494029961456+c.lower,104494412871403+c.upper)) = pointBounds28321 := by
 decide +kernel
def cuts28322 : List PrefixCut := [⟨43,152168031,152168115⟩,
⟨128,451121057,451121307⟩]
theorem checked28322 : checkPrefixCuts (2^48) 3716153345 9 Manual.Count131072.C028322.packed 128 cuts28322 = true := by
 decide +kernel
def pointBounds28322 : List (Nat × Nat × Nat) := [(3716197376,104494626676569,104495009586847)]
theorem point_links_checked28322 : (cuts28322.take 1).map (fun c => (3716153345-1+2*2^9*c.k,104494474508538+c.lower,104494857418732+c.upper)) = pointBounds28322 := by
 decide +kernel
def cuts28323 : List PrefixCut := [⟨29,101871165,101871223⟩,
⟨128,450877925,450878178⟩]
theorem checked28323 : checkPrefixCuts (2^48) 3716284417 9 Manual.Count131072.C028323.packed 128 cuts28323 = true := by
 decide +kernel
def pointBounds28323 : List (Nat × Nat × Nat) := [(3716314112,104495027500760,104495410411262)]
theorem point_links_checked28323 : (cuts28323.take 1).map (fun c => (3716284417-1+2*2^9*c.k,104494925629595+c.lower,104495308540039+c.upper)) = pointBounds28323 := by
 decide +kernel
def cuts28324 : List PrefixCut := [⟨15,54379973,54380003⟩,
⟨128,453588569,453588818⟩]
theorem checked28324 : checkPrefixCuts (2^48) 3716415489 9 Manual.Count131072.C028324.packed 128 cuts28324 = true := by
 decide +kernel
def pointBounds28324 : List (Nat × Nat × Nat) := [(3716430848,104495430887493,104495813798220)]
theorem point_links_checked28324 : (cuts28324.take 1).map (fun c => (3716415489-1+2*2^9*c.k,104495376507520+c.lower,104495759418217+c.upper)) = pointBounds28324 := by
 decide +kernel
def cuts28325 : List PrefixCut := [⟨1,3635309,3635311⟩,
⟨115,404573226,404573449⟩,
⟨128,449482938,449483185⟩]
theorem checked28325 : checkPrefixCuts (2^48) 3716546561 9 Manual.Count131072.C028325.packed 128 cuts28325 = true := by
 decide +kernel
def pointBounds28325 : List (Nat × Nat × Nat) := [(3716547584,104495833731398,104496216642346),(3716664320,104496234669315,104496617580484)]
theorem point_links_checked28325 : (cuts28325.take 2).map (fun c => (3716546561-1+2*2^9*c.k,104495830096089+c.lower,104496213007035+c.upper)) = pointBounds28325 := by
 decide +kernel
def cuts28326 : List PrefixCut := [⟨101,355485516,355485717⟩,
⟨128,451511852,451512103⟩]
theorem checked28326 : checkPrefixCuts (2^48) 3716677633 9 Manual.Count131072.C028326.packed 128 cuts28326 = true := by
 decide +kernel
def pointBounds28326 : List (Nat × Nat × Nat) := [(3716781056,104496635064543,104497017975937)]
theorem point_links_checked28326 : (cuts28326.take 1).map (fun c => (3716677633-1+2*2^9*c.k,104496279579027+c.lower,104496662490220+c.upper)) = pointBounds28326 := by
 decide +kernel
def cuts28327 : List PrefixCut := [⟨87,310338865,310339034⟩,
⟨128,456645390,456645640⟩]
theorem checked28327 : checkPrefixCuts (2^48) 3716808705 9 Manual.Count131072.C028327.packed 128 cuts28327 = true := by
 decide +kernel
def pointBounds28327 : List (Nat × Nat × Nat) := [(3716897792,104497041429744,104497424341357)]
theorem point_links_checked28327 : (cuts28327.take 1).map (fun c => (3716808705-1+2*2^9*c.k,104496731090879+c.lower,104497114002323+c.upper)) = pointBounds28327 := by
 decide +kernel
def cuts28328 : List PrefixCut := [⟨73,255123675,255123818⟩,
⟨128,444513129,444513380⟩]
theorem checked28328 : checkPrefixCuts (2^48) 3716939777 9 Manual.Count131072.C028328.packed 128 cuts28328 = true := by
 decide +kernel
def pointBounds28328 : List (Nat × Nat × Nat) := [(3717014528,104497442859944,104497825771781)]
theorem point_links_checked28328 : (cuts28328.take 1).map (fun c => (3716939777-1+2*2^9*c.k,104497187736269+c.lower,104497570647963+c.upper)) = pointBounds28328 := by
 decide +kernel
def cuts28329 : List PrefixCut := [⟨59,204985692,204985805⟩,
⟨128,446693402,446693653⟩]
theorem checked28329 : checkPrefixCuts (2^48) 3717070849 9 Manual.Count131072.C028329.packed 128 cuts28329 = true := by
 decide +kernel
def pointBounds28329 : List (Nat × Nat × Nat) := [(3717131264,104497837235090,104498220147148)]
theorem point_links_checked28329 : (cuts28329.take 1).map (fun c => (3717070849-1+2*2^9*c.k,104497632249398+c.lower,104498015161343+c.upper)) = pointBounds28329 := by
 decide +kernel
def cuts28330 : List PrefixCut := [⟨45,157198406,157198496⟩,
⟨128,450615138,450615394⟩]
theorem checked28330 : checkPrefixCuts (2^48) 3717201921 9 Manual.Count131072.C028330.packed 128 cuts28330 = true := by
 decide +kernel
def pointBounds28330 : List (Nat × Nat × Nat) := [(3717248000,104498236141206,104498619053492)]
theorem point_links_checked28330 : (cuts28330.take 1).map (fun c => (3717201921-1+2*2^9*c.k,104498078942800+c.lower,104498461854996+c.upper)) = pointBounds28330 := by
 decide +kernel
def cuts28331 : List PrefixCut := [⟨31,110474396,110474456⟩,
⟨128,450372205,450372451⟩]
theorem checked28331 : checkPrefixCuts (2^48) 3717332993 9 Manual.Count131072.C028331.packed 128 cuts28331 = true := by
 decide +kernel
def pointBounds28331 : List (Nat × Nat × Nat) := [(3717364736,104498640032334,104499022944846)]
theorem point_links_checked28331 : (cuts28331.take 1).map (fun c => (3717332993-1+2*2^9*c.k,104498529557938+c.lower,104498912470390+c.upper)) = pointBounds28331 := by
 decide +kernel
def cuts28332 : List PrefixCut := [⟨17,63526340,63526373⟩,
⟨128,451870654,451870904⟩]
theorem checked28332 : checkPrefixCuts (2^48) 3717464065 9 Manual.Count131072.C028332.packed 128 cuts28332 = true := by
 decide +kernel
def pointBounds28332 : List (Nat × Nat × Nat) := [(3717481472,104499043456483,104499426369214)]
theorem point_links_checked28332 : (cuts28332.take 1).map (fun c => (3717464065-1+2*2^9*c.k,104498979930143+c.lower,104499362842841+c.upper)) = pointBounds28332 := by
 decide +kernel
def cuts28333 : List PrefixCut := [⟨3,10675704,10675710⟩,
⟨117,412257437,412257669⟩,
⟨128,449734722,449734975⟩]
theorem checked28333 : checkPrefixCuts (2^48) 3717595137 9 Manual.Count131072.C028333.packed 128 cuts28333 = true := by
 decide +kernel
def pointBounds28333 : List (Nat × Nat × Nat) := [(3717598208,104499442476501,104499825389455),(3717714944,104499844058234,104500226971414)]
theorem point_links_checked28333 : (cuts28333.take 2).map (fun c => (3717595137-1+2*2^9*c.k,104499431800797+c.lower,104499814713745+c.upper)) = pointBounds28333 := by
 decide +kernel
def cuts28334 : List PrefixCut := [⟨103,362577619,362577822⟩,
⟨128,447447591,447447842⟩]
theorem checked28334 : checkPrefixCuts (2^48) 3717726209 9 Manual.Count131072.C028334.packed 128 cuts28334 = true := by
 decide +kernel
def pointBounds28334 : List (Nat × Nat × Nat) := [(3717831680,104500244113138,104500627026542)]
theorem point_links_checked28334 : (cuts28334.take 1).map (fun c => (3717726209-1+2*2^9*c.k,104499881535519+c.lower,104500264448720+c.upper)) = pointBounds28334 := by
 decide +kernel
def cuts28335 : List PrefixCut := [⟨89,313203911,313204084⟩,
⟨128,450838585,450838836⟩]
theorem checked28335 : checkPrefixCuts (2^48) 3717857281 9 Manual.Count131072.C028335.packed 128 cuts28335 = true := by
 decide +kernel
def pointBounds28335 : List (Nat × Nat × Nat) := [(3717948416,104500642187021,104501025100646)]
theorem point_links_checked28335 : (cuts28335.take 1).map (fun c => (3717857281-1+2*2^9*c.k,104500328983110+c.lower,104500711896562+c.upper)) = pointBounds28335 := by
 decide +kernel
def cuts28336 : List PrefixCut := [⟨75,264893390,264893538⟩,
⟨128,447264618,447264868⟩]
theorem checked28336 : checkPrefixCuts (2^48) 3717988353 9 Manual.Count131072.C028336.packed 128 cuts28336 = true := by
 decide +kernel
def pointBounds28336 : List (Nat × Nat × Nat) := [(3718065152,104501044715085,104501427628936)]
theorem point_links_checked28336 : (cuts28336.take 1).map (fun c => (3717988353-1+2*2^9*c.k,104500779821695+c.lower,104501162735398+c.upper)) = pointBounds28336 := by
 decide +kernel
def cuts28337 : List PrefixCut := [⟨61,217797335,217797459⟩,
⟨128,453759229,453759488⟩]
theorem checked28337 : checkPrefixCuts (2^48) 3718119425 9 Manual.Count131072.C028337.packed 128 cuts28337 = true := by
 decide +kernel
def pointBounds28337 : List (Nat × Nat × Nat) := [(3718181888,104501444883648,104501827797725)]
theorem point_links_checked28337 : (cuts28337.take 1).map (fun c => (3718119425-1+2*2^9*c.k,104501227086313+c.lower,104501610000266+c.upper)) = pointBounds28337 := by
 decide +kernel
def cuts28338 : List PrefixCut := [⟨47,166465194,166465287⟩,
⟨128,454802963,454803220⟩]
theorem checked28338 : checkPrefixCuts (2^48) 3718250497 9 Manual.Count131072.C028338.packed 128 cuts28338 = true := by
 decide +kernel
def pointBounds28338 : List (Nat × Nat × Nat) := [(3718298624,104501847310736,104502230225041)]
theorem point_links_checked28338 : (cuts28338.take 1).map (fun c => (3718250497-1+2*2^9*c.k,104501680845542+c.lower,104502063759754+c.upper)) = pointBounds28338 := by
 decide +kernel
def cuts28339 : List PrefixCut := [⟨33,114606595,114606657⟩,
⟨128,449790933,449791179⟩]
theorem checked28339 : checkPrefixCuts (2^48) 3718381569 9 Manual.Count131072.C028339.packed 128 cuts28339 = true := by
 decide +kernel
def pointBounds28339 : List (Nat × Nat × Nat) := [(3718415360,104502250255100,104502633169631)]
theorem point_links_checked28339 : (cuts28339.take 1).map (fun c => (3718381569-1+2*2^9*c.k,104502135648505+c.lower,104502518562974+c.upper)) = pointBounds28339 := by
 decide +kernel
def cuts28340 : List PrefixCut := [⟨19,68807085,68807126⟩,
⟨128,451591774,451592034⟩]
theorem checked28340 : checkPrefixCuts (2^48) 3718512641 9 Manual.Count131072.C028340.packed 128 cuts28340 = true := by
 decide +kernel
def pointBounds28340 : List (Nat × Nat × Nat) := [(3718532096,104502654246523,104503037161279)]
theorem point_links_checked28340 : (cuts28340.take 1).map (fun c => (3718512641-1+2*2^9*c.k,104502585439438+c.lower,104502968354153+c.upper)) = pointBounds28340 := by
 decide +kernel
def cuts28341 : List PrefixCut := [⟨5,17863511,17863520⟩,
⟨119,420845594,420845827⟩,
⟨128,453770882,453771133⟩]
theorem checked28341 : checkPrefixCuts (2^48) 3718643713 9 Manual.Count131072.C028341.packed 128 cuts28341 = true := by
 decide +kernel
def pointBounds28341 : List (Nat × Nat × Nat) := [(3718648832,104503054894723,104503437809707),(3718765568,104503457876806,104503840792014)]
theorem point_links_checked28341 : (cuts28341.take 2).map (fun c => (3718643713-1+2*2^9*c.k,104503037031212+c.lower,104503419946187+c.upper)) = pointBounds28341 := by
 decide +kernel
def cuts28342 : List PrefixCut := [⟨105,372995969,372996180⟩,
⟨128,456479609,456479865⟩]
theorem checked28342 : checkPrefixCuts (2^48) 3718774785 9 Manual.Count131072.C028342.packed 128 cuts28342 = true := by
 decide +kernel
def pointBounds28342 : List (Nat × Nat × Nat) := [(3718882304,104503863798063,104504246713500)]
theorem point_links_checked28342 : (cuts28342.take 1).map (fun c => (3718774785-1+2*2^9*c.k,104503490802094+c.lower,104503873717320+c.upper)) = pointBounds28342 := by
 decide +kernel
def cuts28343 : List PrefixCut := [⟨91,321743784,321743963⟩,
⟨128,449500528,449500779⟩]
theorem checked28343 : checkPrefixCuts (2^48) 3718905857 9 Manual.Count131072.C028343.packed 128 cuts28343 = true := by
 decide +kernel
def pointBounds28343 : List (Nat × Nat × Nat) := [(3718999040,104504269025487,104504651941148)]
theorem point_links_checked28343 : (cuts28343.take 1).map (fun c => (3718905857-1+2*2^9*c.k,104503947281703+c.lower,104504330197185+c.upper)) = pointBounds28343 := by
 decide +kernel
def cuts28344 : List PrefixCut := [⟨77,273143855,273144008⟩,
⟨128,449181939,449182191⟩]
theorem checked28344 : checkPrefixCuts (2^48) 3719036929 9 Manual.Count131072.C028344.packed 128 cuts28344 = true := by
 decide +kernel
def pointBounds28344 : List (Nat × Nat × Nat) := [(3719115776,104504669926086,104505052841972)]
theorem point_links_checked28344 : (cuts28344.take 1).map (fun c => (3719036929-1+2*2^9*c.k,104504396782231+c.lower,104504779697964+c.upper)) = pointBounds28344 := by
 decide +kernel
def cuts28345 : List PrefixCut := [⟨63,224698575,224698697⟩,
⟨128,454539439,454539690⟩]
theorem checked28345 : checkPrefixCuts (2^48) 3719168001 9 Manual.Count131072.C028345.packed 128 cuts28345 = true := by
 decide +kernel
def pointBounds28345 : List (Nat × Nat × Nat) := [(3719232512,104505070662745,104505453578852)]
theorem point_links_checked28345 : (cuts28345.take 1).map (fun c => (3719168001-1+2*2^9*c.k,104504845964170+c.lower,104505228880155+c.upper)) = pointBounds28345 := by
 decide +kernel
def cuts28346 : List PrefixCut := [⟨49,171715760,171715857⟩,
⟨128,447409672,447409918⟩]
theorem checked28346 : checkPrefixCuts (2^48) 3719299073 9 Manual.Count131072.C028346.packed 128 cuts28346 = true := by
 decide +kernel
def pointBounds28346 : List (Nat × Nat × Nat) := [(3719349248,104505472219369,104505855135702)]
theorem point_links_checked28346 : (cuts28346.take 1).map (fun c => (3719299073-1+2*2^9*c.k,104505300503609+c.lower,104505683419845+c.upper)) = pointBounds28346 := by
 decide +kernel
def cuts28347 : List PrefixCut := [⟨35,125320326,125320395⟩,
⟨128,455188433,455188685⟩]
theorem checked28347 : checkPrefixCuts (2^48) 3719430145 9 Manual.Count131072.C028347.packed 128 cuts28347 = true := by
 decide +kernel
def pointBounds28347 : List (Nat × Nat × Nat) := [(3719465984,104505873233607,104506256150158)]
theorem point_links_checked28347 : (cuts28347.take 1).map (fun c => (3719430145-1+2*2^9*c.k,104505747913281+c.lower,104506130829763+c.upper)) = pointBounds28347 := by
 decide +kernel
def cuts28348 : List PrefixCut := [⟨21,73706480,73706522⟩,
⟨128,449799651,449799903⟩]
theorem checked28348 : checkPrefixCuts (2^48) 3719561217 9 Manual.Count131072.C028348.packed 128 cuts28348 = true := by
 decide +kernel
def pointBounds28348 : List (Nat × Nat × Nat) := [(3719582720,104506276808194,104506659724970)]
theorem point_links_checked28348 : (cuts28348.take 1).map (fun c => (3719561217-1+2*2^9*c.k,104506203101714+c.lower,104506586018448+c.upper)) = pointBounds28348 := by
 decide +kernel
def cuts28349 : List PrefixCut := [⟨7,26106661,26106675⟩,
⟨121,423753678,423753912⟩,
⟨128,450994504,450994752⟩]
theorem checked28349 : checkPrefixCuts (2^48) 3719692289 9 Manual.Count131072.C028349.packed 128 cuts28349 = true := by
 decide +kernel
def pointBounds28349 : List (Nat × Nat × Nat) := [(3719699456,104506679008026,104507061925026),(3719816192,104507076655043,104507459572263)]
theorem point_links_checked28349 : (cuts28349.take 2).map (fun c => (3719692289-1+2*2^9*c.k,104506652901365+c.lower,104507035818351+c.upper)) = pointBounds28349 := by
 decide +kernel
def cuts28350 : List PrefixCut := [⟨107,378187531,378187745⟩,
⟨128,450751651,450751904⟩]
theorem checked28350 : checkPrefixCuts (2^48) 3719823361 9 Manual.Count131072.C028350.packed 128 cuts28350 = true := by
 decide +kernel
def pointBounds28350 : List (Nat × Nat × Nat) := [(3719932928,104507482083400,104507865000848)]
theorem point_links_checked28350 : (cuts28350.take 1).map (fun c => (3719823361-1+2*2^9*c.k,104507103895869+c.lower,104507486813103+c.upper)) = pointBounds28350 := by
 decide +kernel
def cuts28351 : List PrefixCut := [⟨93,324603957,324604141⟩,
⟨128,447103844,447104097⟩]
theorem checked28351 : checkPrefixCuts (2^48) 3719954433 9 Manual.Count131072.C028351.packed 128 cuts28351 = true := by
 decide +kernel
def pointBounds28351 : List (Nat × Nat × Nat) := [(3720049664,104507879251477,104508262169148)]
theorem point_links_checked28351 : (cuts28351.take 1).map (fun c => (3719954433-1+2*2^9*c.k,104507554647520+c.lower,104507937565007+c.upper)) = pointBounds28351 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000260
