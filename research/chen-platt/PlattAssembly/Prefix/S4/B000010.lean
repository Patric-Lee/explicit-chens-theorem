import PlattAssemblyKernel
import PlattCertificates.Count131072.C030320
import PlattCertificates.Count131072.C030321
import PlattCertificates.Count131072.C030322
import PlattCertificates.Count131072.C030323
import PlattCertificates.Count131072.C030324
import PlattCertificates.Count131072.C030325
import PlattCertificates.Count131072.C030326
import PlattCertificates.Count131072.C030327
import PlattCertificates.Count131072.C030328
import PlattCertificates.Count131072.C030329
import PlattCertificates.Count131072.C030330
import PlattCertificates.Count131072.C030331
import PlattCertificates.Count131072.C030332
import PlattCertificates.Count131072.C030333
import PlattCertificates.Count131072.C030334
import PlattCertificates.Count131072.C030335
import PlattCertificates.Count131072.C030336
import PlattCertificates.Count131072.C030337
import PlattCertificates.Count131072.C030338
import PlattCertificates.Count131072.C030339
import PlattCertificates.Count131072.C030340
import PlattCertificates.Count131072.C030341
import PlattCertificates.Count131072.C030342
import PlattCertificates.Count131072.C030343
import PlattCertificates.Count131072.C030344
import PlattCertificates.Count131072.C030345
import PlattCertificates.Count131072.C030346
import PlattCertificates.Count131072.C030347
import PlattCertificates.Count131072.C030348
import PlattCertificates.Count131072.C030349
import PlattCertificates.Count131072.C030350
import PlattCertificates.Count131072.C030351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30320 : List PrefixCut := [⟨47,155028249,155028332⟩,
⟨128,416611971,416612204⟩]
theorem checked30320 : checkPrefixCuts (2^48) 3978035201 9 Manual.Count131072.C030320.packed 128 cuts30320 = true := by
 decide +kernel
def pointBounds30320 : List (Nat × Nat × Nat) := [(3978083328,105363153779119,105363537176372)]
theorem point_links_checked30320 : (cuts30320.take 1).map (fun c => (3978035201-1+2*2^9*c.k,105362998750870+c.lower,105363382148040+c.upper)) = pointBounds30320 := by
 decide +kernel
def cuts30321 : List PrefixCut := [⟨41,129834605,129834683⟩,
⟨128,417234907,417235144⟩]
theorem checked30321 : checkPrefixCuts (2^48) 3978166273 9 Manual.Count131072.C030321.packed 128 cuts30321 = true := by
 decide +kernel
def pointBounds30321 : List (Nat × Nat × Nat) := [(3978208256,105363545197446,105363928594927)]
theorem point_links_checked30321 : (cuts30321.take 1).map (fun c => (3978166273-1+2*2^9*c.k,105363415362841+c.lower,105363798760244+c.upper)) = pointBounds30321 := by
 decide +kernel
def cuts30322 : List PrefixCut := [⟨35,119076089,119076158⟩,
⟨128,421678634,421678877⟩]
theorem checked30322 : checkPrefixCuts (2^48) 3978297345 9 Manual.Count131072.C030322.packed 128 cuts30322 = true := by
 decide +kernel
def pointBounds30322 : List (Nat × Nat × Nat) := [(3978333184,105363951673837,105364335071546)]
theorem point_links_checked30322 : (cuts30322.take 1).map (fun c => (3978297345-1+2*2^9*c.k,105363832597748+c.lower,105364215995388+c.upper)) = pointBounds30322 := by
 decide +kernel
def cuts30323 : List PrefixCut := [⟨29,95724759,95724814⟩,
⟨128,423504181,423504419⟩]
theorem checked30323 : checkPrefixCuts (2^48) 3978428417 9 Manual.Count131072.C030323.packed 128 cuts30323 = true := by
 decide +kernel
def pointBounds30323 : List (Nat × Nat × Nat) := [(3978458112,105364350001141,105364733399079)]
theorem point_links_checked30323 : (cuts30323.take 1).map (fun c => (3978428417-1+2*2^9*c.k,105364254276382+c.lower,105364637674265+c.upper)) = pointBounds30323 := by
 decide +kernel
def cuts30324 : List PrefixCut := [⟨23,75558578,75558619⟩,
⟨128,414576089,414576322⟩]
theorem checked30324 : checkPrefixCuts (2^48) 3978559489 9 Manual.Count131072.C030324.packed 128 cuts30324 = true := by
 decide +kernel
def pointBounds30324 : List (Nat × Nat × Nat) := [(3978583040,105364753339141,105365136737303)]
theorem point_links_checked30324 : (cuts30324.take 1).map (fun c => (3978559489-1+2*2^9*c.k,105364677780563+c.lower,105365061178684+c.upper)) = pointBounds30324 := by
 decide +kernel
def cuts30325 : List PrefixCut := [⟨17,56101149,56101177⟩,
⟨128,425315574,425315807⟩]
theorem checked30325 : checkPrefixCuts (2^48) 3978690561 9 Manual.Count131072.C030325.packed 128 cuts30325 = true := by
 decide +kernel
def pointBounds30325 : List (Nat × Nat × Nat) := [(3978707968,105365148457801,105365531856183)]
theorem point_links_checked30325 : (cuts30325.take 1).map (fun c => (3978690561-1+2*2^9*c.k,105365092356652+c.lower,105365475755006+c.upper)) = pointBounds30325 := by
 decide +kernel
def cuts30326 : List PrefixCut := [⟨11,35725309,35725328⟩,
⟨128,420915580,420915815⟩]
theorem checked30326 : checkPrefixCuts (2^48) 3978821633 9 Manual.Count131072.C030326.packed 128 cuts30326 = true := by
 decide +kernel
def pointBounds30326 : List (Nat × Nat × Nat) := [(3978832896,105365553397535,105365936796141)]
theorem point_links_checked30326 : (cuts30326.take 1).map (fun c => (3978821633-1+2*2^9*c.k,105365517672226+c.lower,105365901070813+c.upper)) = pointBounds30326 := by
 decide +kernel
def cuts30327 : List PrefixCut := [⟨5,15562999,15563007⟩,
⟨127,411917848,411918080⟩,
⟨128,415242564,415242797⟩]
theorem checked30327 : checkPrefixCuts (2^48) 3978952705 9 Manual.Count131072.C030327.packed 128 cuts30327 = true := by
 decide +kernel
def pointBounds30327 : List (Nat × Nat × Nat) := [(3978957824,105365954150805,105366337549635),(3979082752,105366350505654,105366733904708)]
theorem point_links_checked30327 : (cuts30327.take 2).map (fun c => (3978952705-1+2*2^9*c.k,105365938587806+c.lower,105366321986628+c.upper)) = pointBounds30327 := by
 decide +kernel
def cuts30328 : List PrefixCut := [⟨121,391885828,391886051⟩,
⟨128,416785026,416785262⟩]
theorem checked30328 : checkPrefixCuts (2^48) 3979083777 9 Manual.Count131072.C030328.packed 128 cuts30328 = true := by
 decide +kernel
def pointBounds30328 : List (Nat × Nat × Nat) := [(3979207680,105366745716198,105367129115476)]
theorem point_links_checked30328 : (cuts30328.take 1).map (fun c => (3979083777-1+2*2^9*c.k,105366353830370+c.lower,105366737229425+c.upper)) = pointBounds30328 := by
 decide +kernel
def cuts30329 : List PrefixCut := [⟨115,372916191,372916401⟩,
⟨128,415356638,415356870⟩]
theorem checked30329 : checkPrefixCuts (2^48) 3979214849 9 Manual.Count131072.C030329.packed 128 cuts30329 = true := by
 decide +kernel
def pointBounds30329 : List (Nat × Nat × Nat) := [(3979332608,105367143531587,105367526931088)]
theorem point_links_checked30329 : (cuts30329.take 1).map (fun c => (3979214849-1+2*2^9*c.k,105366770615396+c.lower,105367154014687+c.upper)) = pointBounds30329 := by
 decide +kernel
def cuts30330 : List PrefixCut := [⟨109,353452658,353452860⟩,
⟨128,416757618,416757855⟩]
theorem checked30330 : checkPrefixCuts (2^48) 3979345921 9 Manual.Count131072.C030330.packed 128 cuts30330 = true := by
 decide +kernel
def pointBounds30330 : List (Nat × Nat × Nat) := [(3979457536,105367539424692,105367922824417)]
theorem point_links_checked30330 : (cuts30330.take 1).map (fun c => (3979345921-1+2*2^9*c.k,105367185972034+c.lower,105367569371557+c.upper)) = pointBounds30330 := by
 decide +kernel
def cuts30331 : List PrefixCut := [⟨103,341063417,341063610⟩,
⟨128,420987782,420988021⟩]
theorem checked30331 : checkPrefixCuts (2^48) 3979476993 9 Manual.Count131072.C030331.packed 128 cuts30331 = true := by
 decide +kernel
def pointBounds30331 : List (Nat × Nat × Nat) := [(3979582464,105367943793069,105368327193022)]
theorem point_links_checked30331 : (cuts30331.take 1).map (fun c => (3979476993-1+2*2^9*c.k,105367602729652+c.lower,105367986129412+c.upper)) = pointBounds30331 := by
 decide +kernel
def cuts30332 : List PrefixCut := [⟨97,310780625,310780802⟩,
⟨128,414325329,414325564⟩]
theorem checked30332 : checkPrefixCuts (2^48) 3979608065 9 Manual.Count131072.C030332.packed 128 cuts30332 = true := by
 decide +kernel
def pointBounds30332 : List (Nat × Nat × Nat) := [(3979707392,105368334498059,105368717898235)]
theorem point_links_checked30332 : (cuts30332.take 1).map (fun c => (3979608065-1+2*2^9*c.k,105368023717434+c.lower,105368407117433+c.upper)) = pointBounds30332 := by
 decide +kernel
def cuts30333 : List PrefixCut := [⟨91,296837630,296837800⟩,
⟨128,417918788,417919027⟩]
theorem checked30333 : checkPrefixCuts (2^48) 3979739137 9 Manual.Count131072.C030333.packed 128 cuts30333 = true := by
 decide +kernel
def pointBounds30333 : List (Nat × Nat × Nat) := [(3979832320,105368734880393,105369118280797)]
theorem point_links_checked30333 : (cuts30333.take 1).map (fun c => (3979739137-1+2*2^9*c.k,105368438042763+c.lower,105368821442997+c.upper)) = pointBounds30333 := by
 decide +kernel
def cuts30334 : List PrefixCut := [⟨85,279571413,279571575⟩,
⟨128,420946105,420946347⟩]
theorem checked30334 : checkPrefixCuts (2^48) 3979870209 9 Manual.Count131072.C030334.packed 128 cuts30334 = true := by
 decide +kernel
def pointBounds30334 : List (Nat × Nat × Nat) := [(3979957248,105369135532964,105369518933599)]
theorem point_links_checked30334 : (cuts30334.take 1).map (fun c => (3979870209-1+2*2^9*c.k,105368855961551+c.lower,105369239362024+c.upper)) = pointBounds30334 := by
 decide +kernel
def cuts30335 : List PrefixCut := [⟨79,258628892,258629035⟩,
⟨128,421285884,421286116⟩]
theorem checked30335 : checkPrefixCuts (2^48) 3980001281 9 Manual.Count131072.C030335.packed 128 cuts30335 = true := by
 decide +kernel
def pointBounds30335 : List (Nat × Nat × Nat) := [(3980082176,105369535536548,105369918937406)]
theorem point_links_checked30335 : (cuts30335.take 1).map (fun c => (3980001281-1+2*2^9*c.k,105369276907656+c.lower,105369660308371+c.upper)) = pointBounds30335 := by
 decide +kernel
def cuts30336 : List PrefixCut := [⟨73,243203740,243203875⟩,
⟨128,422898586,422898822⟩]
theorem checked30336 : checkPrefixCuts (2^48) 3980132353 9 Manual.Count131072.C030336.packed 128 cuts30336 = true := by
 decide +kernel
def pointBounds30336 : List (Nat × Nat × Nat) := [(3980207104,105369941397280,105370324798362)]
theorem point_links_checked30336 : (cuts30336.take 1).map (fun c => (3980132353-1+2*2^9*c.k,105369698193540+c.lower,105370081594487+c.upper)) = pointBounds30336 := by
 decide +kernel
def cuts30337 : List PrefixCut := [⟨67,216747758,216747873⟩,
⟨128,420126610,420126837⟩]
theorem checked30337 : checkPrefixCuts (2^48) 3980263425 9 Manual.Count131072.C030337.packed 128 cuts30337 = true := by
 decide +kernel
def pointBounds30337 : List (Nat × Nat × Nat) := [(3980332032,105370337839884,105370721241182)]
theorem point_links_checked30337 : (cuts30337.take 1).map (fun c => (3980263425-1+2*2^9*c.k,105370121092126+c.lower,105370504493309+c.upper)) = pointBounds30337 := by
 decide +kernel
def cuts30338 : List PrefixCut := [⟨61,197930640,197930754⟩,
⟨128,417637830,417638071⟩]
theorem checked30338 : checkPrefixCuts (2^48) 3980394497 9 Manual.Count131072.C030338.packed 128 cuts30338 = true := by
 decide +kernel
def pointBounds30338 : List (Nat × Nat × Nat) := [(3980456960,105370739149376,105371122550900)]
theorem point_links_checked30338 : (cuts30338.take 1).map (fun c => (3980394497-1+2*2^9*c.k,105370541218736+c.lower,105370924620146+c.upper)) = pointBounds30338 := by
 decide +kernel
def cuts30339 : List PrefixCut := [⟨55,178619766,178619866⟩,
⟨128,419816113,419816348⟩]
theorem checked30339 : checkPrefixCuts (2^48) 3980525569 9 Manual.Count131072.C030339.packed 128 cuts30339 = true := by
 decide +kernel
def pointBounds30339 : List (Nat × Nat × Nat) := [(3980581888,105371137476332,105371520878083)]
theorem point_links_checked30339 : (cuts30339.take 1).map (fun c => (3980525569-1+2*2^9*c.k,105370958856566+c.lower,105371342258217+c.upper)) = pointBounds30339 := by
 decide +kernel
def cuts30340 : List PrefixCut := [⟨49,164542688,164542776⟩,
⟨128,426378349,426378585⟩]
theorem checked30340 : checkPrefixCuts (2^48) 3980656641 9 Manual.Count131072.C030340.packed 128 cuts30340 = true := by
 decide +kernel
def pointBounds30340 : List (Nat × Nat × Nat) := [(3980706816,105371543215367,105371926617341)]
theorem point_links_checked30340 : (cuts30340.take 1).map (fun c => (3980656641-1+2*2^9*c.k,105371378672679+c.lower,105371762074565+c.upper)) = pointBounds30340 := by
 decide +kernel
def cuts30341 : List PrefixCut := [⟨43,139082528,139082607⟩,
⟨128,419364199,419364439⟩]
theorem checked30341 : checkPrefixCuts (2^48) 3980787713 9 Manual.Count131072.C030341.packed 128 cuts30341 = true := by
 decide +kernel
def pointBounds30341 : List (Nat × Nat × Nat) := [(3980831744,105371944133556,105372327535757)]
theorem point_links_checked30341 : (cuts30341.take 1).map (fun c => (3980787713-1+2*2^9*c.k,105371805051028+c.lower,105372188453150+c.upper)) = pointBounds30341 := by
 decide +kernel
def cuts30342 : List PrefixCut := [⟨37,120836009,120836076⟩,
⟨128,416380892,416381123⟩]
theorem checked30342 : checkPrefixCuts (2^48) 3980918785 9 Manual.Count131072.C030342.packed 128 cuts30342 = true := by
 decide +kernel
def pointBounds30342 : List (Nat × Nat × Nat) := [(3980956672,105372345251236,105372728653665)]
theorem point_links_checked30342 : (cuts30342.take 1).map (fun c => (3980918785-1+2*2^9*c.k,105372224415227+c.lower,105372607817589+c.upper)) = pointBounds30342 := by
 decide +kernel
def cuts30343 : List PrefixCut := [⟨31,101035153,101035212⟩,
⟨128,424568594,424568833⟩]
theorem checked30343 : checkPrefixCuts (2^48) 3981049857 9 Manual.Count131072.C030343.packed 128 cuts30343 = true := by
 decide +kernel
def pointBounds30343 : List (Nat × Nat × Nat) := [(3981081600,105372741831272,105373125233924)]
theorem point_links_checked30343 : (cuts30343.take 1).map (fun c => (3981049857-1+2*2^9*c.k,105372640796119+c.lower,105373024198712+c.upper)) = pointBounds30343 := by
 decide +kernel
def cuts30344 : List PrefixCut := [⟨25,82861725,82861772⟩,
⟨128,419959165,419959396⟩]
theorem checked30344 : checkPrefixCuts (2^48) 3981180929 9 Manual.Count131072.C030344.packed 128 cuts30344 = true := by
 decide +kernel
def pointBounds30344 : List (Nat × Nat × Nat) := [(3981206528,105373148226438,105373531629317)]
theorem point_links_checked30344 : (cuts30344.take 1).map (fun c => (3981180929-1+2*2^9*c.k,105373065364713+c.lower,105373448767545+c.upper)) = pointBounds30344 := by
 decide +kernel
def cuts30345 : List PrefixCut := [⟨19,59528435,59528471⟩,
⟨128,415067128,415067366⟩]
theorem checked30345 : checkPrefixCuts (2^48) 3981312001 9 Manual.Count131072.C030345.packed 128 cuts30345 = true := by
 decide +kernel
def pointBounds30345 : List (Nat × Nat × Nat) := [(3981331456,105373544852313,105373928255412)]
theorem point_links_checked30345 : (cuts30345.take 1).map (fun c => (3981312001-1+2*2^9*c.k,105373485323878+c.lower,105373868726941+c.upper)) = pointBounds30345 := by
 decide +kernel
def cuts30346 : List PrefixCut := [⟨13,42347255,42347281⟩,
⟨128,416750224,416750466⟩]
theorem checked30346 : checkPrefixCuts (2^48) 3981443073 9 Manual.Count131072.C030346.packed 128 cuts30346 = true := by
 decide +kernel
def pointBounds30346 : List (Nat × Nat × Nat) := [(3981456384,105373942738261,105374326141588)]
theorem point_links_checked30346 : (cuts30346.take 1).map (fun c => (3981443073-1+2*2^9*c.k,105373900391006+c.lower,105374283794307+c.upper)) = pointBounds30346 := by
 decide +kernel
def cuts30347 : List PrefixCut := [⟨7,23399818,23399832⟩,
⟨128,423947193,423947433⟩]
theorem checked30347 : checkPrefixCuts (2^48) 3981574145 9 Manual.Count131072.C030347.packed 128 cuts30347 = true := by
 decide +kernel
def pointBounds30347 : List (Nat × Nat × Nat) := [(3981581312,105374340541048,105374723944605)]
theorem point_links_checked30347 : (cuts30347.take 1).map (fun c => (3981574145-1+2*2^9*c.k,105374317141230+c.lower,105374700544773+c.upper)) = pointBounds30347 := by
 decide +kernel
def cuts30348 : List PrefixCut := [⟨1,2191453,2191455⟩,
⟨123,400888236,400888464⟩,
⟨128,418631368,418631604⟩]
theorem checked30348 : checkPrefixCuts (2^48) 3981705217 9 Manual.Count131072.C030348.packed 128 cuts30348 = true := by
 decide +kernel
def pointBounds30348 : List (Nat × Nat × Nat) := [(3981706240,105374743279876,105375126683661),(3981831168,105375141976659,105375525380670)]
theorem point_links_checked30348 : (cuts30348.take 2).map (fun c => (3981705217-1+2*2^9*c.k,105374741088423+c.lower,105375124492206+c.upper)) = pointBounds30348 := by
 decide +kernel
def cuts30349 : List PrefixCut := [⟨117,384758351,384758573⟩,
⟨128,420738285,420738528⟩]
theorem checked30349 : checkPrefixCuts (2^48) 3981836289 9 Manual.Count131072.C030349.packed 128 cuts30349 = true := by
 decide +kernel
def pointBounds30349 : List (Nat × Nat × Nat) := [(3981956096,105375544478142,105375927882383)]
theorem point_links_checked30349 : (cuts30349.take 1).map (fun c => (3981836289-1+2*2^9*c.k,105375159719791+c.lower,105375543123810+c.upper)) = pointBounds30349 := by
 decide +kernel
def cuts30350 : List PrefixCut := [⟨111,366791709,366791912⟩,
⟨128,422138239,422138472⟩]
theorem checked30350 : checkPrefixCuts (2^48) 3981967361 9 Manual.Count131072.C030350.packed 128 cuts30350 = true := by
 decide +kernel
def pointBounds30350 : List (Nat × Nat × Nat) := [(3982081024,105375947249785,105376330654250)]
theorem point_links_checked30350 : (cuts30350.take 1).map (fun c => (3981967361-1+2*2^9*c.k,105375580458076+c.lower,105375963862338+c.upper)) = pointBounds30350 := by
 decide +kernel
def cuts30351 : List PrefixCut := [⟨105,334477262,334477452⟩,
⟨128,409330505,409330740⟩]
theorem checked30351 : checkPrefixCuts (2^48) 3982098433 9 Manual.Count131072.C030351.packed 128 cuts30351 = true := by
 decide +kernel
def pointBounds30351 : List (Nat × Nat × Nat) := [(3982205952,105376337073577,105376720478262)]
theorem point_links_checked30351 : (cuts30351.take 1).map (fun c => (3982098433-1+2*2^9*c.k,105376002596315+c.lower,105376386000810+c.upper)) = pointBounds30351 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000010
