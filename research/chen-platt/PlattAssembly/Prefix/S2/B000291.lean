import PlattAssemblyKernel
import PlattCertificates.Count131072.C019312
import PlattCertificates.Count131072.C019313
import PlattCertificates.Count131072.C019314
import PlattCertificates.Count131072.C019315
import PlattCertificates.Count131072.C019316
import PlattCertificates.Count131072.C019317
import PlattCertificates.Count131072.C019318
import PlattCertificates.Count131072.C019319
import PlattCertificates.Count131072.C019320
import PlattCertificates.Count131072.C019321
import PlattCertificates.Count131072.C019322
import PlattCertificates.Count131072.C019323
import PlattCertificates.Count131072.C019324
import PlattCertificates.Count131072.C019325
import PlattCertificates.Count131072.C019326
import PlattCertificates.Count131072.C019327
import PlattCertificates.Count131072.C019328
import PlattCertificates.Count131072.C019329
import PlattCertificates.Count131072.C019330
import PlattCertificates.Count131072.C019331
import PlattCertificates.Count131072.C019332
import PlattCertificates.Count131072.C019333
import PlattCertificates.Count131072.C019334
import PlattCertificates.Count131072.C019335
import PlattCertificates.Count131072.C019336
import PlattCertificates.Count131072.C019337
import PlattCertificates.Count131072.C019338
import PlattCertificates.Count131072.C019339
import PlattCertificates.Count131072.C019340
import PlattCertificates.Count131072.C019341
import PlattCertificates.Count131072.C019342
import PlattCertificates.Count131072.C019343
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000291
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19312 : List PrefixCut := [⟨72,374266435,374266659⟩,
⟨128,666144466,666144863⟩]
theorem checked19312 : checkPrefixCuts (2^48) 2535194625 9 Manual.Count131072.C019312.packed 128 cuts19312 = true := by
 decide +kernel
def pointBounds19312 : List (Nat × Nat × Nat) := [(2535268352,99567191359200,99567571460706)]
theorem point_links_checked19312 : (cuts19312.take 1).map (fun c => (2535194625-1+2*2^9*c.k,99566817092765+c.lower,99567197194047+c.upper)) = pointBounds19312 := by
 decide +kernel
def cuts19313 : List PrefixCut := [⟨22,115905613,115905682⟩,
⟨100,521789145,521789453⟩,
⟨128,667997335,667997729⟩]
theorem checked19313 : checkPrefixCuts (2^48) 2535325697 9 Manual.Count131072.C019313.packed 128 cuts19313 = true := by
 decide +kernel
def pointBounds19313 : List (Nat × Nat × Nat) := [(2535348224,99567599142844,99567979244592),(2535428096,99568005026376,99568385128363)]
theorem point_links_checked19313 : (cuts19313.take 2).map (fun c => (2535325697-1+2*2^9*c.k,99567483237231+c.lower,99567863338910+c.upper)) = pointBounds19313 := by
 decide +kernel
def cuts19314 : List PrefixCut := [⟨50,263881066,263881222⟩,
⟨128,670849084,670849482⟩]
theorem checked19314 : checkPrefixCuts (2^48) 2535456769 9 Manual.Count131072.C019314.packed 128 cuts19314 = true := by
 decide +kernel
def pointBounds19314 : List (Nat × Nat × Nat) := [(2535507968,99568415115632,99568795217861),(2535587840,99568822083650,99569202186121)]
theorem point_links_checked19314 : (cuts19314.take 2).map (fun c => (2535456769-1+2*2^9*c.k,99568151234566+c.lower,99568531336639+c.upper)) = pointBounds19314 := by
 decide +kernel
def cuts19315 : List PrefixCut := [⟨78,409619373,409619619⟩,
⟨128,667928221,667928622⟩]
theorem checked19315 : checkPrefixCuts (2^48) 2535587841 9 Manual.Count131072.C019315.packed 128 cuts19315 = true := by
 decide +kernel
def pointBounds19315 : List (Nat × Nat × Nat) := [(2535667712,99569231703023,99569611805740)]
theorem point_links_checked19315 : (cuts19315.take 1).map (fun c => (2535587841-1+2*2^9*c.k,99568822083650+c.lower,99569202186121+c.upper)) = pointBounds19315 := by
 decide +kernel
def cuts19316 : List PrefixCut := [⟨28,147301429,147301518⟩,
⟨106,553897984,553898316⟩,
⟨128,667227687,667228088⟩]
theorem checked19316 : checkPrefixCuts (2^48) 2535718913 9 Manual.Count131072.C019316.packed 128 cuts19316 = true := by
 decide +kernel
def pointBounds19316 : List (Nat × Nat × Nat) := [(2535747584,99569637313300,99570017416261),(2535827456,99570043909855,99570424013059)]
theorem point_links_checked19316 : (cuts19316.take 2).map (fun c => (2535718913-1+2*2^9*c.k,99569490011871+c.lower,99569870114743+c.upper)) = pointBounds19316 := by
 decide +kernel
def cuts19317 : List PrefixCut := [⟨56,296361969,296362143⟩,
⟨128,672743045,672743439⟩]
theorem checked19317 : checkPrefixCuts (2^48) 2535849985 9 Manual.Count131072.C019317.packed 128 cuts19317 = true := by
 decide +kernel
def pointBounds19317 : List (Nat × Nat × Nat) := [(2535907328,99570453601527,99570833704974)]
theorem point_links_checked19317 : (cuts19317.take 1).map (fun c => (2535849985-1+2*2^9*c.k,99570157239558+c.lower,99570537342831+c.upper)) = pointBounds19317 := by
 decide +kernel
def cuts19318 : List PrefixCut := [⟨6,31965803,31965821⟩,
⟨84,444961325,444961585⟩,
⟨128,679034490,679034887⟩]
theorem checked19318 : checkPrefixCuts (2^48) 2535981057 9 Manual.Count131072.C019318.packed 128 cuts19318 = true := by
 decide +kernel
def pointBounds19318 : List (Nat × Nat × Nat) := [(2535987200,99570861948406,99571242052091),(2536067072,99571274943928,99571655047855)]
theorem point_links_checked19318 : (cuts19318.take 2).map (fun c => (2535981057-1+2*2^9*c.k,99570829982603+c.lower,99571210086270+c.upper)) = pointBounds19318 := by
 decide +kernel
def cuts19319 : List PrefixCut := [⟨34,175912827,175912931⟩,
⟨112,590547209,590547560⟩,
⟨128,675336986,675337388⟩]
theorem checked19319 : checkPrefixCuts (2^48) 2536112129 9 Manual.Count131072.C019319.packed 128 cuts19319 = true := by
 decide +kernel
def pointBounds19319 : List (Nat × Nat × Nat) := [(2536146944,99571684929920,99572065034088),(2536226816,99572099564302,99572479668717)]
theorem point_links_checked19319 : (cuts19319.take 2).map (fun c => (2536112129-1+2*2^9*c.k,99571509017093+c.lower,99571889121157+c.upper)) = pointBounds19319 := by
 decide +kernel
def cuts19320 : List PrefixCut := [⟨62,326280126,326280319⟩,
⟨128,673304457,673304862⟩]
theorem checked19320 : checkPrefixCuts (2^48) 2536243201 9 Manual.Count131072.C019320.packed 128 cuts19320 = true := by
 decide +kernel
def pointBounds19320 : List (Nat × Nat × Nat) := [(2536306688,99572510634205,99572890738864)]
theorem point_links_checked19320 : (cuts19320.take 1).map (fun c => (2536243201-1+2*2^9*c.k,99572184354079+c.lower,99572564458545+c.upper)) = pointBounds19320 := by
 decide +kernel
def cuts19321 : List PrefixCut := [⟨12,65697215,65697253⟩,
⟨90,478849697,478849981⟩,
⟨128,675045391,675045792⟩]
theorem checked19321 : checkPrefixCuts (2^48) 2536374273 9 Manual.Count131072.C019321.packed 128 cuts19321 = true := by
 decide +kernel
def pointBounds19321 : List (Nat × Nat × Nat) := [(2536386560,99572923355751,99573303460660),(2536466432,99573336508233,99573716613388)]
theorem point_links_checked19321 : (cuts19321.take 2).map (fun c => (2536374273-1+2*2^9*c.k,99572857658536+c.lower,99573237763407+c.upper)) = pointBounds19321 := by
 decide +kernel
def cuts19322 : List PrefixCut := [⟨40,205624967,205625090⟩,
⟨118,609763256,609763617⟩,
⟨128,662360221,662360614⟩]
theorem checked19322 : checkPrefixCuts (2^48) 2536505345 9 Manual.Count131072.C019322.packed 128 cuts19322 = true := by
 decide +kernel
def pointBounds19322 : List (Nat × Nat × Nat) := [(2536546304,99573738328894,99574118434289),(2536626176,99574142467183,99574522572816)]
theorem point_links_checked19322 : (cuts19322.take 2).map (fun c => (2536505345-1+2*2^9*c.k,99573532703927+c.lower,99573912809199+c.upper)) = pointBounds19322 := by
 decide +kernel
def cuts19323 : List PrefixCut := [⟨68,356632795,356633009⟩,
⟨128,677749395,677749798⟩]
theorem checked19323 : checkPrefixCuts (2^48) 2536636417 9 Manual.Count131072.C019323.packed 128 cuts19323 = true := by
 decide +kernel
def pointBounds19323 : List (Nat × Nat × Nat) := [(2536706048,99574551696943,99574931802822)]
theorem point_links_checked19323 : (cuts19323.take 1).map (fun c => (2536636417-1+2*2^9*c.k,99574195064148+c.lower,99574575169813+c.upper)) = pointBounds19323 := by
 decide +kernel
def cuts19324 : List PrefixCut := [⟨18,92760630,92760684⟩,
⟨96,496749761,496750058⟩,
⟨128,664177954,664178351⟩]
theorem checked19324 : checkPrefixCuts (2^48) 2536767489 9 Manual.Count131072.C019324.packed 128 cuts19324 = true := by
 decide +kernel
def pointBounds19324 : List (Nat × Nat × Nat) := [(2536785920,99574965574173,99575345680295),(2536865792,99575369563304,99575749669669)]
theorem point_links_checked19324 : (cuts19324.take 2).map (fun c => (2536767489-1+2*2^9*c.k,99574872813543+c.lower,99575252919611+c.upper)) = pointBounds19324 := by
 decide +kernel
def cuts19325 : List PrefixCut := [⟨46,245646254,245646397⟩,
⟨124,652272792,652273177⟩,
⟨128,674794978,674795376⟩]
theorem checked19325 : checkPrefixCuts (2^48) 2536898561 9 Manual.Count131072.C019325.packed 128 cuts19325 = true := by
 decide +kernel
def pointBounds19325 : List (Nat × Nat × Nat) := [(2536945664,99575782637751,99576162744359),(2537025536,99576189264289,99576569371139)]
theorem point_links_checked19325 : (cuts19325.take 2).map (fun c => (2536898561-1+2*2^9*c.k,99575536991497+c.lower,99575917097962+c.upper)) = pointBounds19325 := by
 decide +kernel
def cuts19326 : List PrefixCut := [⟨74,391635761,391635992⟩,
⟨128,673983405,673983800⟩]
theorem checked19326 : checkPrefixCuts (2^48) 2537029633 9 Manual.Count131072.C019326.packed 128 cuts19326 = true := by
 decide +kernel
def pointBounds19326 : List (Nat × Nat × Nat) := [(2537105408,99576603422236,99576983529330)]
theorem point_links_checked19326 : (cuts19326.take 1).map (fun c => (2537029633-1+2*2^9*c.k,99576211786475+c.lower,99576591893338+c.upper)) = pointBounds19326 := by
 decide +kernel
def cuts19327 : List PrefixCut := [⟨24,125806388,125806461⟩,
⟨102,536942964,536943283⟩,
⟨128,678496992,678497396⟩]
theorem checked19327 : checkPrefixCuts (2^48) 2537160705 9 Manual.Count131072.C019327.packed 128 cuts19327 = true := by
 decide +kernel
def pointBounds19327 : List (Nat × Nat × Nat) := [(2537185280,99577011576268,99577391683599),(2537265152,99577422712844,99577802820421)]
theorem point_links_checked19327 : (cuts19327.take 2).map (fun c => (2537160705-1+2*2^9*c.k,99576885769880+c.lower,99577265877138+c.upper)) = pointBounds19327 := by
 decide +kernel
def cuts19328 : List PrefixCut := [⟨52,278888061,278888226⟩,
⟨128,669476547,669476949⟩]
theorem checked19328 : checkPrefixCuts (2^48) 2537291777 9 Manual.Count131072.C019328.packed 128 cuts19328 = true := by
 decide +kernel
def pointBounds19328 : List (Nat × Nat × Nat) := [(2537345024,99577843154933,99578223262760)]
theorem point_links_checked19328 : (cuts19328.take 1).map (fun c => (2537291777-1+2*2^9*c.k,99577564266872+c.lower,99577944374534+c.upper)) = pointBounds19328 := by
 decide +kernel
def cuts19329 : List PrefixCut := [⟨2,11092940,11092946⟩,
⟨80,418419049,418419295⟩,
⟨128,670329254,670329646⟩]
theorem checked19329 : checkPrefixCuts (2^48) 2537422849 9 Manual.Count131072.C019329.packed 128 cuts19329 = true := by
 decide +kernel
def pointBounds19329 : List (Nat × Nat × Nat) := [(2537424896,99578244836359,99578624944429),(2537504768,99578652162468,99579032270778)]
theorem point_links_checked19329 : (cuts19329.take 2).map (fun c => (2537422849-1+2*2^9*c.k,99578233743419+c.lower,99578613851483+c.upper)) = pointBounds19329 := by
 decide +kernel
def cuts19330 : List PrefixCut := [⟨30,161282097,161282194⟩,
⟨108,573352178,573352523⟩,
⟨128,679833868,679834276⟩]
theorem checked19330 : checkPrefixCuts (2^48) 2537553921 9 Manual.Count131072.C019330.packed 128 cuts19330 = true := by
 decide +kernel
def pointBounds19330 : List (Nat × Nat × Nat) := [(2537584640,99579065354770,99579445463323),(2537664512,99579477424851,99579857533652)]
theorem point_links_checked19330 : (cuts19330.take 2).map (fun c => (2537553921-1+2*2^9*c.k,99578904072673+c.lower,99579284181129+c.upper)) = pointBounds19330 := by
 decide +kernel
def cuts19331 : List PrefixCut := [⟨58,311343117,311343298⟩,
⟨128,671036625,671037017⟩]
theorem checked19331 : checkPrefixCuts (2^48) 2537684993 9 Manual.Count131072.C019331.packed 128 cuts19331 = true := by
 decide +kernel
def pointBounds19331 : List (Nat × Nat × Nat) := [(2537744384,99579895249658,99580275358703)]
theorem point_links_checked19331 : (cuts19331.take 1).map (fun c => (2537684993-1+2*2^9*c.k,99579583906541+c.lower,99579964015405+c.upper)) = pointBounds19331 := by
 decide +kernel
def cuts19332 : List PrefixCut := [⟨8,39595608,39595634⟩,
⟨86,459057756,459058029⟩,
⟨128,672554602,672555006⟩]
theorem checked19332 : checkPrefixCuts (2^48) 2537816065 9 Manual.Count131072.C019332.packed 128 cuts19332 = true := by
 decide +kernel
def pointBounds19332 : List (Nat × Nat × Nat) := [(2537824256,99580294538774,99580674648056),(2537904128,99580714000922,99581094110451)]
theorem point_links_checked19332 : (cuts19332.take 2).map (fun c => (2537816065-1+2*2^9*c.k,99580254943166+c.lower,99580635052422+c.upper)) = pointBounds19332 := by
 decide +kernel
def cuts19333 : List PrefixCut := [⟨36,186987027,186987139⟩,
⟨114,599657721,599658078⟩,
⟨128,674959582,674959982⟩]
theorem checked19333 : checkPrefixCuts (2^48) 2537947137 9 Manual.Count131072.C019333.packed 128 cuts19333 = true := by
 decide +kernel
def pointBounds19333 : List (Nat × Nat × Nat) := [(2537984000,99581114484795,99581494594567),(2538063872,99581527155489,99581907265506)]
theorem point_links_checked19333 : (cuts19333.take 2).map (fun c => (2537947137-1+2*2^9*c.k,99580927497768+c.lower,99581307607428+c.upper)) = pointBounds19333 := by
 decide +kernel
def cuts19334 : List PrefixCut := [⟨64,339130247,339130449⟩,
⟨128,674592113,674592513⟩]
theorem checked19334 : checkPrefixCuts (2^48) 2538078209 9 Manual.Count131072.C019334.packed 128 cuts19334 = true := by
 decide +kernel
def pointBounds19334 : List (Nat × Nat × Nat) := [(2538143744,99581941587597,99582321697859)]
theorem point_links_checked19334 : (cuts19334.take 1).map (fun c => (2538078209-1+2*2^9*c.k,99581602457350+c.lower,99581982567410+c.upper)) = pointBounds19334 := by
 decide +kernel
def cuts19335 : List PrefixCut := [⟨14,73412332,73412376⟩,
⟨92,477838069,477838354⟩,
⟨128,668014697,668015092⟩]
theorem checked19335 : checkPrefixCuts (2^48) 2538209281 9 Manual.Count131072.C019335.packed 128 cuts19335 = true := by
 decide +kernel
def pointBounds19335 : List (Nat × Nat × Nat) := [(2538223616,99582350461795,99582730572299),(2538303488,99582754887532,99583134998277)]
theorem point_links_checked19335 : (cuts19335.take 2).map (fun c => (2538209281-1+2*2^9*c.k,99582277049463+c.lower,99582657159923+c.upper)) = pointBounds19335 := by
 decide +kernel
def cuts19336 : List PrefixCut := [⟨42,219115468,219115604⟩,
⟨120,626176906,626177280⟩,
⟨128,669088936,669089334⟩]
theorem checked19336 : checkPrefixCuts (2^48) 2538340353 9 Manual.Count131072.C019336.packed 128 cuts19336 = true := by
 decide +kernel
def pointBounds19336 : List (Nat × Nat × Nat) := [(2538383360,99583164179628,99583544290619),(2538463232,99583571241066,99583951352295)]
theorem point_links_checked19336 : (cuts19336.take 2).map (fun c => (2538340353-1+2*2^9*c.k,99582945064160+c.lower,99583325175015+c.upper)) = pointBounds19336 := by
 decide +kernel
def cuts19337 : List PrefixCut := [⟨70,368128469,368128688⟩,
⟨128,682360087,682360489⟩]
theorem checked19337 : checkPrefixCuts (2^48) 2538471425 9 Manual.Count131072.C019337.packed 128 cuts19337 = true := by
 decide +kernel
def pointBounds19337 : List (Nat × Nat × Nat) := [(2538543104,99583982281565,99584362393037)]
theorem point_links_checked19337 : (cuts19337.take 1).map (fun c => (2538471425-1+2*2^9*c.k,99583614153096+c.lower,99583994264349+c.upper)) = pointBounds19337 := by
 decide +kernel
def cuts19338 : List PrefixCut := [⟨20,103670415,103670481⟩,
⟨98,516126345,516126656⟩,
⟨128,669352596,669352999⟩]
theorem checked19338 : checkPrefixCuts (2^48) 2538602497 9 Manual.Count131072.C019338.packed 128 cuts19338 = true := by
 decide +kernel
def pointBounds19338 : List (Nat × Nat × Nat) := [(2538622976,99584400183598,99584780295319),(2538702848,99584812639528,99585192751494)]
theorem point_links_checked19338 : (cuts19338.take 2).map (fun c => (2538602497-1+2*2^9*c.k,99584296513183+c.lower,99584676624838+c.upper)) = pointBounds19338 := by
 decide +kernel
def cuts19339 : List PrefixCut := [⟨48,248129507,248129653⟩,
⟨126,659561679,659562067⟩,
⟨128,668430998,668431392⟩]
theorem checked19339 : checkPrefixCuts (2^48) 2538733569 9 Manual.Count131072.C019339.packed 128 cuts19339 = true := by
 decide +kernel
def pointBounds19339 : List (Nat × Nat × Nat) := [(2538782720,99585213995286,99585594107490),(2538862592,99585625427458,99586005539904)]
theorem point_links_checked19339 : (cuts19339.take 2).map (fun c => (2538733569-1+2*2^9*c.k,99584965865779+c.lower,99585345977837+c.upper)) = pointBounds19339 := by
 decide +kernel
def cuts19340 : List PrefixCut := [⟨76,398891355,398891590⟩,
⟨128,671722439,671722831⟩]
theorem checked19340 : checkPrefixCuts (2^48) 2538864641 9 Manual.Count131072.C019340.packed 128 cuts19340 = true := by
 decide +kernel
def pointBounds19340 : List (Nat × Nat × Nat) := [(2538942464,99586033188132,99586413300819)]
theorem point_links_checked19340 : (cuts19340.take 1).map (fun c => (2538864641-1+2*2^9*c.k,99585634296777+c.lower,99586014409229+c.upper)) = pointBounds19340 := by
 decide +kernel
def cuts19341 : List PrefixCut := [⟨26,134251636,134251717⟩,
⟨104,543427833,543428157⟩,
⟨128,670579141,670579537⟩]
theorem checked19341 : checkPrefixCuts (2^48) 2538995713 9 Manual.Count131072.C019341.packed 128 cuts19341 = true := by
 decide +kernel
def pointBounds19341 : List (Nat × Nat × Nat) := [(2539022336,99586440270852,99586820383777),(2539102208,99586849447049,99587229560217)]
theorem point_links_checked19341 : (cuts19341.take 2).map (fun c => (2538995713-1+2*2^9*c.k,99586306019216+c.lower,99586686132060+c.upper)) = pointBounds19341 := by
 decide +kernel
def cuts19342 : List PrefixCut := [⟨54,286224506,286224676⟩,
⟨128,671209849,671210249⟩]
theorem checked19342 : checkPrefixCuts (2^48) 2539126785 9 Manual.Count131072.C019342.packed 128 cuts19342 = true := by
 decide +kernel
def pointBounds19342 : List (Nat × Nat × Nat) := [(2539182080,99587262822863,99587642936273)]
theorem point_links_checked19342 : (cuts19342.take 1).map (fun c => (2539126785-1+2*2^9*c.k,99586976598357+c.lower,99587356711597+c.upper)) = pointBounds19342 := by
 decide +kernel
def cuts19343 : List PrefixCut := [⟨4,20950497,20950509⟩,
⟨82,427316841,427317094⟩,
⟨128,667960436,667960833⟩]
theorem checked19343 : checkPrefixCuts (2^48) 2539257857 9 Manual.Count131072.C019343.packed 128 cuts19343 = true := by
 decide +kernel
def pointBounds19343 : List (Nat × Nat × Nat) := [(2539261952,99587668758703,99588048872355),(2539341824,99588075125047,99588455238940)]
theorem point_links_checked19343 : (cuts19343.take 2).map (fun c => (2539257857-1+2*2^9*c.k,99587647808206+c.lower,99588027921846+c.upper)) = pointBounds19343 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000291
