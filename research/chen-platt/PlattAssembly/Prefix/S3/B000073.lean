import PlattAssemblyKernel
import PlattCertificates.Count131072.C022336
import PlattCertificates.Count131072.C022337
import PlattCertificates.Count131072.C022338
import PlattCertificates.Count131072.C022339
import PlattCertificates.Count131072.C022340
import PlattCertificates.Count131072.C022341
import PlattCertificates.Count131072.C022342
import PlattCertificates.Count131072.C022343
import PlattCertificates.Count131072.C022344
import PlattCertificates.Count131072.C022345
import PlattCertificates.Count131072.C022346
import PlattCertificates.Count131072.C022347
import PlattCertificates.Count131072.C022348
import PlattCertificates.Count131072.C022349
import PlattCertificates.Count131072.C022350
import PlattCertificates.Count131072.C022351
import PlattCertificates.Count131072.C022352
import PlattCertificates.Count131072.C022353
import PlattCertificates.Count131072.C022354
import PlattCertificates.Count131072.C022355
import PlattCertificates.Count131072.C022356
import PlattCertificates.Count131072.C022357
import PlattCertificates.Count131072.C022358
import PlattCertificates.Count131072.C022359
import PlattCertificates.Count131072.C022360
import PlattCertificates.Count131072.C022361
import PlattCertificates.Count131072.C022362
import PlattCertificates.Count131072.C022363
import PlattCertificates.Count131072.C022364
import PlattCertificates.Count131072.C022365
import PlattCertificates.Count131072.C022366
import PlattCertificates.Count131072.C022367
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000073
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22336 : List PrefixCut := [⟨10,45895337,45895364⟩,
⟨100,450208930,450209188⟩,
⟨128,577808465,577808798⟩]
theorem checked22336 : checkPrefixCuts (2^48) 2931556353 9 Manual.Count131072.C022336.packed 128 cuts22336 = true := by
 decide +kernel
def pointBounds22336 : List (Nat × Nat × Nat) := [(2931566592,101448851806708,101449233002916),(2931658752,101449256120301,101449637316740)]
theorem point_links_checked22336 : (cuts22336.take 2).map (fun c => (2931556353-1+2*2^9*c.k,101448805911371+c.lower,101449187107552+c.upper)) = pointBounds22336 := by
 decide +kernel
def cuts22337 : List PrefixCut := [⟨62,276413307,276413471⟩,
⟨128,568949800,568950131⟩]
theorem checked22337 : checkPrefixCuts (2^48) 2931687425 9 Manual.Count131072.C022337.packed 128 cuts22337 = true := by
 decide +kernel
def pointBounds22337 : List (Nat × Nat × Nat) := [(2931750912,101449660133143,101450041329821)]
theorem point_links_checked22337 : (cuts22337.take 1).map (fun c => (2931687425-1+2*2^9*c.k,101449383719836+c.lower,101449764916350+c.upper)) = pointBounds22337 := by
 decide +kernel
def cuts22338 : List PrefixCut := [⟨24,109543459,109543522⟩,
⟨114,517371078,517371374⟩,
⟨128,586013132,586013467⟩]
theorem checked22338 : checkPrefixCuts (2^48) 2931818497 9 Manual.Count131072.C022338.packed 128 cuts22338 = true := by
 decide +kernel
def pointBounds22338 : List (Nat × Nat × Nat) := [(2931843072,101450062213095,101450443410003),(2931935232,101450470040714,101450851237855)]
theorem point_links_checked22338 : (cuts22338.take 2).map (fun c => (2931818497-1+2*2^9*c.k,101449952669636+c.lower,101450333866481+c.upper)) = pointBounds22338 := by
 decide +kernel
def cuts22339 : List PrefixCut := [⟨76,343108885,343109081⟩,
⟨128,576098997,576099326⟩]
theorem checked22339 : checkPrefixCuts (2^48) 2931949569 9 Manual.Count131072.C022339.packed 128 cuts22339 = true := by
 decide +kernel
def pointBounds22339 : List (Nat × Nat × Nat) := [(2932027392,101450881791653,101451262989029)]
theorem point_links_checked22339 : (cuts22339.take 1).map (fun c => (2931949569-1+2*2^9*c.k,101450538682768+c.lower,101450919879948+c.upper)) = pointBounds22339 := by
 decide +kernel
def cuts22340 : List PrefixCut := [⟨38,168667976,168668076⟩,
⟨128,573673273,573673612⟩]
theorem checked22340 : checkPrefixCuts (2^48) 2932080641 9 Manual.Count131072.C022340.packed 128 cuts22340 = true := by
 decide +kernel
def pointBounds22340 : List (Nat × Nat × Nat) := [(2932119552,101451283449741,101451664647350),(2932211712,101451688455038,101452069652886)]
theorem point_links_checked22340 : (cuts22340.take 2).map (fun c => (2932080641-1+2*2^9*c.k,101451114781765+c.lower,101451495979274+c.upper)) = pointBounds22340 := by
 decide +kernel
def cuts22341 : List PrefixCut := [⟨90,404320577,404320799⟩,
⟨128,574415584,574415901⟩]
theorem checked22341 : checkPrefixCuts (2^48) 2932211713 9 Manual.Count131072.C022341.packed 128 cuts22341 = true := by
 decide +kernel
def pointBounds22341 : List (Nat × Nat × Nat) := [(2932303872,101452092775615,101452473973685)]
theorem point_links_checked22341 : (cuts22341.take 1).map (fun c => (2932211713-1+2*2^9*c.k,101451688455038+c.lower,101452069652886+c.upper)) = pointBounds22341 := by
 decide +kernel
def cuts22342 : List PrefixCut := [⟨52,232485079,232485210⟩,
⟨128,586484222,586484556⟩]
theorem checked22342 : checkPrefixCuts (2^48) 2932342785 9 Manual.Count131072.C022342.packed 128 cuts22342 = true := by
 decide +kernel
def pointBounds22342 : List (Nat × Nat × Nat) := [(2932396032,101452495355701,101452876553997)]
theorem point_links_checked22342 : (cuts22342.take 1).map (fun c => (2932342785-1+2*2^9*c.k,101452262870622+c.lower,101452644068787+c.upper)) = pointBounds22342 := by
 decide +kernel
def cuts22343 : List PrefixCut := [⟨14,65269961,65269998⟩,
⟨104,472240025,472240290⟩,
⟨128,579355480,579355806⟩]
theorem checked22343 : checkPrefixCuts (2^48) 2932473857 9 Manual.Count131072.C022343.packed 128 cuts22343 = true := by
 decide +kernel
def pointBounds22343 : List (Nat × Nat × Nat) := [(2932488192,101452914624805,101453295823341),(2932580352,101453321594869,101453702793633)]
theorem point_links_checked22343 : (cuts22343.take 2).map (fun c => (2932473857-1+2*2^9*c.k,101452849354844+c.lower,101453230553343+c.upper)) = pointBounds22343 := by
 decide +kernel
def cuts22344 : List PrefixCut := [⟨66,297730192,297730370⟩,
⟨128,580097317,580097656⟩]
theorem checked22344 : checkPrefixCuts (2^48) 2932604929 9 Manual.Count131072.C022344.packed 128 cuts22344 = true := by
 decide +kernel
def pointBounds22344 : List (Nat × Nat × Nat) := [(2932672512,101453726440516,101454107639519)]
theorem point_links_checked22344 : (cuts22344.take 1).map (fun c => (2932604929-1+2*2^9*c.k,101453428710324+c.lower,101453809909149+c.upper)) = pointBounds22344 := by
 decide +kernel
def cuts22345 : List PrefixCut := [⟨28,128512430,128512502⟩,
⟨118,529685606,529685906⟩,
⟨128,574696838,574697165⟩]
theorem checked22345 : checkPrefixCuts (2^48) 2932736001 9 Manual.Count131072.C022345.packed 128 cuts22345 = true := by
 decide +kernel
def pointBounds22345 : List (Nat × Nat × Nat) := [(2932764672,101454137320071,101454518519307),(2932856832,101454538493247,101454919692711)]
theorem point_links_checked22345 : (cuts22345.take 2).map (fun c => (2932736001-1+2*2^9*c.k,101454008807641+c.lower,101454390006805+c.upper)) = pointBounds22345 := by
 decide +kernel
def cuts22346 : List PrefixCut := [⟨80,358260779,358260985⟩,
⟨128,575438891,575439220⟩]
theorem checked22346 : checkPrefixCuts (2^48) 2932867073 9 Manual.Count131072.C022346.packed 128 cuts22346 = true := by
 decide +kernel
def pointBounds22346 : List (Nat × Nat × Nat) := [(2932948992,101454941765258,101455322964955)]
theorem point_links_checked22346 : (cuts22346.take 1).map (fun c => (2932867073-1+2*2^9*c.k,101454583504479+c.lower,101454964703970+c.upper)) = pointBounds22346 := by
 decide +kernel
def cuts22347 : List PrefixCut := [⟨42,190783625,190783732⟩,
⟨128,571478661,571478981⟩]
theorem checked22347 : checkPrefixCuts (2^48) 2932998145 9 Manual.Count131072.C022347.packed 128 cuts22347 = true := by
 decide +kernel
def pointBounds22347 : List (Nat × Nat × Nat) := [(2933041152,101455349726995,101455730926922)]
theorem point_links_checked22347 : (cuts22347.take 1).map (fun c => (2932998145-1+2*2^9*c.k,101455158943370+c.lower,101455540143190+c.upper)) = pointBounds22347 := by
 decide +kernel
def cuts22348 : List PrefixCut := [⟨4,17369477,17369488⟩,
⟨94,423002478,423002720⟩,
⟨128,577498576,577498911⟩]
theorem checked22348 : checkPrefixCuts (2^48) 2933129217 9 Manual.Count131072.C022348.packed 128 cuts22348 = true := by
 decide +kernel
def pointBounds22348 : List (Nat × Nat × Nat) := [(2933133312,101455747791508,101456128991659),(2933225472,101456153424509,101456534624891)]
theorem point_links_checked22348 : (cuts22348.take 2).map (fun c => (2933129217-1+2*2^9*c.k,101455730422031+c.lower,101456111622171+c.upper)) = pointBounds22348 := by
 decide +kernel
def cuts22349 : List PrefixCut := [⟨56,249780763,249780909⟩,
⟨128,575457683,575458016⟩]
theorem checked22349 : checkPrefixCuts (2^48) 2933260289 9 Manual.Count131072.C022349.packed 128 cuts22349 = true := by
 decide +kernel
def pointBounds22349 : List (Nat × Nat × Nat) := [(2933317632,101456557701370,101456938901991)]
theorem point_links_checked22349 : (cuts22349.take 1).map (fun c => (2933260289-1+2*2^9*c.k,101456307920607+c.lower,101456689121082+c.upper)) = pointBounds22349 := by
 decide +kernel
def cuts22350 : List PrefixCut := [⟨18,81369963,81370014⟩,
⟨108,487444468,487444755⟩,
⟨128,575144136,575144470⟩]
theorem checked22350 : checkPrefixCuts (2^48) 2933391361 9 Manual.Count131072.C022350.packed 128 cuts22350 = true := by
 decide +kernel
def pointBounds22350 : List (Nat × Nat × Nat) := [(2933409792,101456964748253,101457345949112),(2933501952,101457370822758,101457752023853)]
theorem point_links_checked22350 : (cuts22350.take 2).map (fun c => (2933391361-1+2*2^9*c.k,101456883378290+c.lower,101457264579098+c.upper)) = pointBounds22350 := by
 decide +kernel
def cuts22351 : List PrefixCut := [⟨70,308671132,308671310⟩,
⟨128,567538455,567538777⟩]
theorem checked22351 : checkPrefixCuts (2^48) 2933522433 9 Manual.Count131072.C022351.packed 128 cuts22351 = true := by
 decide +kernel
def pointBounds22351 : List (Nat × Nat × Nat) := [(2933594112,101457767193558,101458148394878)]
theorem point_links_checked22351 : (cuts22351.take 1).map (fun c => (2933522433-1+2*2^9*c.k,101457458522426+c.lower,101457839723568+c.upper)) = pointBounds22351 := by
 decide +kernel
def cuts22352 : List PrefixCut := [⟨32,150156027,150156107⟩,
⟨122,556863969,556864287⟩,
⟨128,582768497,582768829⟩]
theorem checked22352 : checkPrefixCuts (2^48) 2933653505 9 Manual.Count131072.C022352.packed 128 cuts22352 = true := by
 decide +kernel
def pointBounds22352 : List (Nat × Nat × Nat) := [(2933686272,101458176216908,101458557418452),(2933778432,101458582924850,101458964126632)]
theorem point_links_checked22352 : (cuts22352.take 2).map (fun c => (2933653505-1+2*2^9*c.k,101458026060881+c.lower,101458407262345+c.upper)) = pointBounds22352 := by
 decide +kernel
def cuts22353 : List PrefixCut := [⟨84,378008293,378008510⟩,
⟨128,576602099,576602429⟩]
theorem checked22353 : checkPrefixCuts (2^48) 2933784577 9 Manual.Count131072.C022353.packed 128 cuts22353 = true := by
 decide +kernel
def pointBounds22353 : List (Nat × Nat × Nat) := [(2933870592,101458986837671,101459368039684)]
theorem point_links_checked22353 : (cuts22353.take 1).map (fun c => (2933784577-1+2*2^9*c.k,101458608829378+c.lower,101458990031174+c.upper)) = pointBounds22353 := by
 decide +kernel
def cuts22354 : List PrefixCut := [⟨46,202907909,202908020⟩,
⟨128,582428342,582428668⟩]
theorem checked22354 : checkPrefixCuts (2^48) 2933915649 9 Manual.Count131072.C022354.packed 128 cuts22354 = true := by
 decide +kernel
def pointBounds22354 : List (Nat × Nat × Nat) := [(2933962752,101459388339386,101459769541623)]
theorem point_links_checked22354 : (cuts22354.take 1).map (fun c => (2933915649-1+2*2^9*c.k,101459185431477+c.lower,101459566633603+c.upper)) = pointBounds22354 := by
 decide +kernel
def cuts22355 : List PrefixCut := [⟨8,35975206,35975227⟩,
⟨98,443974972,443975226⟩,
⟨128,572617407,572617739⟩]
theorem checked22355 : checkPrefixCuts (2^48) 2934046721 9 Manual.Count131072.C022355.packed 128 cuts22355 = true := by
 decide +kernel
def pointBounds22355 : List (Nat × Nat × Nat) := [(2934054912,101459803835025,101460185037498),(2934147072,101460211834791,101460593037497)]
theorem point_links_checked22355 : (cuts22355.take 2).map (fun c => (2934046721-1+2*2^9*c.k,101459767859819+c.lower,101460149062271+c.upper)) = pointBounds22355 := by
 decide +kernel
def cuts22356 : List PrefixCut := [⟨60,272149803,272149963⟩,
⟨128,577771921,577772253⟩]
theorem checked22356 : checkPrefixCuts (2^48) 2934177793 9 Manual.Count131072.C022356.packed 128 cuts22356 = true := by
 decide +kernel
def pointBounds22356 : List (Nat × Nat × Nat) := [(2934239232,101460612627029,101460993829973)]
theorem point_links_checked22356 : (cuts22356.take 1).map (fun c => (2934177793-1+2*2^9*c.k,101460340477226+c.lower,101460721680010+c.upper)) = pointBounds22356 := by
 decide +kernel
def cuts22357 : List PrefixCut := [⟨22,96116927,96116984⟩,
⟨112,502159843,502160143⟩,
⟨128,576019344,576019687⟩]
theorem checked22357 : checkPrefixCuts (2^48) 2934308865 9 Manual.Count131072.C022357.packed 128 cuts22357 = true := by
 decide +kernel
def pointBounds22357 : List (Nat × Nat × Nat) := [(2934331392,101461014366074,101461395569247),(2934423552,101461420408990,101461801612406)]
theorem point_links_checked22357 : (cuts22357.take 2).map (fun c => (2934308865-1+2*2^9*c.k,101460918249147+c.lower,101461299452263+c.upper)) = pointBounds22357 := by
 decide +kernel
def cuts22358 : List PrefixCut := [⟨74,334952338,334952533⟩,
⟨128,573212127,573212463⟩]
theorem checked22358 : checkPrefixCuts (2^48) 2934439937 9 Manual.Count131072.C022358.packed 128 cuts22358 = true := by
 decide +kernel
def pointBounds22358 : List (Nat × Nat × Nat) := [(2934515712,101461829220829,101462210424483)]
theorem point_links_checked22358 : (cuts22358.take 1).map (fun c => (2934439937-1+2*2^9*c.k,101461494268491+c.lower,101461875471950+c.upper)) = pointBounds22358 := by
 decide +kernel
def cuts22359 : List PrefixCut := [⟨36,167565733,167565826⟩,
⟨126,575296881,575297203⟩,
⟨128,584216756,584217082⟩]
theorem checked22359 : checkPrefixCuts (2^48) 2934571009 9 Manual.Count131072.C022359.packed 128 cuts22359 = true := by
 decide +kernel
def pointBounds22359 : List (Nat × Nat × Nat) := [(2934607872,101462235046351,101462616250239),(2934700032,101462642777499,101463023981616)]
theorem point_links_checked22359 : (cuts22359.take 2).map (fun c => (2934571009-1+2*2^9*c.k,101462067480618+c.lower,101462448684413+c.upper)) = pointBounds22359 := by
 decide +kernel
def cuts22360 : List PrefixCut := [⟨88,401388109,401388339⟩,
⟨128,581984748,581985082⟩]
theorem checked22360 : checkPrefixCuts (2^48) 2934702081 9 Manual.Count131072.C022360.packed 128 cuts22360 = true := by
 decide +kernel
def pointBounds22360 : List (Nat × Nat × Nat) := [(2934792192,101463053085483,101463434289834)]
theorem point_links_checked22360 : (cuts22360.take 1).map (fun c => (2934702081-1+2*2^9*c.k,101462651697374+c.lower,101463032901495+c.upper)) = pointBounds22360 := by
 decide +kernel
def cuts22361 : List PrefixCut := [⟨50,226725234,226725360⟩,
⟨128,578985525,578985856⟩]
theorem checked22361 : checkPrefixCuts (2^48) 2934833153 9 Manual.Count131072.C022361.packed 128 cuts22361 = true := by
 decide +kernel
def pointBounds22361 : List (Nat × Nat × Nat) := [(2934884352,101463460407356,101463841611937)]
theorem point_links_checked22361 : (cuts22361.take 1).map (fun c => (2934833153-1+2*2^9*c.k,101463233682122+c.lower,101463614886577+c.upper)) = pointBounds22361 := by
 decide +kernel
def cuts22362 : List PrefixCut := [⟨12,52651201,52651230⟩,
⟨102,455056474,455056732⟩,
⟨128,573301390,573301714⟩]
theorem checked22362 : checkPrefixCuts (2^48) 2934964225 9 Manual.Count131072.C022362.packed 128 cuts22362 = true := by
 decide +kernel
def pointBounds22362 : List (Nat × Nat × Nat) := [(2934976512,101463865318848,101464246523663),(2935068672,101464267724121,101464648929165)]
theorem point_links_checked22362 : (cuts22362.take 2).map (fun c => (2934964225-1+2*2^9*c.k,101463812667647+c.lower,101464193872433+c.upper)) = pointBounds22362 := by
 decide +kernel
def cuts22363 : List PrefixCut := [⟨64,287408342,287408507⟩,
⟨128,573659472,573659795⟩]
theorem checked22363 : checkPrefixCuts (2^48) 2935095297 9 Manual.Count131072.C022363.packed 128 cuts22363 = true := by
 decide +kernel
def pointBounds22363 : List (Nat × Nat × Nat) := [(2935160832,101464673377379,101465054582654)]
theorem point_links_checked22363 : (cuts22363.take 1).map (fun c => (2935095297-1+2*2^9*c.k,101464385969037+c.lower,101464767174147+c.upper)) = pointBounds22363 := by
 decide +kernel
def cuts22364 : List PrefixCut := [⟨26,117087831,117087900⟩,
⟨116,522044298,522044600⟩,
⟨128,577085955,577086290⟩]
theorem checked22364 : checkPrefixCuts (2^48) 2935226369 9 Manual.Count131072.C022364.packed 128 cuts22364 = true := by
 decide +kernel
def pointBounds22364 : List (Nat × Nat × Nat) := [(2935252992,101465076716340,101465457921842),(2935345152,101465481672807,101465862878542)]
theorem point_links_checked22364 : (cuts22364.take 2).map (fun c => (2935226369-1+2*2^9*c.k,101464959628509+c.lower,101465340833942+c.upper)) = pointBounds22364 := by
 decide +kernel
def cuts22365 : List PrefixCut := [⟨78,350861087,350861286⟩,
⟨128,575238396,575238724⟩]
theorem checked22365 : checkPrefixCuts (2^48) 2935357441 9 Manual.Count131072.C022365.packed 128 cuts22365 = true := by
 decide +kernel
def pointBounds22365 : List (Nat × Nat × Nat) := [(2935437312,101465887575551,101466268781518)]
theorem point_links_checked22365 : (cuts22365.take 1).map (fun c => (2935357441-1+2*2^9*c.k,101465536714464+c.lower,101465917920232+c.upper)) = pointBounds22365 := by
 decide +kernel
def cuts22366 : List PrefixCut := [⟨40,174129400,174129503⟩,
⟨128,564569445,564569780⟩]
theorem checked22366 : checkPrefixCuts (2^48) 2935488513 9 Manual.Count131072.C022366.packed 128 cuts22366 = true := by
 decide +kernel
def pointBounds22366 : List (Nat × Nat × Nat) := [(2935529472,101466286082260,101466667288459)]
theorem point_links_checked22366 : (cuts22366.take 1).map (fun c => (2935488513-1+2*2^9*c.k,101466111952860+c.lower,101466493158956+c.upper)) = pointBounds22366 := by
 decide +kernel
def cuts22367 : List PrefixCut := [⟨2,8917081,8917086⟩,
⟨92,417753800,417754037⟩,
⟨128,576049931,576050259⟩]
theorem checked22367 : checkPrefixCuts (2^48) 2935619585 9 Manual.Count131072.C022367.packed 128 cuts22367 = true := by
 decide +kernel
def pointBounds22367 : List (Nat × Nat × Nat) := [(2935621632,101466685439386,101467066645822),(2935713792,101467094276105,101467475482773)]
theorem point_links_checked22367 : (cuts22367.take 2).map (fun c => (2935619585-1+2*2^9*c.k,101466676522305+c.lower,101467057728736+c.upper)) = pointBounds22367 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000073
