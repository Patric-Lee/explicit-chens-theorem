import PlattAssemblyKernel
import PlattCertificates.Count131072.C027360
import PlattCertificates.Count131072.C027361
import PlattCertificates.Count131072.C027362
import PlattCertificates.Count131072.C027363
import PlattCertificates.Count131072.C027364
import PlattCertificates.Count131072.C027365
import PlattCertificates.Count131072.C027366
import PlattCertificates.Count131072.C027367
import PlattCertificates.Count131072.C027368
import PlattCertificates.Count131072.C027369
import PlattCertificates.Count131072.C027370
import PlattCertificates.Count131072.C027371
import PlattCertificates.Count131072.C027372
import PlattCertificates.Count131072.C027373
import PlattCertificates.Count131072.C027374
import PlattCertificates.Count131072.C027375
import PlattCertificates.Count131072.C027376
import PlattCertificates.Count131072.C027377
import PlattCertificates.Count131072.C027378
import PlattCertificates.Count131072.C027379
import PlattCertificates.Count131072.C027380
import PlattCertificates.Count131072.C027381
import PlattCertificates.Count131072.C027382
import PlattCertificates.Count131072.C027383
import PlattCertificates.Count131072.C027384
import PlattCertificates.Count131072.C027385
import PlattCertificates.Count131072.C027386
import PlattCertificates.Count131072.C027387
import PlattCertificates.Count131072.C027388
import PlattCertificates.Count131072.C027389
import PlattCertificates.Count131072.C027390
import PlattCertificates.Count131072.C027391
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000230
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27360 : List PrefixCut := [⟨14,52138493,52138522⟩,
⟨124,452539350,452539606⟩,
⟨128,466965150,466965414⟩]
theorem checked27360 : checkPrefixCuts (2^48) 3590062081 9 Manual.Count131072.C027360.packed 128 cuts27360 = true := by
 decide +kernel
def pointBounds27360 : List (Nat × Nat × Nat) := [(3590076416,104053233666607,104053616329900),(3590189056,104053634067464,104054016730984)]
theorem point_links_checked27360 : (cuts27360.take 2).map (fun c => (3590062081-1+2*2^9*c.k,104053181528114+c.lower,104053564191378+c.upper)) = pointBounds27360 := by
 decide +kernel
def cuts27361 : List PrefixCut := [⟨106,382826547,382826759⟩,
⟨128,464047325,464047581⟩]
theorem checked27361 : checkPrefixCuts (2^48) 3590193153 9 Manual.Count131072.C027361.packed 128 cuts27361 = true := by
 decide +kernel
def pointBounds27361 : List (Nat × Nat × Nat) := [(3590301696,104054031319811,104054413983551)]
theorem point_links_checked27361 : (cuts27361.take 1).map (fun c => (3590193153-1+2*2^9*c.k,104053648493264+c.lower,104054031156792+c.upper)) = pointBounds27361 := by
 decide +kernel
def cuts27362 : List PrefixCut := [⟨88,322134100,322134279⟩,
⟨128,465206379,465206634⟩]
theorem checked27362 : checkPrefixCuts (2^48) 3590324225 9 Manual.Count131072.C027362.packed 128 cuts27362 = true := by
 decide +kernel
def pointBounds27362 : List (Nat × Nat × Nat) := [(3590414336,104054434674689,104054817338652)]
theorem point_links_checked27362 : (cuts27362.take 1).map (fun c => (3590324225-1+2*2^9*c.k,104054112540589+c.lower,104054495204373+c.upper)) = pointBounds27362 := by
 decide +kernel
def cuts27363 : List PrefixCut := [⟨70,258153219,258153362⟩,
⟨128,468560308,468560570⟩]
theorem checked27363 : checkPrefixCuts (2^48) 3590455297 9 Manual.Count131072.C027363.packed 128 cuts27363 = true := by
 decide +kernel
def pointBounds27363 : List (Nat × Nat × Nat) := [(3590526976,104054835900187,104055218564369)]
theorem point_links_checked27363 : (cuts27363.take 1).map (fun c => (3590455297-1+2*2^9*c.k,104054577746968+c.lower,104054960411007+c.upper)) = pointBounds27363 := by
 decide +kernel
def cuts27364 : List PrefixCut := [⟨52,189551554,189551662⟩,
⟨128,465015595,465015857⟩]
theorem checked27364 : checkPrefixCuts (2^48) 3590586369 9 Manual.Count131072.C027364.packed 128 cuts27364 = true := by
 decide +kernel
def pointBounds27364 : List (Nat × Nat × Nat) := [(3590639616,104055235858830,104055618523239)]
theorem point_links_checked27364 : (cuts27364.take 1).map (fun c => (3590586369-1+2*2^9*c.k,104055046307276+c.lower,104055428971577+c.upper)) = pointBounds27364 := by
 decide +kernel
def cuts27365 : List PrefixCut := [⟨34,123384626,123384694⟩,
⟨128,465312156,465312416⟩]
theorem checked27365 : checkPrefixCuts (2^48) 3590717441 9 Manual.Count131072.C027365.packed 128 cuts27365 = true := by
 decide +kernel
def pointBounds27365 : List (Nat × Nat × Nat) := [(3590752256,104055634707497,104056017372128)]
theorem point_links_checked27365 : (cuts27365.take 1).map (fun c => (3590717441-1+2*2^9*c.k,104055511322871+c.lower,104055893987434+c.upper)) = pointBounds27365 := by
 decide +kernel
def cuts27366 : List PrefixCut := [⟨16,59808948,59808982⟩,
⟨126,462238289,462238549⟩,
⟨128,470155063,470155327⟩]
theorem checked27366 : checkPrefixCuts (2^48) 3590848513 9 Manual.Count131072.C027366.packed 128 cuts27366 = true := by
 decide +kernel
def pointBounds27366 : List (Nat × Nat × Nat) := [(3590864896,104056036443975,104056419108832),(3590977536,104056438873316,104056821538399)]
theorem point_links_checked27366 : (cuts27366.take 2).map (fun c => (3590848513-1+2*2^9*c.k,104055976635027+c.lower,104056359299850+c.upper)) = pointBounds27366 := by
 decide +kernel
def cuts27367 : List PrefixCut := [⟨108,390424029,390424247⟩,
⟨128,459242754,459243013⟩]
theorem checked27367 : checkPrefixCuts (2^48) 3590979585 9 Manual.Count131072.C027367.packed 128 cuts27367 = true := by
 decide +kernel
def pointBounds27367 : List (Nat × Nat × Nat) := [(3591090176,104056837214119,104057219879424)]
theorem point_links_checked27367 : (cuts27367.take 1).map (fun c => (3590979585-1+2*2^9*c.k,104056446790090+c.lower,104056829455177+c.upper)) = pointBounds27367 := by
 decide +kernel
def cuts27368 : List PrefixCut := [⟨90,325982399,325982581⟩,
⟨128,463928701,463928958⟩]
theorem checked27368 : checkPrefixCuts (2^48) 3591110657 9 Manual.Count131072.C027368.packed 128 cuts27368 = true := by
 decide +kernel
def pointBounds27368 : List (Nat × Nat × Nat) := [(3591202816,104057232015243,104057614680771)]
theorem point_links_checked27368 : (cuts27368.take 1).map (fun c => (3591110657-1+2*2^9*c.k,104056906032844+c.lower,104057288698190+c.upper)) = pointBounds27368 := by
 decide +kernel
def cuts27369 : List PrefixCut := [⟨72,258253322,258253471⟩,
⟨128,461403730,461403990⟩]
theorem checked27369 : checkPrefixCuts (2^48) 3591241729 9 Manual.Count131072.C027369.packed 128 cuts27369 = true := by
 decide +kernel
def pointBounds27369 : List (Nat × Nat × Nat) := [(3591315456,104057628214867,104058010880619)]
theorem point_links_checked27369 : (cuts27369.take 1).map (fun c => (3591241729-1+2*2^9*c.k,104057369961545+c.lower,104057752627148+c.upper)) = pointBounds27369 := by
 decide +kernel
def cuts27370 : List PrefixCut := [⟨54,194290850,194290961⟩,
⟨128,469145876,469146140⟩]
theorem checked27370 : checkPrefixCuts (2^48) 3591372801 9 Manual.Count131072.C027370.packed 128 cuts27370 = true := by
 decide +kernel
def pointBounds27370 : List (Nat × Nat × Nat) := [(3591428096,104058025656125,104058408322099)]
theorem point_links_checked27370 : (cuts27370.take 1).map (fun c => (3591372801-1+2*2^9*c.k,104057831365275+c.lower,104058214031138+c.upper)) = pointBounds27370 := by
 decide +kernel
def cuts27371 : List PrefixCut := [⟨36,128373388,128373462⟩,
⟨128,459802650,459802910⟩]
theorem checked27371 : checkPrefixCuts (2^48) 3591503873 9 Manual.Count131072.C027371.packed 128 cuts27371 = true := by
 decide +kernel
def pointBounds27371 : List (Nat × Nat × Nat) := [(3591540736,104058428884539,104058811550740)]
theorem point_links_checked27371 : (cuts27371.take 1).map (fun c => (3591503873-1+2*2^9*c.k,104058300511151+c.lower,104058683177278+c.upper)) = pointBounds27371 := by
 decide +kernel
def cuts27372 : List PrefixCut := [⟨18,64968207,64968242⟩,
⟨128,466917409,466917667⟩]
theorem checked27372 : checkPrefixCuts (2^48) 3591634945 9 Manual.Count131072.C027372.packed 128 cuts27372 = true := by
 decide +kernel
def pointBounds27372 : List (Nat × Nat × Nat) := [(3591653376,104058825282008,104059207948430),(3591766016,104059227231210,104059609897855)]
theorem point_links_checked27372 : (cuts27372.take 2).map (fun c => (3591634945-1+2*2^9*c.k,104058760313801+c.lower,104059142980188+c.upper)) = pointBounds27372 := by
 decide +kernel
def cuts27373 : List PrefixCut := [⟨110,399350487,399350708⟩,
⟨128,466351757,466352014⟩]
theorem checked27373 : checkPrefixCuts (2^48) 3591766017 9 Manual.Count131072.C027373.packed 128 cuts27373 = true := by
 decide +kernel
def pointBounds27373 : List (Nat × Nat × Nat) := [(3591878656,104059626581697,104060009248563)]
theorem point_links_checked27373 : (cuts27373.take 1).map (fun c => (3591766017-1+2*2^9*c.k,104059227231210+c.lower,104059609897855+c.upper)) = pointBounds27373 := by
 decide +kernel
def cuts27374 : List PrefixCut := [⟨92,331318003,331318187⟩,
⟨128,462494989,462495247⟩]
theorem checked27374 : checkPrefixCuts (2^48) 3591897089 9 Manual.Count131072.C027374.packed 128 cuts27374 = true := by
 decide +kernel
def pointBounds27374 : List (Nat × Nat × Nat) := [(3591991296,104060024900970,104060407568056)]
theorem point_links_checked27374 : (cuts27374.take 1).map (fun c => (3591897089-1+2*2^9*c.k,104059693582967+c.lower,104060076249869+c.upper)) = pointBounds27374 := by
 decide +kernel
def cuts27375 : List PrefixCut := [⟨74,269715713,269715863⟩,
⟨128,466552854,466553113⟩]
theorem checked27375 : checkPrefixCuts (2^48) 3592028161 9 Manual.Count131072.C027375.packed 128 cuts27375 = true := by
 decide +kernel
def pointBounds27375 : List (Nat × Nat × Nat) := [(3592103936,104060425793669,104060808460979)]
theorem point_links_checked27375 : (cuts27375.take 1).map (fun c => (3592028161-1+2*2^9*c.k,104060156077956+c.lower,104060538745116+c.upper)) = pointBounds27375 := by
 decide +kernel
def cuts27376 : List PrefixCut := [⟨56,206236950,206237063⟩,
⟨128,471942421,471942677⟩]
theorem checked27376 : checkPrefixCuts (2^48) 3592159233 9 Manual.Count131072.C027376.packed 128 cuts27376 = true := by
 decide +kernel
def pointBounds27376 : List (Nat × Nat × Nat) := [(3592216576,104060828867760,104061211535292)]
theorem point_links_checked27376 : (cuts27376.take 1).map (fun c => (3592159233-1+2*2^9*c.k,104060622630810+c.lower,104061005298229+c.upper)) = pointBounds27376 := by
 decide +kernel
def cuts27377 : List PrefixCut := [⟨38,136572505,136572582⟩,
⟨128,461817539,461817799⟩]
theorem checked27377 : checkPrefixCuts (2^48) 3592290305 9 Manual.Count131072.C027377.packed 128 cuts27377 = true := by
 decide +kernel
def pointBounds27377 : List (Nat × Nat × Nat) := [(3592329216,104061231145736,104061613813488)]
theorem point_links_checked27377 : (cuts27377.take 1).map (fun c => (3592290305-1+2*2^9*c.k,104061094573231+c.lower,104061477240906+c.upper)) = pointBounds27377 := by
 decide +kernel
def cuts27378 : List PrefixCut := [⟨20,73807768,73807810⟩,
⟨128,465091493,465091756⟩]
theorem checked27378 : checkPrefixCuts (2^48) 3592421377 9 Manual.Count131072.C027378.packed 128 cuts27378 = true := by
 decide +kernel
def pointBounds27378 : List (Nat × Nat × Nat) := [(3592441856,104061630198538,104062012866515)]
theorem point_links_checked27378 : (cuts27378.take 1).map (fun c => (3592421377-1+2*2^9*c.k,104061556390770+c.lower,104061939058705+c.upper)) = pointBounds27378 := by
 decide +kernel
def cuts27379 : List PrefixCut := [⟨2,7756604,7756608⟩,
⟨112,407254460,407254687⟩,
⟨128,467268170,467268430⟩]
theorem checked27379 : checkPrefixCuts (2^48) 3592552449 9 Manual.Count131072.C027379.packed 128 cuts27379 = true := by
 decide +kernel
def pointBounds27379 : List (Nat × Nat × Nat) := [(3592554496,104062029238867,104062411907069),(3592667136,104062428736723,104062811405148)]
theorem point_links_checked27379 : (cuts27379.take 2).map (fun c => (3592552449-1+2*2^9*c.k,104062021482263+c.lower,104062404150461+c.upper)) = pointBounds27379 := by
 decide +kernel
def cuts27380 : List PrefixCut := [⟨94,338453236,338453427⟩,
⟨128,466467697,466467959⟩]
theorem checked27380 : checkPrefixCuts (2^48) 3592683521 9 Manual.Count131072.C027380.packed 128 cuts27380 = true := by
 decide +kernel
def pointBounds27380 : List (Nat × Nat × Nat) := [(3592779776,104062827203669,104063209872318)]
theorem point_links_checked27380 : (cuts27380.take 1).map (fun c => (3592683521-1+2*2^9*c.k,104062488750433+c.lower,104062871418891+c.upper)) = pointBounds27380 := by
 decide +kernel
def cuts27381 : List PrefixCut := [⟨76,270126625,270126776⟩,
⟨128,460418274,460418534⟩]
theorem checked27381 : checkPrefixCuts (2^48) 3592814593 9 Manual.Count131072.C027381.packed 128 cuts27381 = true := by
 decide +kernel
def pointBounds27381 : List (Nat × Nat × Nat) := [(3592892416,104063225344755,104063608013626)]
theorem point_links_checked27381 : (cuts27381.take 1).map (fun c => (3592814593-1+2*2^9*c.k,104062955218130+c.lower,104063337886850+c.upper)) = pointBounds27381 := by
 decide +kernel
def cuts27382 : List PrefixCut := [⟨58,213634086,213634205⟩,
⟨128,464788644,464788907⟩]
theorem checked27382 : checkPrefixCuts (2^48) 3592945665 9 Manual.Count131072.C027382.packed 128 cuts27382 = true := by
 decide +kernel
def pointBounds27382 : List (Nat × Nat × Nat) := [(3593005056,104063629270490,104064011939589)]
theorem point_links_checked27382 : (cuts27382.take 1).map (fun c => (3592945665-1+2*2^9*c.k,104063415636404+c.lower,104063798305384+c.upper)) = pointBounds27382 := by
 decide +kernel
def cuts27383 : List PrefixCut := [⟨40,147901536,147901614⟩,
⟨128,467905063,467905324⟩]
theorem checked27383 : checkPrefixCuts (2^48) 3593076737 9 Manual.Count131072.C027383.packed 128 cuts27383 = true := by
 decide +kernel
def pointBounds27383 : List (Nat × Nat × Nat) := [(3593117696,104064028326584,104064410995905)]
theorem point_links_checked27383 : (cuts27383.take 1).map (fun c => (3593076737-1+2*2^9*c.k,104063880425048+c.lower,104064263094291+c.upper)) = pointBounds27383 := by
 decide +kernel
def cuts27384 : List PrefixCut := [⟨22,77865008,77865052⟩,
⟨128,467026344,467026606⟩]
theorem checked27384 : checkPrefixCuts (2^48) 3593207809 9 Manual.Count131072.C027384.packed 128 cuts27384 = true := by
 decide +kernel
def pointBounds27384 : List (Nat × Nat × Nat) := [(3593230336,104064426195119,104064808864667)]
theorem point_links_checked27384 : (cuts27384.take 1).map (fun c => (3593207809-1+2*2^9*c.k,104064348330111+c.lower,104064730999615+c.upper)) = pointBounds27384 := by
 decide +kernel
def cuts27385 : List PrefixCut := [⟨4,14334824,14334831⟩,
⟨114,420481584,420481820⟩,
⟨128,473275808,473276073⟩]
theorem checked27385 : checkPrefixCuts (2^48) 3593338881 9 Manual.Count131072.C027385.packed 128 cuts27385 = true := by
 decide +kernel
def pointBounds27385 : List (Nat × Nat × Nat) := [(3593342976,104064829691279,104065212361052),(3593455616,104065235838039,104065618508041)]
theorem point_links_checked27385 : (cuts27385.take 2).map (fun c => (3593338881-1+2*2^9*c.k,104064815356455+c.lower,104065198026221+c.upper)) = pointBounds27385 := by
 decide +kernel
def cuts27386 : List PrefixCut := [⟨96,355454669,355454864⟩,
⟨128,472475287,472475549⟩]
theorem checked27386 : checkPrefixCuts (2^48) 3593469953 9 Manual.Count131072.C027386.packed 128 cuts27386 = true := by
 decide +kernel
def pointBounds27386 : List (Nat × Nat × Nat) := [(3593568256,104065644086932,104066026757158)]
theorem point_links_checked27386 : (cuts27386.take 1).map (fun c => (3593469953-1+2*2^9*c.k,104065288632263+c.lower,104065671302294+c.upper)) = pointBounds27386 := by
 decide +kernel
def cuts27387 : List PrefixCut := [⟨78,280876407,280876571⟩,
⟨128,462354008,462354277⟩]
theorem checked27387 : checkPrefixCuts (2^48) 3593601025 9 Manual.Count131072.C027387.packed 128 cuts27387 = true := by
 decide +kernel
def pointBounds27387 : List (Nat × Nat × Nat) := [(3593680896,104066041983957,104066424654414)]
theorem point_links_checked27387 : (cuts27387.take 1).map (fun c => (3593601025-1+2*2^9*c.k,104065761107550+c.lower,104066143777843+c.upper)) = pointBounds27387 := by
 decide +kernel
def cuts27388 : List PrefixCut := [⟨60,217660082,217660204⟩,
⟨128,464686867,464687126⟩]
theorem checked27388 : checkPrefixCuts (2^48) 3593732097 9 Manual.Count131072.C027388.packed 128 cuts27388 = true := by
 decide +kernel
def pointBounds27388 : List (Nat × Nat × Nat) := [(3593793536,104066441121640,104066823792324)]
theorem point_links_checked27388 : (cuts27388.take 1).map (fun c => (3593732097-1+2*2^9*c.k,104066223461558+c.lower,104066606132120+c.upper)) = pointBounds27388 := by
 decide +kernel
def cuts27389 : List PrefixCut := [⟨42,155622863,155622951⟩,
⟨128,471875355,471875617⟩]
theorem checked27389 : checkPrefixCuts (2^48) 3593863169 9 Manual.Count131072.C027389.packed 128 cuts27389 = true := by
 decide +kernel
def pointBounds27389 : List (Nat × Nat × Nat) := [(3593906176,104066843771288,104067226442197)]
theorem point_links_checked27389 : (cuts27389.take 1).map (fun c => (3593863169-1+2*2^9*c.k,104066688148425+c.lower,104067070819246+c.upper)) = pointBounds27389 := by
 decide +kernel
def cuts27390 : List PrefixCut := [⟨24,87637682,87637731⟩,
⟨128,470448386,470448647⟩]
theorem checked27390 : checkPrefixCuts (2^48) 3593994241 9 Manual.Count131072.C027390.packed 128 cuts27390 = true := by
 decide +kernel
def pointBounds27390 : List (Nat × Nat × Nat) := [(3594018816,104067247661462,104067630332594)]
theorem point_links_checked27390 : (cuts27390.take 1).map (fun c => (3593994241-1+2*2^9*c.k,104067160023780+c.lower,104067542694863+c.upper)) = pointBounds27390 := by
 decide +kernel
def cuts27391 : List PrefixCut := [⟨6,21693310,21693323⟩,
⟨116,423365367,423365603⟩,
⟨128,466907143,466907403⟩]
theorem checked27391 : checkPrefixCuts (2^48) 3594125313 9 Manual.Count131072.C027391.packed 128 cuts27391 = true := by
 decide +kernel
def pointBounds27391 : List (Nat × Nat × Nat) := [(3594131456,104067652165476,104068034836833),(3594244096,104068053837533,104068436509113)]
theorem point_links_checked27391 : (cuts27391.take 2).map (fun c => (3594125313-1+2*2^9*c.k,104067630472166+c.lower,104068013143510+c.upper)) = pointBounds27391 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000230
