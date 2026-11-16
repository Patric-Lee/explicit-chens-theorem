import PlattAssemblyKernel
import PlattCertificates.Count131072.C028480
import PlattCertificates.Count131072.C028481
import PlattCertificates.Count131072.C028482
import PlattCertificates.Count131072.C028483
import PlattCertificates.Count131072.C028484
import PlattCertificates.Count131072.C028485
import PlattCertificates.Count131072.C028486
import PlattCertificates.Count131072.C028487
import PlattCertificates.Count131072.C028488
import PlattCertificates.Count131072.C028489
import PlattCertificates.Count131072.C028490
import PlattCertificates.Count131072.C028491
import PlattCertificates.Count131072.C028492
import PlattCertificates.Count131072.C028493
import PlattCertificates.Count131072.C028494
import PlattCertificates.Count131072.C028495
import PlattCertificates.Count131072.C028496
import PlattCertificates.Count131072.C028497
import PlattCertificates.Count131072.C028498
import PlattCertificates.Count131072.C028499
import PlattCertificates.Count131072.C028500
import PlattCertificates.Count131072.C028501
import PlattCertificates.Count131072.C028502
import PlattCertificates.Count131072.C028503
import PlattCertificates.Count131072.C028504
import PlattCertificates.Count131072.C028505
import PlattCertificates.Count131072.C028506
import PlattCertificates.Count131072.C028507
import PlattCertificates.Count131072.C028508
import PlattCertificates.Count131072.C028509
import PlattCertificates.Count131072.C028510
import PlattCertificates.Count131072.C028511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000265
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28480 : List PrefixCut := [⟨7,26965915,26965929⟩,
⟨122,429640131,429640365⟩,
⟨128,451407978,451408224⟩]
theorem checked28480 : checkPrefixCuts (2^48) 3736862721 9 Manual.Count131072.C028480.packed 128 cuts28480 = true := by
 decide +kernel
def pointBounds28480 : List (Nat × Nat × Nat) := [(3736869888,104565555495054,104565938444985),(3736987648,104565958169270,104566341119421)]
theorem point_links_checked28480 : (cuts28480.take 2).map (fun c => (3736862721-1+2*2^9*c.k,104565528529139+c.lower,104565911479056+c.upper)) = pointBounds28480 := by
 decide +kernel
def cuts28481 : List PrefixCut := [⟨109,372005850,372006058⟩,
⟨128,437231894,437232140⟩]
theorem checked28481 : checkPrefixCuts (2^48) 3736993793 9 Manual.Count131072.C028481.packed 128 cuts28481 = true := by
 decide +kernel
def pointBounds28481 : List (Nat × Nat × Nat) := [(3737105408,104566351942967,104566734893338)]
theorem point_links_checked28481 : (cuts28481.take 1).map (fun c => (3736993793-1+2*2^9*c.k,104565979937117+c.lower,104566362887280+c.upper)) = pointBounds28481 := by
 decide +kernel
def cuts28482 : List PrefixCut := [⟨96,343523502,343523692⟩,
⟨128,456271940,456272190⟩]
theorem checked28482 : checkPrefixCuts (2^48) 3737124865 9 Manual.Count131072.C028482.packed 128 cuts28482 = true := by
 decide +kernel
def pointBounds28482 : List (Nat × Nat × Nat) := [(3737223168,104566760692513,104567143643112)]
theorem point_links_checked28482 : (cuts28482.take 1).map (fun c => (3737124865-1+2*2^9*c.k,104566417169011+c.lower,104566800119420+c.upper)) = pointBounds28482 := by
 decide +kernel
def cuts28483 : List PrefixCut := [⟨83,286121949,286122112⟩,
⟨128,445937746,445937997⟩]
theorem checked28483 : checkPrefixCuts (2^48) 3737255937 9 Manual.Count131072.C028483.packed 128 cuts28483 = true := by
 decide +kernel
def pointBounds28483 : List (Nat × Nat × Nat) := [(3737340928,104567159562900,104567542513722)]
theorem point_links_checked28483 : (cuts28483.take 1).map (fun c => (3737255937-1+2*2^9*c.k,104566873440951+c.lower,104567256391610+c.upper)) = pointBounds28483 := by
 decide +kernel
def cuts28484 : List PrefixCut := [⟨70,240924915,240925048⟩,
⟨128,444491192,444491441⟩]
theorem checked28484 : checkPrefixCuts (2^48) 3737387009 9 Manual.Count131072.C028484.packed 128 cuts28484 = true := by
 decide +kernel
def pointBounds28484 : List (Nat × Nat × Nat) := [(3737458688,104567560303612,104567943254655)]
theorem point_links_checked28484 : (cuts28484.take 1).map (fun c => (3737387009-1+2*2^9*c.k,104567319378697+c.lower,104567702329607+c.upper)) = pointBounds28484 := by
 decide +kernel
def cuts28485 : List PrefixCut := [⟨57,197839534,197839644⟩,
⟨128,445304049,445304299⟩]
theorem checked28485 : checkPrefixCuts (2^48) 3737518081 9 Manual.Count131072.C028485.packed 128 cuts28485 = true := by
 decide +kernel
def pointBounds28485 : List (Nat × Nat × Nat) := [(3737576448,104567961709423,104568344660692)]
theorem point_links_checked28485 : (cuts28485.take 1).map (fun c => (3737518081-1+2*2^9*c.k,104567763869889+c.lower,104568146821048+c.upper)) = pointBounds28485 := by
 decide +kernel
def cuts28486 : List PrefixCut := [⟨44,154982949,154983037⟩,
⟨128,449806855,449807109⟩]
theorem checked28486 : checkPrefixCuts (2^48) 3737649153 9 Manual.Count131072.C028486.packed 128 cuts28486 = true := by
 decide +kernel
def pointBounds28486 : List (Nat × Nat × Nat) := [(3737694208,104568364156887,104568747108384)]
theorem point_links_checked28486 : (cuts28486.take 1).map (fun c => (3737649153-1+2*2^9*c.k,104568209173938+c.lower,104568592125347+c.upper)) = pointBounds28486 := by
 decide +kernel
def cuts28487 : List PrefixCut := [⟨31,109342920,109342982⟩,
⟨128,444670367,444670621⟩]
theorem checked28487 : checkPrefixCuts (2^48) 3737780225 9 Manual.Count131072.C028487.packed 128 cuts28487 = true := by
 decide +kernel
def pointBounds28487 : List (Nat × Nat × Nat) := [(3737811968,104568768323713,104569151275438)]
theorem point_links_checked28487 : (cuts28487.take 1).map (fun c => (3737780225-1+2*2^9*c.k,104568658980793+c.lower,104569041932456+c.upper)) = pointBounds28487 := by
 decide +kernel
def cuts28488 : List PrefixCut := [⟨18,63856551,63856586⟩,
⟨128,445859616,445859867⟩]
theorem checked28488 : checkPrefixCuts (2^48) 3737911297 9 Manual.Count131072.C028488.packed 128 cuts28488 = true := by
 decide +kernel
def pointBounds28488 : List (Nat × Nat × Nat) := [(3737929728,104569167507711,104569550459663)]
theorem point_links_checked28488 : (cuts28488.take 1).map (fun c => (3737911297-1+2*2^9*c.k,104569103651160+c.lower,104569486603077+c.upper)) = pointBounds28488 := by
 decide +kernel
def cuts28489 : List PrefixCut := [⟨5,17017806,17017816⟩,
⟨120,421598301,421598537⟩,
⟨128,449533684,449533936⟩]
theorem checked28489 : checkPrefixCuts (2^48) 3738042369 9 Manual.Count131072.C028489.packed 128 cuts28489 = true := by
 decide +kernel
def pointBounds28489 : List (Nat × Nat × Nat) := [(3738047488,104569566528582,104569949480760),(3738165248,104569971109077,104570354061481)]
theorem point_links_checked28489 : (cuts28489.take 2).map (fun c => (3738042369-1+2*2^9*c.k,104569549510776+c.lower,104569932462944+c.upper)) = pointBounds28489 := by
 decide +kernel
def cuts28490 : List PrefixCut := [⟨107,380246533,380246741⟩,
⟨128,453282698,453282944⟩]
theorem checked28490 : checkPrefixCuts (2^48) 3738173441 9 Manual.Count131072.C028490.packed 128 cuts28490 = true := by
 decide +kernel
def pointBounds28490 : List (Nat × Nat × Nat) := [(3738283008,104570379290993,104570762243621)]
theorem point_links_checked28490 : (cuts28490.take 1).map (fun c => (3738173441-1+2*2^9*c.k,104569999044460+c.lower,104570381996880+c.upper)) = pointBounds28490 := by
 decide +kernel
def cuts28491 : List PrefixCut := [⟨94,327302327,327302507⟩,
⟨128,446415080,446415327⟩]
theorem checked28491 : checkPrefixCuts (2^48) 3738304513 9 Manual.Count131072.C028491.packed 128 cuts28491 = true := by
 decide +kernel
def pointBounds28491 : List (Nat × Nat × Nat) := [(3738400768,104570779629485,104571162582331)]
theorem point_links_checked28491 : (cuts28491.take 1).map (fun c => (3738304513-1+2*2^9*c.k,104570452327158+c.lower,104570835279824+c.upper)) = pointBounds28491 := by
 decide +kernel
def cuts28492 : List PrefixCut := [⟨81,284977686,284977847⟩,
⟨128,447077064,447077316⟩]
theorem checked28492 : checkPrefixCuts (2^48) 3738435585 9 Manual.Count131072.C028492.packed 128 cuts28492 = true := by
 decide +kernel
def pointBounds28492 : List (Nat × Nat × Nat) := [(3738518528,104571183719924,104571566672998)]
theorem point_links_checked28492 : (cuts28492.take 1).map (fun c => (3738435585-1+2*2^9*c.k,104570898742238+c.lower,104571281695151+c.upper)) = pointBounds28492 := by
 decide +kernel
def cuts28493 : List PrefixCut := [⟨68,239267854,239267984⟩,
⟨128,447437793,447438040⟩]
theorem checked28493 : checkPrefixCuts (2^48) 3738566657 9 Manual.Count131072.C028493.packed 128 cuts28493 = true := by
 decide +kernel
def pointBounds28493 : List (Nat × Nat × Nat) := [(3738636288,104571585087156,104571968040451)]
theorem point_links_checked28493 : (cuts28493.take 1).map (fun c => (3738566657-1+2*2^9*c.k,104571345819302+c.lower,104571728772467+c.upper)) = pointBounds28493 := by
 decide +kernel
def cuts28494 : List PrefixCut := [⟨55,197325440,197325550⟩,
⟨128,449454892,449455142⟩]
theorem checked28494 : checkPrefixCuts (2^48) 3738697729 9 Manual.Count131072.C028494.packed 128 cuts28494 = true := by
 decide +kernel
def pointBounds28494 : List (Nat × Nat × Nat) := [(3738754048,104571990582535,104572373536057)]
theorem point_links_checked28494 : (cuts28494.take 1).map (fun c => (3738697729-1+2*2^9*c.k,104571793257095+c.lower,104572176210507+c.upper)) = pointBounds28494 := by
 decide +kernel
def cuts28495 : List PrefixCut := [⟨42,148083267,148083349⟩,
⟨128,445825521,445825769⟩]
theorem checked28495 : checkPrefixCuts (2^48) 3738828801 9 Manual.Count131072.C028495.packed 128 cuts28495 = true := by
 decide +kernel
def pointBounds28495 : List (Nat × Nat × Nat) := [(3738871808,104572390795254,104572773748998)]
theorem point_links_checked28495 : (cuts28495.take 1).map (fun c => (3738828801-1+2*2^9*c.k,104572242711987+c.lower,104572625665649+c.upper)) = pointBounds28495 := by
 decide +kernel
def cuts28496 : List PrefixCut := [⟨29,99371321,99371376⟩,
⟨128,445508672,445508916⟩]
theorem checked28496 : checkPrefixCuts (2^48) 3738959873 9 Manual.Count131072.C028496.packed 128 cuts28496 = true := by
 decide +kernel
def pointBounds28496 : List (Nat × Nat × Nat) := [(3738989568,104572787908829,104573170862794)]
theorem point_links_checked28496 : (cuts28496.take 1).map (fun c => (3738959873-1+2*2^9*c.k,104572688537508+c.lower,104573071491418+c.upper)) = pointBounds28496 := by
 decide +kernel
def cuts28497 : List PrefixCut := [⟨16,52469324,52469355⟩,
⟨128,450009702,450009957⟩]
theorem checked28497 : checkPrefixCuts (2^48) 3739090945 9 Manual.Count131072.C028497.packed 128 cuts28497 = true := by
 decide +kernel
def pointBounds28497 : List (Nat × Nat × Nat) := [(3739107328,104573186515504,104573569469689)]
theorem point_links_checked28497 : (cuts28497.take 1).map (fun c => (3739090945-1+2*2^9*c.k,104573134046180+c.lower,104573517000334+c.upper)) = pointBounds28497 := by
 decide +kernel
def cuts28498 : List PrefixCut := [⟨3,10915063,10915069⟩,
⟨118,415970296,415970528⟩,
⟨128,451650070,451650323⟩]
theorem checked28498 : checkPrefixCuts (2^48) 3739222017 9 Manual.Count131072.C028498.packed 128 cuts28498 = true := by
 decide +kernel
def pointBounds28498 : List (Nat × Nat × Nat) := [(3739225088,104573594970945,104573977925360),(3739342848,104574000026178,104574382980819)]
theorem point_links_checked28498 : (cuts28498.take 2).map (fun c => (3739222017-1+2*2^9*c.k,104573584055882+c.lower,104573967010291+c.upper)) = pointBounds28498 := by
 decide +kernel
def cuts28499 : List PrefixCut := [⟨105,364394669,364394878⟩,
⟨128,445687661,445687915⟩]
theorem checked28499 : checkPrefixCuts (2^48) 3739353089 9 Manual.Count131072.C028499.packed 128 cuts28499 = true := by
 decide +kernel
def pointBounds28499 : List (Nat × Nat × Nat) := [(3739460608,104574400100621,104574783055492)]
theorem point_links_checked28499 : (cuts28499.take 1).map (fun c => (3739353089-1+2*2^9*c.k,104574035705952+c.lower,104574418660614+c.upper)) = pointBounds28499 := by
 decide +kernel
def cuts28500 : List PrefixCut := [⟨92,320199006,320199183⟩,
⟨128,444543026,444543274⟩]
theorem checked28500 : checkPrefixCuts (2^48) 3739484161 9 Manual.Count131072.C028500.packed 128 cuts28500 = true := by
 decide +kernel
def pointBounds28500 : List (Nat × Nat × Nat) := [(3739578368,104574801592619,104575184547712)]
theorem point_links_checked28500 : (cuts28500.take 1).map (fun c => (3739484161-1+2*2^9*c.k,104574481393613+c.lower,104574864348529+c.upper)) = pointBounds28500 := by
 decide +kernel
def cuts28501 : List PrefixCut := [⟨79,277662161,277662318⟩,
⟨128,447237087,447237339⟩]
theorem checked28501 : checkPrefixCuts (2^48) 3739615233 9 Manual.Count131072.C028501.packed 128 cuts28501 = true := by
 decide +kernel
def pointBounds28501 : List (Nat × Nat × Nat) := [(3739696128,104575203598800,104575586554121)]
theorem point_links_checked28501 : (cuts28501.take 1).map (fun c => (3739615233-1+2*2^9*c.k,104574925936639+c.lower,104575308891803+c.upper)) = pointBounds28501 := by
 decide +kernel
def cuts28502 : List PrefixCut := [⟨66,229784349,229784480⟩,
⟨128,444436631,444436887⟩]
theorem checked28502 : checkPrefixCuts (2^48) 3739746305 9 Manual.Count131072.C028502.packed 128 cuts28502 = true := by
 decide +kernel
def pointBounds28502 : List (Nat × Nat × Nat) := [(3739813888,104575602958075,104575985913622)]
theorem point_links_checked28502 : (cuts28502.take 1).map (fun c => (3739746305-1+2*2^9*c.k,104575373173726+c.lower,104575756129142+c.upper)) = pointBounds28502 := by
 decide +kernel
def cuts28503 : List PrefixCut := [⟨53,186877016,186877122⟩,
⟨128,453226625,453226879⟩]
theorem checked28503 : checkPrefixCuts (2^48) 3739877377 9 Manual.Count131072.C028503.packed 128 cuts28503 = true := by
 decide +kernel
def pointBounds28503 : List (Nat × Nat × Nat) := [(3739931648,104576004487373,104576387443151)]
theorem point_links_checked28503 : (cuts28503.take 1).map (fun c => (3739877377-1+2*2^9*c.k,104575817610357+c.lower,104576200566029+c.upper)) = pointBounds28503 := by
 decide +kernel
def cuts28504 : List PrefixCut := [⟨40,139833240,139833320⟩,
⟨128,443276590,443276840⟩]
theorem checked28504 : checkPrefixCuts (2^48) 3740008449 9 Manual.Count131072.C028504.packed 128 cuts28504 = true := by
 decide +kernel
def pointBounds28504 : List (Nat × Nat × Nat) := [(3740049408,104576410670222,104576793626228)]
theorem point_links_checked28504 : (cuts28504.take 1).map (fun c => (3740008449-1+2*2^9*c.k,104576270836982+c.lower,104576653792908+c.upper)) = pointBounds28504 := by
 decide +kernel
def cuts28505 : List PrefixCut := [⟨27,96705989,96706043⟩,
⟨128,444164146,444164397⟩]
theorem checked28505 : checkPrefixCuts (2^48) 3740139521 9 Manual.Count131072.C028505.packed 128 cuts28505 = true := by
 decide +kernel
def pointBounds28505 : List (Nat × Nat × Nat) := [(3740167168,104576810819561,104577193775791)]
theorem point_links_checked28505 : (cuts28505.take 1).map (fun c => (3740139521-1+2*2^9*c.k,104576714113572+c.lower,104577097069748+c.upper)) = pointBounds28505 := by
 decide +kernel
def cuts28506 : List PrefixCut := [⟨14,48539525,48539552⟩,
⟨128,449491595,449491843⟩]
theorem checked28506 : checkPrefixCuts (2^48) 3740270593 9 Manual.Count131072.C028506.packed 128 cuts28506 = true := by
 decide +kernel
def pointBounds28506 : List (Nat × Nat × Nat) := [(3740284928,104577206817243,104577589773697)]
theorem point_links_checked28506 : (cuts28506.take 1).map (fun c => (3740270593-1+2*2^9*c.k,104577158277718+c.lower,104577541234145+c.upper)) = pointBounds28506 := by
 decide +kernel
def cuts28507 : List PrefixCut := [⟨1,3461618,3461620⟩,
⟨116,401240324,401240556⟩,
⟨128,444433868,444434125⟩]
theorem checked28507 : checkPrefixCuts (2^48) 3740401665 9 Manual.Count131072.C028507.packed 128 cuts28507 = true := by
 decide +kernel
def pointBounds28507 : List (Nat × Nat × Nat) := [(3740402688,104577611230931,104577994187608),(3740520448,104578009009637,104578391966544)]
theorem point_links_checked28507 : (cuts28507.take 2).map (fun c => (3740401665-1+2*2^9*c.k,104577607769313+c.lower,104577990725988+c.upper)) = pointBounds28507 := by
 decide +kernel
def cuts28508 : List PrefixCut := [⟨103,365258138,365258343⟩,
⟨128,450965122,450965375⟩]
theorem checked28508 : checkPrefixCuts (2^48) 3740532737 9 Manual.Count131072.C028508.packed 128 cuts28508 = true := by
 decide +kernel
def pointBounds28508 : List (Nat × Nat × Nat) := [(3740638208,104578417461319,104578800418456)]
theorem point_links_checked28508 : (cuts28508.take 1).map (fun c => (3740532737-1+2*2^9*c.k,104578052203181+c.lower,104578435160113+c.upper)) = pointBounds28508 := by
 decide +kernel
def cuts28509 : List PrefixCut := [⟨90,314003173,314003351⟩,
⟨128,448466102,448466356⟩]
theorem checked28509 : checkPrefixCuts (2^48) 3740663809 9 Manual.Count131072.C028509.packed 128 cuts28509 = true := by
 decide +kernel
def pointBounds28509 : List (Nat × Nat × Nat) := [(3740755968,104578817171476,104579200128839)]
theorem point_links_checked28509 : (cuts28509.take 1).map (fun c => (3740663809-1+2*2^9*c.k,104578503168303+c.lower,104578886125488+c.upper)) = pointBounds28509 := by
 decide +kernel
def cuts28510 : List PrefixCut := [⟨77,273436274,273436426⟩,
⟨128,452664060,452664315⟩]
theorem checked28510 : checkPrefixCuts (2^48) 3740794881 9 Manual.Count131072.C028510.packed 128 cuts28510 = true := by
 decide +kernel
def pointBounds28510 : List (Nat × Nat × Nat) := [(3740873728,104579225070679,104579608028270)]
theorem point_links_checked28510 : (cuts28510.take 1).map (fun c => (3740794881-1+2*2^9*c.k,104578951634405+c.lower,104579334591844+c.upper)) = pointBounds28510 := by
 decide +kernel
def cuts28511 : List PrefixCut := [⟨64,222187803,222187927⟩,
⟨128,444221203,444221449⟩]
theorem checked28511 : checkPrefixCuts (2^48) 3740925953 9 Manual.Count131072.C028511.packed 128 cuts28511 = true := by
 decide +kernel
def pointBounds28511 : List (Nat × Nat × Nat) := [(3740991488,104579626486268,104580009444086)]
theorem point_links_checked28511 : (cuts28511.take 1).map (fun c => (3740925953-1+2*2^9*c.k,104579404298465+c.lower,104579787256159+c.upper)) = pointBounds28511 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000265
