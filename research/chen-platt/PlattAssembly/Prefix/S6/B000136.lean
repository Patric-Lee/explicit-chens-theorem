import PlattAssemblyKernel
import PlattCertificates.Count131072.C054352
import PlattCertificates.Count131072.C054353
import PlattCertificates.Count131072.C054354
import PlattCertificates.Count131072.C054355
import PlattCertificates.Count131072.C054356
import PlattCertificates.Count131072.C054357
import PlattCertificates.Count131072.C054358
import PlattCertificates.Count131072.C054359
import PlattCertificates.Count131072.C054360
import PlattCertificates.Count131072.C054361
import PlattCertificates.Count131072.C054362
import PlattCertificates.Count131072.C054363
import PlattCertificates.Count131072.C054364
import PlattCertificates.Count131072.C054365
import PlattCertificates.Count131072.C054366
import PlattCertificates.Count131072.C054367
import PlattCertificates.Count131072.C054368
import PlattCertificates.Count131072.C054369
import PlattCertificates.Count131072.C054370
import PlattCertificates.Count131072.C054371
import PlattCertificates.Count131072.C054372
import PlattCertificates.Count131072.C054373
import PlattCertificates.Count131072.C054374
import PlattCertificates.Count131072.C054375
import PlattCertificates.Count131072.C054376
import PlattCertificates.Count131072.C054377
import PlattCertificates.Count131072.C054378
import PlattCertificates.Count131072.C054379
import PlattCertificates.Count131072.C054380
import PlattCertificates.Count131072.C054381
import PlattCertificates.Count131072.C054382
import PlattCertificates.Count131072.C054383
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000136
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54352 : List PrefixCut := [⟨64,228480413,228480542⟩]
theorem checked54352 : checkPrefixCuts (2^48) 7127957505 10 Manual.Count131072.C054352.packed 64 cuts54352 = true := by
 decide +kernel
def cuts54353 : List PrefixCut := [⟨30,107328278,107328338⟩,
⟨64,228120838,228120967⟩]
theorem checked54353 : checkPrefixCuts (2^48) 7128088577 10 Manual.Count131072.C054353.packed 64 cuts54353 = true := by
 decide +kernel
def pointBounds54353 : List (Nat × Nat × Nat) := [(7128150016,112693964667089,112694352378496)]
theorem point_links_checked54353 : (cuts54353.take 1).map (fun c => (7128088577-1+2*2^10*c.k,112693857338811+c.lower,112694245050158+c.upper)) = pointBounds54353 := by
 decide +kernel
def cuts54354 : List PrefixCut := [⟨64,229222286,229222414⟩]
theorem checked54354 : checkPrefixCuts (2^48) 7128219649 10 Manual.Count131072.C054354.packed 64 cuts54354 = true := by
 decide +kernel
def cuts54355 : List PrefixCut := [⟨11,39407643,39407666⟩,
⟨64,229770874,229771005⟩]
theorem checked54355 : checkPrefixCuts (2^48) 7128350721 10 Manual.Count131072.C054355.packed 64 cuts54355 = true := by
 decide +kernel
def pointBounds54355 : List (Nat × Nat × Nat) := [(7128373248,112694354089578,112694741801205)]
theorem point_links_checked54355 : (cuts54355.take 1).map (fun c => (7128350721-1+2*2^10*c.k,112694314681935+c.lower,112694702393539+c.upper)) = pointBounds54355 := by
 decide +kernel
def cuts54356 : List PrefixCut := [⟨56,197980977,197981089⟩,
⟨64,227002652,227002781⟩]
theorem checked54356 : checkPrefixCuts (2^48) 7128481793 10 Manual.Count131072.C054356.packed 64 cuts54356 = true := by
 decide +kernel
def pointBounds54356 : List (Nat × Nat × Nat) := [(7128596480,112694742433786,112695130145633)]
theorem point_links_checked54356 : (cuts54356.take 1).map (fun c => (7128481793-1+2*2^10*c.k,112694544452809+c.lower,112694932164544+c.upper)) = pointBounds54356 := by
 decide +kernel
def cuts54357 : List PrefixCut := [⟨64,228064576,228064701⟩]
theorem checked54357 : checkPrefixCuts (2^48) 7128612865 10 Manual.Count131072.C054357.packed 64 cuts54357 = true := by
 decide +kernel
def cuts54358 : List PrefixCut := [⟨37,132904115,132904190⟩,
⟨64,227468120,227468250⟩]
theorem checked54358 : checkPrefixCuts (2^48) 7128743937 10 Manual.Count131072.C054358.packed 64 cuts54358 = true := by
 decide +kernel
def pointBounds54358 : List (Nat × Nat × Nat) := [(7128819712,112695132424152,112695520136216)]
theorem point_links_checked54358 : (cuts54358.take 1).map (fun c => (7128743937-1+2*2^10*c.k,112694999520037+c.lower,112695387232026+c.upper)) = pointBounds54358 := by
 decide +kernel
def cuts54359 : List PrefixCut := [⟨64,230148802,230148930⟩]
theorem checked54359 : checkPrefixCuts (2^48) 7128875009 10 Manual.Count131072.C054359.packed 64 cuts54359 = true := by
 decide +kernel
def cuts54360 : List PrefixCut := [⟨18,62856855,62856890⟩,
⟨64,225525105,225525239⟩]
theorem checked54360 : checkPrefixCuts (2^48) 7129006081 10 Manual.Count131072.C054360.packed 64 cuts54360 = true := by
 decide +kernel
def pointBounds54360 : List (Nat × Nat × Nat) := [(7129042944,112695519993814,112695907706096)]
theorem point_links_checked54360 : (cuts54360.take 1).map (fun c => (7129006081-1+2*2^10*c.k,112695457136959+c.lower,112695844849206+c.upper)) = pointBounds54360 := by
 decide +kernel
def cuts54361 : List PrefixCut := [⟨63,224928755,224928886⟩,
⟨64,228324173,228324306⟩]
theorem checked54361 : checkPrefixCuts (2^48) 7129137153 10 Manual.Count131072.C054361.packed 64 cuts54361 = true := by
 decide +kernel
def pointBounds54361 : List (Nat × Nat × Nat) := [(7129266176,112695907590819,112696295303331)]
theorem point_links_checked54361 : (cuts54361.take 1).map (fun c => (7129137153-1+2*2^10*c.k,112695682662064+c.lower,112696070374445+c.upper)) = pointBounds54361 := by
 decide +kernel
def cuts54362 : List PrefixCut := [⟨64,228359457,228359587⟩]
theorem checked54362 : checkPrefixCuts (2^48) 7129268225 10 Manual.Count131072.C054362.packed 64 cuts54362 = true := by
 decide +kernel
def cuts54363 : List PrefixCut := [⟨44,156895985,156896075⟩,
⟨64,229618620,229618753⟩]
theorem checked54363 : checkPrefixCuts (2^48) 7129399297 10 Manual.Count131072.C054363.packed 64 cuts54363 = true := by
 decide +kernel
def pointBounds54363 : List (Nat × Nat × Nat) := [(7129489408,112696296241679,112696683954413)]
theorem point_links_checked54363 : (cuts54363.take 1).map (fun c => (7129399297-1+2*2^10*c.k,112696139345694+c.lower,112696527058338+c.upper)) = pointBounds54363 := by
 decide +kernel
def cuts54364 : List PrefixCut := [⟨64,229772343,229772471⟩]
theorem checked54364 : checkPrefixCuts (2^48) 7129530369 10 Manual.Count131072.C054364.packed 64 cuts54364 = true := by
 decide +kernel
def cuts54365 : List PrefixCut := [⟨25,88394103,88394154⟩,
⟨64,227438846,227438976⟩]
theorem checked54365 : checkPrefixCuts (2^48) 7129661441 10 Manual.Count131072.C054365.packed 64 cuts54365 = true := by
 decide +kernel
def pointBounds54365 : List (Nat × Nat × Nat) := [(7129712640,112696687130760,112697074843716)]
theorem point_links_checked54365 : (cuts54365.take 1).map (fun c => (7129661441-1+2*2^10*c.k,112696598736657+c.lower,112696986449562+c.upper)) = pointBounds54365 := by
 decide +kernel
def cuts54366 : List PrefixCut := [⟨64,231619381,231619510⟩]
theorem checked54366 : checkPrefixCuts (2^48) 7129792513 10 Manual.Count131072.C054366.packed 64 cuts54366 = true := by
 decide +kernel
def cuts54367 : List PrefixCut := [⟨6,21436519,21436531⟩,
⟨64,225732941,225733070⟩]
theorem checked54367 : checkPrefixCuts (2^48) 7129923585 10 Manual.Count131072.C054367.packed 64 cuts54367 = true := by
 decide +kernel
def pointBounds54367 : List (Nat × Nat × Nat) := [(7129935872,112697079231403,112697466944579)]
theorem point_links_checked54367 : (cuts54367.take 1).map (fun c => (7129923585-1+2*2^10*c.k,112697057794884+c.lower,112697445508048+c.upper)) = pointBounds54367 := by
 decide +kernel
def cuts54368 : List PrefixCut := [⟨51,181712415,181712519⟩,
⟨64,227386829,227386961⟩]
theorem checked54368 : checkPrefixCuts (2^48) 7130054657 10 Manual.Count131072.C054368.packed 64 cuts54368 = true := by
 decide +kernel
def pointBounds54368 : List (Nat × Nat × Nat) := [(7130159104,112697465240240,112697852953637)]
theorem point_links_checked54368 : (cuts54368.take 1).map (fun c => (7130054657-1+2*2^10*c.k,112697283527825+c.lower,112697671241118+c.upper)) = pointBounds54368 := by
 decide +kernel
def cuts54369 : List PrefixCut := [⟨64,227382646,227382775⟩]
theorem checked54369 : checkPrefixCuts (2^48) 7130185729 10 Manual.Count131072.C054369.packed 64 cuts54369 = true := by
 decide +kernel
def cuts54370 : List PrefixCut := [⟨32,114913497,114913562⟩,
⟨64,230497026,230497157⟩]
theorem checked54370 : checkPrefixCuts (2^48) 7130316801 10 Manual.Count131072.C054370.packed 64 cuts54370 = true := by
 decide +kernel
def pointBounds54370 : List (Nat × Nat × Nat) := [(7130382336,112697853210797,112698240924416)]
theorem point_links_checked54370 : (cuts54370.take 1).map (fun c => (7130316801-1+2*2^10*c.k,112697738297300+c.lower,112698126010854+c.upper)) = pointBounds54370 := by
 decide +kernel
def cuts54371 : List PrefixCut := [⟨64,225440049,225440177⟩]
theorem checked54371 : checkPrefixCuts (2^48) 7130447873 10 Manual.Count131072.C054371.packed 64 cuts54371 = true := by
 decide +kernel
def cuts54372 : List PrefixCut := [⟨13,45592779,45592804⟩,
⟨64,226067456,226067582⟩]
theorem checked54372 : checkPrefixCuts (2^48) 7130578945 10 Manual.Count131072.C054372.packed 64 cuts54372 = true := by
 decide +kernel
def pointBounds54372 : List (Nat × Nat × Nat) := [(7130605568,112698239827154,112698627540992)]
theorem point_links_checked54372 : (cuts54372.take 1).map (fun c => (7130578945-1+2*2^10*c.k,112698194234375+c.lower,112698581948188+c.upper)) = pointBounds54372 := by
 decide +kernel
def cuts54373 : List PrefixCut := [⟨58,207511085,207511204⟩,
⟨64,229458029,229458160⟩]
theorem checked54373 : checkPrefixCuts (2^48) 7130710017 10 Manual.Count131072.C054373.packed 64 cuts54373 = true := by
 decide +kernel
def pointBounds54373 : List (Nat × Nat × Nat) := [(7130828800,112698627812916,112699015526974)]
theorem point_links_checked54373 : (cuts54373.take 1).map (fun c => (7130710017-1+2*2^10*c.k,112698420301831+c.lower,112698808015770+c.upper)) = pointBounds54373 := by
 decide +kernel
def cuts54374 : List PrefixCut := [⟨64,227559101,227559232⟩]
theorem checked54374 : checkPrefixCuts (2^48) 7130841089 10 Manual.Count131072.C054374.packed 64 cuts54374 = true := by
 decide +kernel
def cuts54375 : List PrefixCut := [⟨39,138822829,138822911⟩,
⟨64,227949651,227949783⟩]
theorem checked54375 : checkPrefixCuts (2^48) 7130972161 10 Manual.Count131072.C054375.packed 64 cuts54375 = true := by
 decide +kernel
def pointBounds54375 : List (Nat × Nat × Nat) := [(7131052032,112699016141790,112699403856073)]
theorem point_links_checked54375 : (cuts54375.take 1).map (fun c => (7130972161-1+2*2^10*c.k,112698877318961+c.lower,112699265033162+c.upper)) = pointBounds54375 := by
 decide +kernel
def cuts54376 : List PrefixCut := [⟨64,230274248,230274376⟩]
theorem checked54376 : checkPrefixCuts (2^48) 7131103233 10 Manual.Count131072.C054376.packed 64 cuts54376 = true := by
 decide +kernel
def cuts54377 : List PrefixCut := [⟨20,72191723,72191763⟩,
⟨64,230743670,230743798⟩]
theorem checked54377 : checkPrefixCuts (2^48) 7131234305 10 Manual.Count131072.C054377.packed 64 cuts54377 = true := by
 decide +kernel
def pointBounds54377 : List (Nat × Nat × Nat) := [(7131275264,112699407734583,112699795449084)]
theorem point_links_checked54377 : (cuts54377.take 1).map (fun c => (7131234305-1+2*2^10*c.k,112699335542860+c.lower,112699723257321+c.upper)) = pointBounds54377 := by
 decide +kernel
def cuts54378 : List PrefixCut := [⟨64,226910877,226911007⟩]
theorem checked54378 : checkPrefixCuts (2^48) 7131365377 10 Manual.Count131072.C054378.packed 64 cuts54378 = true := by
 decide +kernel
def cuts54379 : List PrefixCut := [⟨1,3552233,3552235⟩,
⟨64,227853949,227854079⟩]
theorem checked54379 : checkPrefixCuts (2^48) 7131496449 10 Manual.Count131072.C054379.packed 64 cuts54379 = true := by
 decide +kernel
def pointBounds54379 : List (Nat × Nat × Nat) := [(7131498496,112699796749640,112700184464361)]
theorem point_links_checked54379 : (cuts54379.take 1).map (fun c => (7131496449-1+2*2^10*c.k,112699793197407+c.lower,112700180912126+c.upper)) = pointBounds54379 := by
 decide +kernel
def cuts54380 : List PrefixCut := [⟨46,165885165,165885258⟩,
⟨64,229862655,229862784⟩]
theorem checked54380 : checkPrefixCuts (2^48) 7131627521 10 Manual.Count131072.C054380.packed 64 cuts54380 = true := by
 decide +kernel
def pointBounds54380 : List (Nat × Nat × Nat) := [(7131721728,112700186936521,112700574651463)]
theorem point_links_checked54380 : (cuts54380.take 1).map (fun c => (7131627521-1+2*2^10*c.k,112700021051356+c.lower,112700408766205+c.upper)) = pointBounds54380 := by
 decide +kernel
def cuts54381 : List PrefixCut := [⟨64,229621591,229621724⟩]
theorem checked54381 : checkPrefixCuts (2^48) 7131758593 10 Manual.Count131072.C054381.packed 64 cuts54381 = true := by
 decide +kernel
def cuts54382 : List PrefixCut := [⟨27,98469992,98470048⟩,
⟨64,230327796,230327928⟩]
theorem checked54382 : checkPrefixCuts (2^48) 7131889665 10 Manual.Count131072.C054382.packed 64 cuts54382 = true := by
 decide +kernel
def pointBounds54382 : List (Nat × Nat × Nat) := [(7131944960,112700579005594,112700966720761)]
theorem point_links_checked54382 : (cuts54382.take 1).map (fun c => (7131889665-1+2*2^10*c.k,112700480535602+c.lower,112700868250713+c.upper)) = pointBounds54382 := by
 decide +kernel
def cuts54383 : List PrefixCut := [⟨64,226613763,226613895⟩]
theorem checked54383 : checkPrefixCuts (2^48) 7132020737 10 Manual.Count131072.C054383.packed 64 cuts54383 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000136
