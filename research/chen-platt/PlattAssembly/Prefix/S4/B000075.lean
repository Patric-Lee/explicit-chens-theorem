import PlattAssemblyKernel
import PlattCertificates.Count131072.C032400
import PlattCertificates.Count131072.C032401
import PlattCertificates.Count131072.C032402
import PlattCertificates.Count131072.C032403
import PlattCertificates.Count131072.C032404
import PlattCertificates.Count131072.C032405
import PlattCertificates.Count131072.C032406
import PlattCertificates.Count131072.C032407
import PlattCertificates.Count131072.C032408
import PlattCertificates.Count131072.C032409
import PlattCertificates.Count131072.C032410
import PlattCertificates.Count131072.C032411
import PlattCertificates.Count131072.C032412
import PlattCertificates.Count131072.C032413
import PlattCertificates.Count131072.C032414
import PlattCertificates.Count131072.C032415
import PlattCertificates.Count131072.C032416
import PlattCertificates.Count131072.C032417
import PlattCertificates.Count131072.C032418
import PlattCertificates.Count131072.C032419
import PlattCertificates.Count131072.C032420
import PlattCertificates.Count131072.C032421
import PlattCertificates.Count131072.C032422
import PlattCertificates.Count131072.C032423
import PlattCertificates.Count131072.C032424
import PlattCertificates.Count131072.C032425
import PlattCertificates.Count131072.C032426
import PlattCertificates.Count131072.C032427
import PlattCertificates.Count131072.C032428
import PlattCertificates.Count131072.C032429
import PlattCertificates.Count131072.C032430
import PlattCertificates.Count131072.C032431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts32400 : List PrefixCut := [⟨65,196337873,196337983⟩,
⟨128,390355118,390355339⟩]
theorem checked32400 : checkPrefixCuts (2^48) 4250664961 9 Manual.Count131072.C032400.packed 128 cuts32400 = true := by
 decide +kernel
def pointBounds32400 : List (Nat × Nat × Nat) := [(4250731520,106205956843199,106206340716215)]
theorem point_links_checked32400 : (cuts32400.take 1).map (fun c => (4250664961-1+2*2^9*c.k,106205760505326+c.lower,106206144378232+c.upper)) = pointBounds32400 := by
 decide +kernel
def cuts32401 : List PrefixCut := [⟨67,206992618,206992733⟩,
⟨128,395044441,395044666⟩]
theorem checked32401 : checkPrefixCuts (2^48) 4250796033 9 Manual.Count131072.C032401.packed 128 cuts32401 = true := by
 decide +kernel
def pointBounds32401 : List (Nat × Nat × Nat) := [(4250864640,106206357853062,106206741726304)]
theorem point_links_checked32401 : (cuts32401.take 1).map (fun c => (4250796033-1+2*2^9*c.k,106206150860444+c.lower,106206534733571+c.upper)) = pointBounds32401 := by
 decide +kernel
def cuts32402 : List PrefixCut := [⟨69,208641556,208641677⟩,
⟨128,391059402,391059624⟩]
theorem checked32402 : checkPrefixCuts (2^48) 4250927105 9 Manual.Count131072.C032402.packed 128 cuts32402 = true := by
 decide +kernel
def pointBounds32402 : List (Nat × Nat × Nat) := [(4250997760,106206754546441,106207138419914)]
theorem point_links_checked32402 : (cuts32402.take 1).map (fun c => (4250927105-1+2*2^9*c.k,106206545904885+c.lower,106206929778237+c.upper)) = pointBounds32402 := by
 decide +kernel
def cuts32403 : List PrefixCut := [⟨71,218964201,218964324⟩,
⟨128,392570275,392570500⟩]
theorem checked32403 : checkPrefixCuts (2^48) 4251058177 9 Manual.Count131072.C032403.packed 128 cuts32403 = true := by
 decide +kernel
def pointBounds32403 : List (Nat × Nat × Nat) := [(4251130880,106207155928488,106207539802185)]
theorem point_links_checked32403 : (cuts32403.take 1).map (fun c => (4251058177-1+2*2^9*c.k,106206936964287+c.lower,106207320837861+c.upper)) = pointBounds32403 := by
 decide +kernel
def cuts32404 : List PrefixCut := [⟨73,221672012,221672138⟩,
⟨128,388386925,388387146⟩]
theorem checked32404 : checkPrefixCuts (2^48) 4251189249 9 Manual.Count131072.C032404.packed 128 cuts32404 = true := by
 decide +kernel
def pointBounds32404 : List (Nat × Nat × Nat) := [(4251264000,106207551206574,106207935080499)]
theorem point_links_checked32404 : (cuts32404.take 1).map (fun c => (4251189249-1+2*2^9*c.k,106207329534562+c.lower,106207713408361+c.upper)) = pointBounds32404 := by
 decide +kernel
def cuts32405 : List PrefixCut := [⟨75,229742531,229742657⟩,
⟨128,391552913,391553134⟩]
theorem checked32405 : checkPrefixCuts (2^48) 4251320321 9 Manual.Count131072.C032405.packed 128 cuts32405 = true := by
 decide +kernel
def pointBounds32405 : List (Nat × Nat × Nat) := [(4251397120,106207947664018,106208331538164)]
theorem point_links_checked32405 : (cuts32405.take 1).map (fun c => (4251320321-1+2*2^9*c.k,106207717921487+c.lower,106208101795507+c.upper)) = pointBounds32405 := by
 decide +kernel
def cuts32406 : List PrefixCut := [⟨77,236951845,236951975⟩,
⟨128,388694031,388694246⟩]
theorem checked32406 : checkPrefixCuts (2^48) 4251451393 9 Manual.Count131072.C032406.packed 128 cuts32406 = true := by
 decide +kernel
def pointBounds32406 : List (Nat × Nat × Nat) := [(4251530240,106208346426245,106208730300616)]
theorem point_links_checked32406 : (cuts32406.take 1).map (fun c => (4251451393-1+2*2^9*c.k,106208109474400+c.lower,106208493348641+c.upper)) = pointBounds32406 := by
 decide +kernel
def cuts32407 : List PrefixCut := [⟨79,242108437,242108576⟩,
⟨128,390403359,390403581⟩]
theorem checked32407 : checkPrefixCuts (2^48) 4251582465 9 Manual.Count131072.C032407.packed 128 cuts32407 = true := by
 decide +kernel
def pointBounds32407 : List (Nat × Nat × Nat) := [(4251663360,106208740276868,106209124151463)]
theorem point_links_checked32407 : (cuts32407.take 1).map (fun c => (4251582465-1+2*2^9*c.k,106208498168431+c.lower,106208882042887+c.upper)) = pointBounds32407 := by
 decide +kernel
def cuts32408 : List PrefixCut := [⟨81,244417963,244418106⟩,
⟨128,387875600,387875823⟩]
theorem checked32408 : checkPrefixCuts (2^48) 4251713537 9 Manual.Count131072.C032408.packed 128 cuts32408 = true := by
 decide +kernel
def pointBounds32408 : List (Nat × Nat × Nat) := [(4251796480,106209132989753,106209516864574)]
theorem point_links_checked32408 : (cuts32408.take 1).map (fun c => (4251713537-1+2*2^9*c.k,106208888571790+c.lower,106209272446468+c.upper)) = pointBounds32408 := by
 decide +kernel
def cuts32409 : List PrefixCut := [⟨83,250434568,250434716⟩,
⟨128,388194633,388194861⟩]
theorem checked32409 : checkPrefixCuts (2^48) 4251844609 9 Manual.Count131072.C032409.packed 128 cuts32409 = true := by
 decide +kernel
def pointBounds32409 : List (Nat × Nat × Nat) := [(4251929600,106209526881958,106209910757007)]
theorem point_links_checked32409 : (cuts32409.take 1).map (fun c => (4251844609-1+2*2^9*c.k,106209276447390+c.lower,106209660322291+c.upper)) = pointBounds32409 := by
 decide +kernel
def cuts32410 : List PrefixCut := [⟨85,264394586,264394730⟩,
⟨128,395861663,395861881⟩]
theorem checked32410 : checkPrefixCuts (2^48) 4251975681 9 Manual.Count131072.C032410.packed 128 cuts32410 = true := by
 decide +kernel
def pointBounds32410 : List (Nat × Nat × Nat) := [(4252062720,106209929036609,106210312911882)]
theorem point_links_checked32410 : (cuts32410.take 1).map (fun c => (4251975681-1+2*2^9*c.k,106209664642023+c.lower,106210048517152+c.upper)) = pointBounds32410 := by
 decide +kernel
def cuts32411 : List PrefixCut := [⟨87,263922986,263923138⟩,
⟨128,391679061,391679289⟩]
theorem checked32411 : checkPrefixCuts (2^48) 4252106753 9 Manual.Count131072.C032411.packed 128 cuts32411 = true := by
 decide +kernel
def pointBounds32411 : List (Nat × Nat × Nat) := [(4252195840,106210324426672,106210708302171)]
theorem point_links_checked32411 : (cuts32411.take 1).map (fun c => (4252106753-1+2*2^9*c.k,106210060503686+c.lower,106210444379033+c.upper)) = pointBounds32411 := by
 decide +kernel
def cuts32412 : List PrefixCut := [⟨89,270666567,270666717⟩,
⟨128,389548844,389549063⟩]
theorem checked32412 : checkPrefixCuts (2^48) 4252237825 9 Manual.Count131072.C032412.packed 128 cuts32412 = true := by
 decide +kernel
def pointBounds32412 : List (Nat × Nat × Nat) := [(4252328960,106210722849314,106211106725039)]
theorem point_links_checked32412 : (cuts32412.take 1).map (fun c => (4252237825-1+2*2^9*c.k,106210452182747+c.lower,106210836058322+c.upper)) = pointBounds32412 := by
 decide +kernel
def cuts32413 : List PrefixCut := [⟨91,283102195,283102347⟩,
⟨128,391787397,391787613⟩]
theorem checked32413 : checkPrefixCuts (2^48) 4252368897 9 Manual.Count131072.C032413.packed 128 cuts32413 = true := by
 decide +kernel
def pointBounds32413 : List (Nat × Nat × Nat) := [(4252462080,106211124833786,106211508709732)]
theorem point_links_checked32413 : (cuts32413.take 1).map (fun c => (4252368897-1+2*2^9*c.k,106210841731591+c.lower,106211225607385+c.upper)) = pointBounds32413 := by
 decide +kernel
def cuts32414 : List PrefixCut := [⟨93,282696282,282696441⟩,
⟨128,389657212,389657434⟩]
theorem checked32414 : checkPrefixCuts (2^48) 4252499969 9 Manual.Count131072.C032414.packed 128 cuts32414 = true := by
 decide +kernel
def pointBounds32414 : List (Nat × Nat × Nat) := [(4252595200,106211516215270,106211900091439)]
theorem point_links_checked32414 : (cuts32414.take 1).map (fun c => (4252499969-1+2*2^9*c.k,106211233518988+c.lower,106211617394998+c.upper)) = pointBounds32414 := by
 decide +kernel
def cuts32415 : List PrefixCut := [⟨95,290232859,290233028⟩,
⟨128,392027901,392028126⟩]
theorem checked32415 : checkPrefixCuts (2^48) 4252631041 9 Manual.Count131072.C032415.packed 128 cuts32415 = true := by
 decide +kernel
def pointBounds32415 : List (Nat × Nat × Nat) := [(4252728320,106211913409059,106212297285460)]
theorem point_links_checked32415 : (cuts32415.take 1).map (fun c => (4252631041-1+2*2^9*c.k,106211623176200+c.lower,106212007052432+c.upper)) = pointBounds32415 := by
 decide +kernel
def cuts32416 : List PrefixCut := [⟨97,300217879,300218050⟩,
⟨128,394332349,394332570⟩]
theorem checked32416 : checkPrefixCuts (2^48) 4252762113 9 Manual.Count131072.C032416.packed 128 cuts32416 = true := by
 decide +kernel
def pointBounds32416 : List (Nat × Nat × Nat) := [(4252861440,106212315421980,106212699298608)]
theorem point_links_checked32416 : (cuts32416.take 1).map (fun c => (4252762113-1+2*2^9*c.k,106212015204101+c.lower,106212399080558+c.upper)) = pointBounds32416 := by
 decide +kernel
def cuts32417 : List PrefixCut := [⟨99,304709044,304709215⟩,
⟨128,391739062,391739281⟩]
theorem checked32417 : checkPrefixCuts (2^48) 4252893185 9 Manual.Count131072.C032417.packed 128 cuts32417 = true := by
 decide +kernel
def pointBounds32417 : List (Nat × Nat × Nat) := [(4252994560,106212714245494,106213098122343)]
theorem point_links_checked32417 : (cuts32417.take 1).map (fun c => (4252893185-1+2*2^9*c.k,106212409536450+c.lower,106212793413128+c.upper)) = pointBounds32417 := by
 decide +kernel
def cuts32418 : List PrefixCut := [⟨101,307942443,307942617⟩,
⟨128,390668033,390668255⟩]
theorem checked32418 : checkPrefixCuts (2^48) 4253024257 9 Manual.Count131072.C032418.packed 128 cuts32418 = true := by
 decide +kernel
def pointBounds32418 : List (Nat × Nat × Nat) := [(4253127680,106213109217955,106213493095026)]
theorem point_links_checked32418 : (cuts32418.take 1).map (fun c => (4253024257-1+2*2^9*c.k,106212801275512+c.lower,106213185152409+c.upper)) = pointBounds32418 := by
 decide +kernel
def cuts32419 : List PrefixCut := [⟨103,318720141,318720320⟩,
⟨128,394692960,394693185⟩]
theorem checked32419 : checkPrefixCuts (2^48) 4253155329 9 Manual.Count131072.C032419.packed 128 cuts32419 = true := by
 decide +kernel
def pointBounds32419 : List (Nat × Nat × Nat) := [(4253260800,106213510663686,106213894540984)]
theorem point_links_checked32419 : (cuts32419.take 1).map (fun c => (4253155329-1+2*2^9*c.k,106213191943545+c.lower,106213575820664+c.upper)) = pointBounds32419 := by
 decide +kernel
def cuts32420 : List PrefixCut := [⟨105,316129352,316129531⟩,
⟨128,386408641,386408860⟩]
theorem checked32420 : checkPrefixCuts (2^48) 4253286401 9 Manual.Count131072.C032420.packed 128 cuts32420 = true := by
 decide +kernel
def pointBounds32420 : List (Nat × Nat × Nat) := [(4253393920,106213902765857,106214286643380)]
theorem point_links_checked32420 : (cuts32420.take 1).map (fun c => (4253286401-1+2*2^9*c.k,106213586636505+c.lower,106213970513849+c.upper)) = pointBounds32420 := by
 decide +kernel
def cuts32421 : List PrefixCut := [⟨107,323729661,323729848⟩,
⟨128,385536456,385536679⟩]
theorem checked32421 : checkPrefixCuts (2^48) 4253417473 9 Manual.Count131072.C032421.packed 128 cuts32421 = true := by
 decide +kernel
def pointBounds32421 : List (Nat × Nat × Nat) := [(4253527040,106214296774807,106214680652557)]
theorem point_links_checked32421 : (cuts32421.take 1).map (fun c => (4253417473-1+2*2^9*c.k,106213973045146+c.lower,106214356922709+c.upper)) = pointBounds32421 := by
 decide +kernel
def cuts32422 : List PrefixCut := [⟨109,337682213,337682403⟩,
⟨128,396707859,396708083⟩]
theorem checked32422 : checkPrefixCuts (2^48) 4253548545 9 Manual.Count131072.C032422.packed 128 cuts32422 = true := by
 decide +kernel
def pointBounds32422 : List (Nat × Nat × Nat) := [(4253660160,106214696263815,106215080141791)]
theorem point_links_checked32422 : (cuts32422.take 1).map (fun c => (4253548545-1+2*2^9*c.k,106214358581602+c.lower,106214742459388+c.upper)) = pointBounds32422 := by
 decide +kernel
def cuts32423 : List PrefixCut := [⟨111,342899221,342899411⟩,
⟨128,394578140,394578361⟩]
theorem checked32423 : checkPrefixCuts (2^48) 4253679617 9 Manual.Count131072.C032423.packed 128 cuts32423 = true := by
 decide +kernel
def pointBounds32423 : List (Nat × Nat × Nat) := [(4253793280,106215098188682,106215482066882)]
theorem point_links_checked32423 : (cuts32423.take 1).map (fun c => (4253679617-1+2*2^9*c.k,106214755289461+c.lower,106215139167471+c.upper)) = pointBounds32423 := by
 decide +kernel
def cuts32424 : List PrefixCut := [⟨113,344608970,344609170⟩,
⟨128,390066482,390066709⟩]
theorem checked32424 : checkPrefixCuts (2^48) 4253810689 9 Manual.Count131072.C032424.packed 128 cuts32424 = true := by
 decide +kernel
def pointBounds32424 : List (Nat × Nat × Nat) := [(4253926400,106215494476571,106215878355002)]
theorem point_links_checked32424 : (cuts32424.take 1).map (fun c => (4253810689-1+2*2^9*c.k,106215149867601+c.lower,106215533745832+c.upper)) = pointBounds32424 := by
 decide +kernel
def cuts32425 : List PrefixCut := [⟨115,351678157,351678357⟩,
⟨128,390848476,390848701⟩]
theorem checked32425 : checkPrefixCuts (2^48) 4253941761 9 Manual.Count131072.C032425.packed 128 cuts32425 = true := by
 decide +kernel
def pointBounds32425 : List (Nat × Nat × Nat) := [(4254059520,106215891612240,106216275490898)]
theorem point_links_checked32425 : (cuts32425.take 1).map (fun c => (4253941761-1+2*2^9*c.k,106215539934083+c.lower,106215923812541+c.upper)) = pointBounds32425 := by
 decide +kernel
def cuts32426 : List PrefixCut := [⟨117,356828139,356828345⟩,
⟨128,389314675,389314901⟩]
theorem checked32426 : checkPrefixCuts (2^48) 4254072833 9 Manual.Count131072.C032426.packed 128 cuts32426 = true := by
 decide +kernel
def pointBounds32426 : List (Nat × Nat × Nat) := [(4254192640,106216287610698,106216671489587)]
theorem point_links_checked32426 : (cuts32426.take 1).map (fun c => (4254072833-1+2*2^9*c.k,106215930782559+c.lower,106216314661242+c.upper)) = pointBounds32426 := by
 decide +kernel
def cuts32427 : List PrefixCut := [⟨119,362308527,362308731⟩,
⟨128,389964234,389964453⟩]
theorem checked32427 : checkPrefixCuts (2^48) 4254203905 9 Manual.Count131072.C032427.packed 128 cuts32427 = true := by
 decide +kernel
def pointBounds32427 : List (Nat × Nat × Nat) := [(4254325760,106216682405761,106217066284874)]
theorem point_links_checked32427 : (cuts32427.take 1).map (fun c => (4254203905-1+2*2^9*c.k,106216320097234+c.lower,106216703976143+c.upper)) = pointBounds32427 := by
 decide +kernel
def cuts32428 : List PrefixCut := [⟨121,368582578,368582791⟩,
⟨128,388430555,388430779⟩]
theorem checked32428 : checkPrefixCuts (2^48) 4254334977 9 Manual.Count131072.C032428.packed 128 cuts32428 = true := by
 decide +kernel
def pointBounds32428 : List (Nat × Nat × Nat) := [(4254458880,106217078644046,106217462523387)]
theorem point_links_checked32428 : (cuts32428.take 1).map (fun c => (4254334977-1+2*2^9*c.k,106216710061468+c.lower,106217093940596+c.upper)) = pointBounds32428 := by
 decide +kernel
def cuts32429 : List PrefixCut := [⟨123,374790045,374790262⟩,
⟨128,391660301,391660528⟩]
theorem checked32429 : checkPrefixCuts (2^48) 4254466049 9 Manual.Count131072.C032429.packed 128 cuts32429 = true := by
 decide +kernel
def pointBounds32429 : List (Nat × Nat × Nat) := [(4254592000,106217473282068,106217857161637)]
theorem point_links_checked32429 : (cuts32429.take 1).map (fun c => (4254466049-1+2*2^9*c.k,106217098492023+c.lower,106217482371375+c.upper)) = pointBounds32429 := by
 decide +kernel
def cuts32430 : List PrefixCut := [⟨125,383577342,383577565⟩,
⟨128,391582195,391582424⟩]
theorem checked32430 : checkPrefixCuts (2^48) 4254597121 9 Manual.Count131072.C032430.packed 128 cuts32430 = true := by
 decide +kernel
def pointBounds32430 : List (Nat × Nat × Nat) := [(4254725120,106217873729666,106218257609468)]
theorem point_links_checked32430 : (cuts32430.take 1).map (fun c => (4254597121-1+2*2^9*c.k,106217490152324+c.lower,106217874031903+c.upper)) = pointBounds32430 := by
 decide +kernel
def cuts32431 : List PrefixCut := [⟨127,387402378,387402602⟩,
⟨128,390577758,390577984⟩]
theorem checked32431 : checkPrefixCuts (2^48) 4254728193 9 Manual.Count131072.C032431.packed 128 cuts32431 = true := by
 decide +kernel
def pointBounds32431 : List (Nat × Nat × Nat) := [(4254858240,106218269136897,106218653016929)]
theorem point_links_checked32431 : (cuts32431.take 1).map (fun c => (4254728193-1+2*2^9*c.k,106217881734519+c.lower,106218265614327+c.upper)) = pointBounds32431 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000075
