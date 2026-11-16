import PlattAssemblyKernel
import PlattCertificates.Count131072.C022464
import PlattCertificates.Count131072.C022465
import PlattCertificates.Count131072.C022466
import PlattCertificates.Count131072.C022467
import PlattCertificates.Count131072.C022468
import PlattCertificates.Count131072.C022469
import PlattCertificates.Count131072.C022470
import PlattCertificates.Count131072.C022471
import PlattCertificates.Count131072.C022472
import PlattCertificates.Count131072.C022473
import PlattCertificates.Count131072.C022474
import PlattCertificates.Count131072.C022475
import PlattCertificates.Count131072.C022476
import PlattCertificates.Count131072.C022477
import PlattCertificates.Count131072.C022478
import PlattCertificates.Count131072.C022479
import PlattCertificates.Count131072.C022480
import PlattCertificates.Count131072.C022481
import PlattCertificates.Count131072.C022482
import PlattCertificates.Count131072.C022483
import PlattCertificates.Count131072.C022484
import PlattCertificates.Count131072.C022485
import PlattCertificates.Count131072.C022486
import PlattCertificates.Count131072.C022487
import PlattCertificates.Count131072.C022488
import PlattCertificates.Count131072.C022489
import PlattCertificates.Count131072.C022490
import PlattCertificates.Count131072.C022491
import PlattCertificates.Count131072.C022492
import PlattCertificates.Count131072.C022493
import PlattCertificates.Count131072.C022494
import PlattCertificates.Count131072.C022495
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000077
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22464 : List PrefixCut := [⟨6,26253987,26254004⟩,
⟨96,432563448,432563697⟩,
⟨128,578052768,578053099⟩]
theorem checked22464 : checkPrefixCuts (2^48) 2948333569 9 Manual.Count131072.C022464.packed 128 cuts22464 = true := by
 decide +kernel
def pointBounds22464 : List (Nat × Nat × Nat) := [(2948339712,101522509117907,101522890356307),(2948431872,101522915427368,101523296666000)]
theorem point_links_checked22464 : (cuts22464.take 2).map (fun c => (2948333569-1+2*2^9*c.k,101522482863920+c.lower,101522864102303+c.upper)) = pointBounds22464 := by
 decide +kernel
def cuts22465 : List PrefixCut := [⟨58,262812220,262812365⟩,
⟨128,575926980,575927303⟩]
theorem checked22465 : checkPrefixCuts (2^48) 2948464641 9 Manual.Count131072.C022465.packed 128 cuts22465 = true := by
 decide +kernel
def pointBounds22465 : List (Nat × Nat × Nat) := [(2948524032,101523323728908,101523704967767)]
theorem point_links_checked22465 : (cuts22465.take 1).map (fun c => (2948464641-1+2*2^9*c.k,101523060916688+c.lower,101523442155402+c.upper)) = pointBounds22465 := by
 decide +kernel
def cuts22466 : List PrefixCut := [⟨20,88300812,88300863⟩,
⟨110,488462902,488463186⟩,
⟨128,570364765,570365096⟩]
theorem checked22466 : checkPrefixCuts (2^48) 2948595713 9 Manual.Count131072.C022466.packed 128 cuts22466 = true := by
 decide +kernel
def pointBounds22466 : List (Nat × Nat × Nat) := [(2948616192,101523725144480,101524106383568),(2948708352,101524125306570,101524506545891)]
theorem point_links_checked22466 : (cuts22466.take 2).map (fun c => (2948595713-1+2*2^9*c.k,101523636843668+c.lower,101524018082705+c.upper)) = pointBounds22466 := by
 decide +kernel
def cuts22467 : List PrefixCut := [⟨72,320825030,320825207⟩,
⟨128,572343939,572344260⟩]
theorem checked22467 : checkPrefixCuts (2^48) 2948726785 9 Manual.Count131072.C022467.packed 128 cuts22467 = true := by
 decide +kernel
def pointBounds22467 : List (Nat × Nat × Nat) := [(2948800512,101524528033463,101524909273008)]
theorem point_links_checked22467 : (cuts22467.take 1).map (fun c => (2948726785-1+2*2^9*c.k,101524207208433+c.lower,101524588447801+c.upper)) = pointBounds22467 := by
 decide +kernel
def cuts22468 : List PrefixCut := [⟨34,150049926,150050015⟩,
⟨124,553610621,553610941⟩,
⟨128,570218573,570218902⟩]
theorem checked22468 : checkPrefixCuts (2^48) 2948857857 9 Manual.Count131072.C022468.packed 128 cuts22468 = true := by
 decide +kernel
def pointBounds22468 : List (Nat × Nat × Nat) := [(2948892672,101524929602298,101525310842076),(2948984832,101525333162993,101525714403002)]
theorem point_links_checked22468 : (cuts22468.take 2).map (fun c => (2948857857-1+2*2^9*c.k,101524779552372+c.lower,101525160792061+c.upper)) = pointBounds22468 := by
 decide +kernel
def cuts22469 : List PrefixCut := [⟨86,387035519,387035750⟩,
⟨128,578974158,578974499⟩]
theorem checked22469 : checkPrefixCuts (2^48) 2948988929 9 Manual.Count131072.C022469.packed 128 cuts22469 = true := by
 decide +kernel
def pointBounds22469 : List (Nat × Nat × Nat) := [(2949076992,101525736806464,101526118046713)]
theorem point_links_checked22469 : (cuts22469.take 1).map (fun c => (2948988929-1+2*2^9*c.k,101525349770945+c.lower,101525731010963+c.upper)) = pointBounds22469 := by
 decide +kernel
def cuts22470 : List PrefixCut := [⟨48,216464476,216464596⟩,
⟨128,575703561,575703888⟩]
theorem checked22470 : checkPrefixCuts (2^48) 2949120001 9 Manual.Count131072.C022470.packed 128 cuts22470 = true := by
 decide +kernel
def pointBounds22470 : List (Nat × Nat × Nat) := [(2949169152,101526145209579,101526526450058)]
theorem point_links_checked22470 : (cuts22470.take 1).map (fun c => (2949120001-1+2*2^9*c.k,101525928745103+c.lower,101526309985462+c.upper)) = pointBounds22470 := by
 decide +kernel
def cuts22471 : List PrefixCut := [⟨11,51441766,51441797⟩,
⟨102,457242365,457242624⟩,
⟨128,571192518,571192844⟩]
theorem checked22471 : checkPrefixCuts (2^48) 2949251073 9 Manual.Count131072.C022471.packed 128 cuts22471 = true := by
 decide +kernel
def pointBounds22471 : List (Nat × Nat × Nat) := [(2949262336,101526555890430,101526937131147),(2949355520,101526961691029,101527342931974)]
theorem point_links_checked22471 : (cuts22471.take 2).map (fun c => (2949251073-1+2*2^9*c.k,101526504448664+c.lower,101526885689350+c.upper)) = pointBounds22471 := by
 decide +kernel
def cuts22472 : List PrefixCut := [⟨65,294700568,294700738⟩,
⟨128,583000682,583001010⟩]
theorem checked22472 : checkPrefixCuts (2^48) 2949382145 9 Manual.Count131072.C022472.packed 128 cuts22472 = true := by
 decide +kernel
def pointBounds22472 : List (Nat × Nat × Nat) := [(2949448704,101527370341750,101527751582932)]
theorem point_links_checked22472 : (cuts22472.take 1).map (fun c => (2949382145-1+2*2^9*c.k,101527075641182+c.lower,101527456882194+c.upper)) = pointBounds22472 := by
 decide +kernel
def cuts22473 : List PrefixCut := [⟨28,123009915,123009985⟩,
⟨119,531253164,531253468⟩,
⟨128,572095864,572096190⟩]
theorem checked22473 : checkPrefixCuts (2^48) 2949513217 9 Manual.Count131072.C022473.packed 128 cuts22473 = true := by
 decide +kernel
def pointBounds22473 : List (Nat × Nat × Nat) := [(2949541888,101527781651779,101528162893189),(2949635072,101528189895028,101528571136672)]
theorem point_links_checked22473 : (cuts22473.take 2).map (fun c => (2949513217-1+2*2^9*c.k,101527658641864+c.lower,101528039883204+c.upper)) = pointBounds22473 := by
 decide +kernel
def cuts22474 : List PrefixCut := [⟨82,370632081,370632289⟩,
⟨128,574074451,574074772⟩]
theorem checked22474 : checkPrefixCuts (2^48) 2949644289 9 Manual.Count131072.C022474.packed 128 cuts22474 = true := by
 decide +kernel
def pointBounds22474 : List (Nat × Nat × Nat) := [(2949728256,101528601369809,101528982611683)]
theorem point_links_checked22474 : (cuts22474.take 1).map (fun c => (2949644289-1+2*2^9*c.k,101528230737728+c.lower,101528611979394+c.upper)) = pointBounds22474 := by
 decide +kernel
def cuts22475 : List PrefixCut := [⟨45,201912405,201912521⟩,
⟨128,576148050,576148375⟩]
theorem checked22475 : checkPrefixCuts (2^48) 2949775361 9 Manual.Count131072.C022475.packed 128 cuts22475 = true := by
 decide +kernel
def pointBounds22475 : List (Nat × Nat × Nat) := [(2949821440,101529006724584,101529387966687)]
theorem point_links_checked22475 : (cuts22475.take 1).map (fun c => (2949775361-1+2*2^9*c.k,101528804812179+c.lower,101529186054166+c.upper)) = pointBounds22475 := by
 decide +kernel
def cuts22476 : List PrefixCut := [⟨8,34159684,34159703⟩,
⟨99,440156806,440157058⟩,
⟨128,565722261,565722583⟩]
theorem checked22476 : checkPrefixCuts (2^48) 2949906433 9 Manual.Count131072.C022476.packed 128 cuts22476 = true := by
 decide +kernel
def pointBounds22476 : List (Nat × Nat × Nat) := [(2949914624,101529415119913,101529796362244),(2950007808,101529821117035,101530202359599)]
theorem point_links_checked22476 : (cuts22476.take 2).map (fun c => (2949906433-1+2*2^9*c.k,101529380960229+c.lower,101529762202541+c.upper)) = pointBounds22476 := by
 decide +kernel
def cuts22477 : List PrefixCut := [⟨62,280800394,280800550⟩,
⟨128,579436344,579436666⟩]
theorem checked22477 : checkPrefixCuts (2^48) 2950037505 9 Manual.Count131072.C022477.packed 128 cuts22477 = true := by
 decide +kernel
def pointBounds22477 : List (Nat × Nat × Nat) := [(2950100992,101530227482884,101530608725674)]
theorem point_links_checked22477 : (cuts22477.take 1).map (fun c => (2950037505-1+2*2^9*c.k,101529946682490+c.lower,101530327925124+c.upper)) = pointBounds22477 := by
 decide +kernel
def cuts22478 : List PrefixCut := [⟨25,106858482,106858546⟩,
⟨116,519686456,519686759⟩,
⟨128,573590688,573591022⟩]
theorem checked22478 : checkPrefixCuts (2^48) 2950168577 9 Manual.Count131072.C022478.packed 128 cuts22478 = true := by
 decide +kernel
def pointBounds22478 : List (Nat × Nat × Nat) := [(2950194176,101530632977316,101531014220336),(2950287360,101531045805290,101531427048549)]
theorem point_links_checked22478 : (cuts22478.take 2).map (fun c => (2950168577-1+2*2^9*c.k,101530526118834+c.lower,101530907361790+c.upper)) = pointBounds22478 := by
 decide +kernel
def cuts22479 : List PrefixCut := [⟨79,363967048,363967252⟩,
⟨128,581102221,581102555⟩]
theorem checked22479 : checkPrefixCuts (2^48) 2950299649 9 Manual.Count131072.C022479.packed 128 cuts22479 = true := by
 decide +kernel
def pointBounds22479 : List (Nat × Nat × Nat) := [(2950380544,101531463676570,101531844920064)]
theorem point_links_checked22479 : (cuts22479.take 1).map (fun c => (2950299649-1+2*2^9*c.k,101531099709522+c.lower,101531480952812+c.upper)) = pointBounds22479 := by
 decide +kernel
def cuts22480 : List PrefixCut := [⟨42,183359941,183360046⟩,
⟨128,569914607,569914931⟩]
theorem checked22480 : checkPrefixCuts (2^48) 2950430721 9 Manual.Count131072.C022480.packed 128 cuts22480 = true := by
 decide +kernel
def pointBounds22480 : List (Nat × Nat × Nat) := [(2950473728,101531864171684,101532245415413)]
theorem point_links_checked22480 : (cuts22480.take 1).map (fun c => (2950430721-1+2*2^9*c.k,101531680811743+c.lower,101532062055367+c.upper)) = pointBounds22480 := by
 decide +kernel
def cuts22481 : List PrefixCut := [⟨5,23086066,23086079⟩,
⟨96,424891402,424891645⟩,
⟨128,567695238,567695559⟩]
theorem checked22481 : checkPrefixCuts (2^48) 2950561793 9 Manual.Count131072.C022481.packed 128 cuts22481 = true := by
 decide +kernel
def pointBounds22481 : List (Nat × Nat × Nat) := [(2950566912,101532273812416,101532655056377),(2950660096,101532675617752,101533056861943)]
theorem point_links_checked22481 : (cuts22481.take 2).map (fun c => (2950561793-1+2*2^9*c.k,101532250726350+c.lower,101532631970298+c.upper)) = pointBounds22481 := by
 decide +kernel
def cuts22482 : List PrefixCut := [⟨59,266524796,266524947⟩,
⟨128,577495246,577495578⟩]
theorem checked22482 : checkPrefixCuts (2^48) 2950692865 9 Manual.Count131072.C022482.packed 128 cuts22482 = true := by
 decide +kernel
def pointBounds22482 : List (Nat × Nat × Nat) := [(2950753280,101533084946384,101533466190804)]
theorem point_links_checked22482 : (cuts22482.take 1).map (fun c => (2950692865-1+2*2^9*c.k,101532818421588+c.lower,101533199665857+c.upper)) = pointBounds22482 := by
 decide +kernel
def cuts22483 : List PrefixCut := [⟨22,97295980,97296034⟩,
⟨113,498014000,498014284⟩,
⟨128,562970902,562971225⟩]
theorem checked22483 : checkPrefixCuts (2^48) 2950823937 9 Manual.Count131072.C022483.packed 128 cuts22483 = true := by
 decide +kernel
def pointBounds22483 : List (Nat × Nat × Nat) := [(2950846464,101533493212814,101533874457469),(2950939648,101533893930834,101534275175719)]
theorem point_links_checked22483 : (cuts22483.take 2).map (fun c => (2950823937-1+2*2^9*c.k,101533395916834+c.lower,101533777161435+c.upper)) = pointBounds22483 := by
 decide +kernel
def cuts22484 : List PrefixCut := [⟨76,341280691,341280884⟩,
⟨128,576967050,576967374⟩]
theorem checked22484 : checkPrefixCuts (2^48) 2950955009 9 Manual.Count131072.C022484.packed 128 cuts22484 = true := by
 decide +kernel
def pointBounds22484 : List (Nat × Nat × Nat) := [(2951032832,101534300168427,101534681413544)]
theorem point_links_checked22484 : (cuts22484.take 1).map (fun c => (2950955009-1+2*2^9*c.k,101533958887736+c.lower,101534340132660+c.upper)) = pointBounds22484 := by
 decide +kernel
def cuts22485 : List PrefixCut := [⟨39,172636828,172636920⟩,
⟨128,569120453,569120772⟩]
theorem checked22485 : checkPrefixCuts (2^48) 2951086081 9 Manual.Count131072.C022485.packed 128 cuts22485 = true := by
 decide +kernel
def pointBounds22485 : List (Nat × Nat × Nat) := [(2951126016,101534708491614,101535089736954)]
theorem point_links_checked22485 : (cuts22485.take 1).map (fun c => (2951086081-1+2*2^9*c.k,101534535854786+c.lower,101534917100034+c.upper)) = pointBounds22485 := by
 decide +kernel
def cuts22486 : List PrefixCut := [⟨2,8202321,8202327⟩,
⟨93,419837709,419837952⟩,
⟨128,577774097,577774430⟩]
theorem checked22486 : checkPrefixCuts (2^48) 2951217153 9 Manual.Count131072.C022486.packed 128 cuts22486 = true := by
 decide +kernel
def pointBounds22486 : List (Nat × Nat × Nat) := [(2951219200,101535113177560,101535494423133),(2951312384,101535524812948,101535906058758)]
theorem point_links_checked22486 : (cuts22486.take 2).map (fun c => (2951217153-1+2*2^9*c.k,101535104975239+c.lower,101535486220806+c.upper)) = pointBounds22486 := by
 decide +kernel
def cuts22487 : List PrefixCut := [⟨56,248917512,248917658⟩,
⟨128,573456798,573457129⟩]
theorem checked22487 : checkPrefixCuts (2^48) 2951348225 9 Manual.Count131072.C022487.packed 128 cuts22487 = true := by
 decide +kernel
def pointBounds22487 : List (Nat × Nat × Nat) := [(2951405568,101535931666848,101536312912894)]
theorem point_links_checked22487 : (cuts22487.take 1).map (fun c => (2951348225-1+2*2^9*c.k,101535682749336+c.lower,101536063995236+c.upper)) = pointBounds22487 := by
 decide +kernel
def cuts22488 : List PrefixCut := [⟨19,83923030,83923077⟩,
⟨110,494184377,494184656⟩,
⟨128,570665868,570666196⟩]
theorem checked22488 : checkPrefixCuts (2^48) 2951479297 9 Manual.Count131072.C022488.packed 128 cuts22488 = true := by
 decide +kernel
def pointBounds22488 : List (Nat × Nat × Nat) := [(2951498752,101536340129164,101536721375442),(2951591936,101536750390511,101537131637021)]
theorem point_links_checked22488 : (cuts22488.take 2).map (fun c => (2951479297-1+2*2^9*c.k,101536256206134+c.lower,101536637452365+c.upper)) = pointBounds22488 := by
 decide +kernel
def cuts22489 : List PrefixCut := [⟨73,326710094,326710277⟩,
⟨128,576552874,576553199⟩]
theorem checked22489 : checkPrefixCuts (2^48) 2951610369 9 Manual.Count131072.C022489.packed 128 cuts22489 = true := by
 decide +kernel
def pointBounds22489 : List (Nat × Nat × Nat) := [(2951685120,101537153582096,101537534828838)]
theorem point_links_checked22489 : (cuts22489.take 1).map (fun c => (2951610369-1+2*2^9*c.k,101536826872002+c.lower,101537208118561+c.upper)) = pointBounds22489 := by
 decide +kernel
def cuts22490 : List PrefixCut := [⟨36,164016315,164016409⟩,
⟨127,571282764,571283091⟩,
⟨128,575669081,575669410⟩]
theorem checked22490 : checkPrefixCuts (2^48) 2951741441 9 Manual.Count131072.C022490.packed 128 cuts22490 = true := by
 decide +kernel
def pointBounds22490 : List (Nat × Nat × Nat) := [(2951778304,101537567441191,101537948688169),(2951871488,101537974707640,101538355954851)]
theorem point_links_checked22490 : (cuts22490.take 2).map (fun c => (2951741441-1+2*2^9*c.k,101537403424876+c.lower,101537784671760+c.upper)) = pointBounds22490 := by
 decide +kernel
def cuts22491 : List PrefixCut := [⟨90,405251070,405251303⟩,
⟨128,576215599,576215930⟩]
theorem checked22491 : checkPrefixCuts (2^48) 2951872513 9 Manual.Count131072.C022491.packed 128 cuts22491 = true := by
 decide +kernel
def pointBounds22491 : List (Nat × Nat × Nat) := [(2951964672,101538384345027,101538765592473)]
theorem point_links_checked22491 : (cuts22491.take 1).map (fun c => (2951872513-1+2*2^9*c.k,101537979093957+c.lower,101538360341170+c.upper)) = pointBounds22491 := by
 decide +kernel
def cuts22492 : List PrefixCut := [⟨53,236085553,236085685⟩,
⟨128,573615575,573615892⟩]
theorem checked22492 : checkPrefixCuts (2^48) 2952003585 9 Manual.Count131072.C022492.packed 128 cuts22492 = true := by
 decide +kernel
def pointBounds22492 : List (Nat × Nat × Nat) := [(2952057856,101538791395109,101539172642785)]
theorem point_links_checked22492 : (cuts22492.take 1).map (fun c => (2952003585-1+2*2^9*c.k,101538555309556+c.lower,101538936557100+c.upper)) = pointBounds22492 := by
 decide +kernel
def cuts22493 : List PrefixCut := [⟨16,70842051,70842089⟩,
⟨107,478343104,478343379⟩,
⟨128,569776408,569776739⟩]
theorem checked22493 : checkPrefixCuts (2^48) 2952134657 9 Manual.Count131072.C022493.packed 128 cuts22493 = true := by
 decide +kernel
def pointBounds22493 : List (Nat × Nat × Nat) := [(2952151040,101539199767182,101539581015081),(2952244224,101539607268235,101539988516371)]
theorem point_links_checked22493 : (cuts22493.take 2).map (fun c => (2952134657-1+2*2^9*c.k,101539128925131+c.lower,101539510172992+c.upper)) = pointBounds22493 := by
 decide +kernel
def cuts22494 : List PrefixCut := [⟨70,316722259,316722438⟩,
⟨128,576996927,576997255⟩]
theorem checked22494 : checkPrefixCuts (2^48) 2952265729 9 Manual.Count131072.C022494.packed 128 cuts22494 = true := by
 decide +kernel
def pointBounds22494 : List (Nat × Nat × Nat) := [(2952337408,101540015423798,101540396672169)]
theorem point_links_checked22494 : (cuts22494.take 1).map (fun c => (2952265729-1+2*2^9*c.k,101539698701539+c.lower,101540079949731+c.upper)) = pointBounds22494 := by
 decide +kernel
def cuts22495 : List PrefixCut := [⟨33,147391330,147391412⟩,
⟨124,555807126,555807441⟩,
⟨128,573920508,573920834⟩]
theorem checked22495 : checkPrefixCuts (2^48) 2952396801 9 Manual.Count131072.C022495.packed 128 cuts22495 = true := by
 decide +kernel
def pointBounds22495 : List (Nat × Nat × Nat) := [(2952430592,101540423089796,101540804338398),(2952523776,101540831505592,101541212754427)]
theorem point_links_checked22495 : (cuts22495.take 2).map (fun c => (2952396801-1+2*2^9*c.k,101540275698466+c.lower,101540656946986+c.upper)) = pointBounds22495 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000077
