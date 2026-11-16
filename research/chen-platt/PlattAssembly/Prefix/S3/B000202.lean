import PlattAssemblyKernel
import PlattCertificates.Count131072.C026464
import PlattCertificates.Count131072.C026465
import PlattCertificates.Count131072.C026466
import PlattCertificates.Count131072.C026467
import PlattCertificates.Count131072.C026468
import PlattCertificates.Count131072.C026469
import PlattCertificates.Count131072.C026470
import PlattCertificates.Count131072.C026471
import PlattCertificates.Count131072.C026472
import PlattCertificates.Count131072.C026473
import PlattCertificates.Count131072.C026474
import PlattCertificates.Count131072.C026475
import PlattCertificates.Count131072.C026476
import PlattCertificates.Count131072.C026477
import PlattCertificates.Count131072.C026478
import PlattCertificates.Count131072.C026479
import PlattCertificates.Count131072.C026480
import PlattCertificates.Count131072.C026481
import PlattCertificates.Count131072.C026482
import PlattCertificates.Count131072.C026483
import PlattCertificates.Count131072.C026484
import PlattCertificates.Count131072.C026485
import PlattCertificates.Count131072.C026486
import PlattCertificates.Count131072.C026487
import PlattCertificates.Count131072.C026488
import PlattCertificates.Count131072.C026489
import PlattCertificates.Count131072.C026490
import PlattCertificates.Count131072.C026491
import PlattCertificates.Count131072.C026492
import PlattCertificates.Count131072.C026493
import PlattCertificates.Count131072.C026494
import PlattCertificates.Count131072.C026495
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000202
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26464 : List PrefixCut := [⟨27,102048395,102048452⟩,
⟨128,485188697,485188970⟩]
theorem checked26464 : checkPrefixCuts (2^48) 3472621569 9 Manual.Count131072.C026464.packed 128 cuts26464 = true := by
 decide +kernel
def pointBounds26464 : List (Nat × Nat × Nat) := [(3472649216,103627373265918,103627755690971)]
theorem point_links_checked26464 : (cuts26464.take 1).map (fun c => (3472621569-1+2*2^9*c.k,103627271217523+c.lower,103627653642519+c.upper)) = pointBounds26464 := by
 decide +kernel
def cuts26465 : List PrefixCut := [⟨5,19209402,19209412⟩,
⟨111,422438158,422438400⟩,
⟨128,485008397,485008675⟩]
theorem checked26465 : checkPrefixCuts (2^48) 3472752641 9 Manual.Count131072.C026465.packed 128 cuts26465 = true := by
 decide +kernel
def pointBounds26465 : List (Nat × Nat × Nat) := [(3472757760,103627775615622,103628158040901),(3472866304,103628178844378,103628561269889)]
theorem point_links_checked26465 : (cuts26465.take 2).map (fun c => (3472752641-1+2*2^9*c.k,103627756406220+c.lower,103628138831489+c.upper)) = pointBounds26465 := by
 decide +kernel
def cuts26466 : List PrefixCut := [⟨89,335783039,335783226⟩,
⟨128,477371704,477371968⟩]
theorem checked26466 : checkPrefixCuts (2^48) 3472883713 9 Manual.Count131072.C026466.packed 128 cuts26466 = true := by
 decide +kernel
def pointBounds26466 : List (Nat × Nat × Nat) := [(3472974848,103628577197656,103628959623390)]
theorem point_links_checked26466 : (cuts26466.take 1).map (fun c => (3472883713-1+2*2^9*c.k,103628241414617+c.lower,103628623840164+c.upper)) = pointBounds26466 := by
 decide +kernel
def cuts26467 : List PrefixCut := [⟨67,253915500,253915641⟩,
⟨128,488942930,488943205⟩]
theorem checked26467 : checkPrefixCuts (2^48) 3473014785 9 Manual.Count131072.C026467.packed 128 cuts26467 = true := by
 decide +kernel
def pointBounds26467 : List (Nat × Nat × Nat) := [(3473083392,103628972701821,103629355127773)]
theorem point_links_checked26467 : (cuts26467.take 1).map (fun c => (3473014785-1+2*2^9*c.k,103628718786321+c.lower,103629101212132+c.upper)) = pointBounds26467 := by
 decide +kernel
def cuts26468 : List PrefixCut := [⟨45,171081097,171081189⟩,
⟨128,491193650,491193922⟩]
theorem checked26468 : checkPrefixCuts (2^48) 3473145857 9 Manual.Count131072.C026468.packed 128 cuts26468 = true := by
 decide +kernel
def pointBounds26468 : List (Nat × Nat × Nat) := [(3473191936,103629378810348,103629761236526)]
theorem point_links_checked26468 : (cuts26468.take 1).map (fun c => (3473145857-1+2*2^9*c.k,103629207729251+c.lower,103629590155337+c.upper)) = pointBounds26468 := by
 decide +kernel
def cuts26469 : List PrefixCut := [⟨23,87036837,87036883⟩,
⟨128,490526769,490527035⟩]
theorem checked26469 : checkPrefixCuts (2^48) 3473276929 9 Manual.Count131072.C026469.packed 128 cuts26469 = true := by
 decide +kernel
def pointBounds26469 : List (Nat × Nat × Nat) := [(3473300480,103629785959738,103630168386142)]
theorem point_links_checked26469 : (cuts26469.take 1).map (fun c => (3473276929-1+2*2^9*c.k,103629698922901+c.lower,103630081349259+c.upper)) = pointBounds26469 := by
 decide +kernel
def cuts26470 : List PrefixCut := [⟨1,3403557,3403559⟩,
⟨107,398453148,398453372⟩,
⟨128,478839157,478839424⟩]
theorem checked26470 : checkPrefixCuts (2^48) 3473408001 9 Manual.Count131072.C026470.packed 128 cuts26470 = true := by
 decide +kernel
def pointBounds26470 : List (Nat × Nat × Nat) := [(3473409024,103630192853227,103630575279853),(3473517568,103630587902818,103630970329666)]
theorem point_links_checked26470 : (cuts26470.take 2).map (fun c => (3473408001-1+2*2^9*c.k,103630189449670+c.lower,103630571876294+c.upper)) = pointBounds26470 := by
 decide +kernel
def cuts26471 : List PrefixCut := [⟨86,323645817,323646001⟩,
⟨128,483764024,483764294⟩]
theorem checked26471 : checkPrefixCuts (2^48) 3473539073 9 Manual.Count131072.C026471.packed 128 cuts26471 = true := by
 decide +kernel
def pointBounds26471 : List (Nat × Nat × Nat) := [(3473627136,103630991934644,103631374361719)]
theorem point_links_checked26471 : (cuts26471.take 1).map (fun c => (3473539073-1+2*2^9*c.k,103630668288827+c.lower,103631050715718+c.upper)) = pointBounds26471 := by
 decide +kernel
def cuts26472 : List PrefixCut := [⟨65,243090612,243090754⟩,
⟨128,487473097,487473374⟩]
theorem checked26472 : checkPrefixCuts (2^48) 3473670145 9 Manual.Count131072.C026472.packed 128 cuts26472 = true := by
 decide +kernel
def pointBounds26472 : List (Nat × Nat × Nat) := [(3473736704,103631395143463,103631777570766)]
theorem point_links_checked26472 : (cuts26472.take 1).map (fun c => (3473670145-1+2*2^9*c.k,103631152052851+c.lower,103631534480012+c.upper)) = pointBounds26472 := by
 decide +kernel
def cuts26473 : List PrefixCut := [⟨44,166673374,166673463⟩,
⟨128,483241458,483241723⟩]
theorem checked26473 : checkPrefixCuts (2^48) 3473801217 9 Manual.Count131072.C026473.packed 128 cuts26473 = true := by
 decide +kernel
def pointBounds26473 : List (Nat × Nat × Nat) := [(3473846272,103631806199322,103632188626849)]
theorem point_links_checked26473 : (cuts26473.take 1).map (fun c => (3473801217-1+2*2^9*c.k,103631639525948+c.lower,103632021953386+c.upper)) = pointBounds26473 := by
 decide +kernel
def cuts26474 : List PrefixCut := [⟨23,89937304,89937353⟩,
⟨128,486869295,486869559⟩]
theorem checked26474 : checkPrefixCuts (2^48) 3473932289 9 Manual.Count131072.C026474.packed 128 cuts26474 = true := by
 decide +kernel
def pointBounds26474 : List (Nat × Nat × Nat) := [(3473955840,103632212704710,103632595132462)]
theorem point_links_checked26474 : (cuts26474.take 1).map (fun c => (3473932289-1+2*2^9*c.k,103632122767406+c.lower,103632505195109+c.upper)) = pointBounds26474 := by
 decide +kernel
def cuts26475 : List PrefixCut := [⟨2,7535026,7535030⟩,
⟨109,404454360,404454586⟩,
⟨128,480774238,480774505⟩]
theorem checked26475 : checkPrefixCuts (2^48) 3474063361 9 Manual.Count131072.C026475.packed 128 cuts26475 = true := by
 decide +kernel
def pointBounds26475 : List (Nat × Nat × Nat) := [(3474065408,103632617171727,103632999599698),(3474174976,103633014091061,103633396519254)]
theorem point_links_checked26475 : (cuts26475.take 2).map (fun c => (3474063361-1+2*2^9*c.k,103632609636701+c.lower,103632992064668+c.upper)) = pointBounds26475 := by
 decide +kernel
def cuts26476 : List PrefixCut := [⟨88,330633251,330633437⟩,
⟨128,481809429,481809701⟩]
theorem checked26476 : checkPrefixCuts (2^48) 3474194433 9 Manual.Count131072.C026476.packed 128 cuts26476 = true := by
 decide +kernel
def pointBounds26476 : List (Nat × Nat × Nat) := [(3474284544,103633421044190,103633803472610)]
theorem point_links_checked26476 : (cuts26476.take 1).map (fun c => (3474194433-1+2*2^9*c.k,103633090410939+c.lower,103633472839173+c.upper)) = pointBounds26476 := by
 decide +kernel
def cuts26477 : List PrefixCut := [⟨67,249606903,249607046⟩,
⟨128,478631699,478631967⟩]
theorem checked26477 : checkPrefixCuts (2^48) 3474325505 9 Manual.Count131072.C026477.packed 128 cuts26477 = true := by
 decide +kernel
def pointBounds26477 : List (Nat × Nat × Nat) := [(3474394112,103633821827271,103634204255920)]
theorem point_links_checked26477 : (cuts26477.take 1).map (fun c => (3474325505-1+2*2^9*c.k,103633572220368+c.lower,103633954648874+c.upper)) = pointBounds26477 := by
 decide +kernel
def cuts26478 : List PrefixCut := [⟨46,175958257,175958356⟩,
⟨128,485175559,485175830⟩]
theorem checked26478 : checkPrefixCuts (2^48) 3474456577 9 Manual.Count131072.C026478.packed 128 cuts26478 = true := by
 decide +kernel
def pointBounds26478 : List (Nat × Nat × Nat) := [(3474503680,103634226810324,103634609239197)]
theorem point_links_checked26478 : (cuts26478.take 1).map (fun c => (3474456577-1+2*2^9*c.k,103634050852067+c.lower,103634433280841+c.upper)) = pointBounds26478 := by
 decide +kernel
def cuts26479 : List PrefixCut := [⟨25,91297465,91297519⟩,
⟨128,485076112,485076385⟩]
theorem checked26479 : checkPrefixCuts (2^48) 3474587649 9 Manual.Count131072.C026479.packed 128 cuts26479 = true := by
 decide +kernel
def pointBounds26479 : List (Nat × Nat × Nat) := [(3474613248,103634627325091,103635009754190)]
theorem point_links_checked26479 : (cuts26479.take 1).map (fun c => (3474587649-1+2*2^9*c.k,103634536027626+c.lower,103634918456671+c.upper)) = pointBounds26479 := by
 decide +kernel
def cuts26480 : List PrefixCut := [⟨4,15634251,15634259⟩,
⟨111,417743848,417744078⟩,
⟨128,481736747,481737015⟩]
theorem checked26480 : checkPrefixCuts (2^48) 3474718721 9 Manual.Count131072.C026480.packed 128 cuts26480 = true := by
 decide +kernel
def pointBounds26480 : List (Nat × Nat × Nat) := [(3474722816,103635036737989,103635419167315),(3474832384,103635438847586,103635821277134)]
theorem point_links_checked26480 : (cuts26480.take 2).map (fun c => (3474718721-1+2*2^9*c.k,103635021103738+c.lower,103635403533056+c.upper)) = pointBounds26480 := by
 decide +kernel
def cuts26481 : List PrefixCut := [⟨90,340372062,340372250⟩,
⟨128,481070572,481070839⟩]
theorem checked26481 : checkPrefixCuts (2^48) 3474849793 9 Manual.Count131072.C026481.packed 128 cuts26481 = true := by
 decide +kernel
def pointBounds26481 : List (Nat × Nat × Nat) := [(3474941952,103635843212547,103636225642321)]
theorem point_links_checked26481 : (cuts26481.take 1).map (fun c => (3474849793-1+2*2^9*c.k,103635502840485+c.lower,103635885270071+c.upper)) = pointBounds26481 := by
 decide +kernel
def cuts26482 : List PrefixCut := [⟨69,260818709,260818853⟩,
⟨128,482672409,482672679⟩]
theorem checked26482 : checkPrefixCuts (2^48) 3474980865 9 Manual.Count131072.C026482.packed 128 cuts26482 = true := by
 decide +kernel
def pointBounds26482 : List (Nat × Nat × Nat) := [(3475051520,103636244729766,103636627159763)]
theorem point_links_checked26482 : (cuts26482.take 1).map (fun c => (3474980865-1+2*2^9*c.k,103635983911057+c.lower,103636366340910+c.upper)) = pointBounds26482 := by
 decide +kernel
def cuts26483 : List PrefixCut := [⟨48,182728769,182728870⟩,
⟨128,481763254,481763525⟩]
theorem checked26483 : checkPrefixCuts (2^48) 3475111937 9 Manual.Count131072.C026483.packed 128 cuts26483 = true := by
 decide +kernel
def pointBounds26483 : List (Nat × Nat × Nat) := [(3475161088,103636649312235,103637031742459)]
theorem point_links_checked26483 : (cuts26483.take 1).map (fun c => (3475111937-1+2*2^9*c.k,103636466583466+c.lower,103636849013589+c.upper)) = pointBounds26483 := by
 decide +kernel
def cuts26484 : List PrefixCut := [⟨27,102214403,102214459⟩,
⟨128,485389715,485389983⟩]
theorem checked26484 : checkPrefixCuts (2^48) 3475243009 9 Manual.Count131072.C026484.packed 128 cuts26484 = true := by
 decide +kernel
def pointBounds26484 : List (Nat × Nat × Nat) := [(3475270656,103637050561123,103637432991573)]
theorem point_links_checked26484 : (cuts26484.take 1).map (fun c => (3475243009-1+2*2^9*c.k,103636948346720+c.lower,103637330777114+c.upper)) = pointBounds26484 := by
 decide +kernel
def cuts26485 : List PrefixCut := [⟨6,20814734,20814747⟩,
⟨113,430947252,430947495⟩,
⟨128,485776379,485776654⟩]
theorem checked26485 : checkPrefixCuts (2^48) 3475374081 9 Manual.Count131072.C026485.packed 128 cuts26485 = true := by
 decide +kernel
def pointBounds26485 : List (Nat × Nat × Nat) := [(3475380224,103637454551169,103637836981844),(3475489792,103637864683687,103638247114592)]
theorem point_links_checked26485 : (cuts26485.take 2).map (fun c => (3475374081-1+2*2^9*c.k,103637433736435+c.lower,103637816167097+c.upper)) = pointBounds26485 := by
 decide +kernel
def cuts26486 : List PrefixCut := [⟨92,344438120,344438316⟩,
⟨128,481141751,481142020⟩]
theorem checked26486 : checkPrefixCuts (2^48) 3475505153 9 Manual.Count131072.C026486.packed 128 cuts26486 = true := by
 decide +kernel
def pointBounds26486 : List (Nat × Nat × Nat) := [(3475599360,103638263950934,103638646382067)]
theorem point_links_checked26486 : (cuts26486.take 1).map (fun c => (3475505153-1+2*2^9*c.k,103637919512814+c.lower,103638301943751+c.upper)) = pointBounds26486 := by
 decide +kernel
def cuts26487 : List PrefixCut := [⟨71,268786823,268786977⟩,
⟨128,486630510,486630784⟩]
theorem checked26487 : checkPrefixCuts (2^48) 3475636225 9 Manual.Count131072.C026487.packed 128 cuts26487 = true := by
 decide +kernel
def pointBounds26487 : List (Nat × Nat × Nat) := [(3475708928,103638669441388,103639051872748)]
theorem point_links_checked26487 : (cuts26487.take 1).map (fun c => (3475636225-1+2*2^9*c.k,103638400654565+c.lower,103638783085771+c.upper)) = pointBounds26487 := by
 decide +kernel
def cuts26488 : List PrefixCut := [⟨50,189253768,189253873⟩,
⟨128,479243020,479243286⟩]
theorem checked26488 : checkPrefixCuts (2^48) 3475767297 9 Manual.Count131072.C026488.packed 128 cuts26488 = true := by
 decide +kernel
def pointBounds26488 : List (Nat × Nat × Nat) := [(3475818496,103639076538843,103639458970428)]
theorem point_links_checked26488 : (cuts26488.take 1).map (fun c => (3475767297-1+2*2^9*c.k,103638887285075+c.lower,103639269716555+c.upper)) = pointBounds26488 := by
 decide +kernel
def cuts26489 : List PrefixCut := [⟨29,108916339,108916401⟩,
⟨128,485784054,485784326⟩]
theorem checked26489 : checkPrefixCuts (2^48) 3475898369 9 Manual.Count131072.C026489.packed 128 cuts26489 = true := by
 decide +kernel
def pointBounds26489 : List (Nat × Nat × Nat) := [(3475928064,103639475444434,103639857876242)]
theorem point_links_checked26489 : (cuts26489.take 1).map (fun c => (3475898369-1+2*2^9*c.k,103639366528095+c.lower,103639748959841+c.upper)) = pointBounds26489 := by
 decide +kernel
def cuts26490 : List PrefixCut := [⟨8,30365956,30365975⟩,
⟨115,442688227,442688479⟩,
⟨128,489409698,489409976⟩]
theorem checked26490 : checkPrefixCuts (2^48) 3476029441 9 Manual.Count131072.C026490.packed 128 cuts26490 = true := by
 decide +kernel
def pointBounds26490 : List (Nat × Nat × Nat) := [(3476037632,103639882678105,103640265110142),(3476147200,103640295000376,103640677432646)]
theorem point_links_checked26490 : (cuts26490.take 2).map (fun c => (3476029441-1+2*2^9*c.k,103639852312149+c.lower,103640234744167+c.upper)) = pointBounds26490 := by
 decide +kernel
def cuts26491 : List PrefixCut := [⟨94,353441946,353442144⟩,
⟨128,483237318,483237589⟩]
theorem checked26491 : checkPrefixCuts (2^48) 3476160513 9 Manual.Count131072.C026491.packed 128 cuts26491 = true := by
 decide +kernel
def pointBounds26491 : List (Nat × Nat × Nat) := [(3476256768,103640695163793,103641077596287)]
theorem point_links_checked26491 : (cuts26491.take 1).map (fun c => (3476160513-1+2*2^9*c.k,103640341721847+c.lower,103640724154143+c.upper)) = pointBounds26491 := by
 decide +kernel
def cuts26492 : List PrefixCut := [⟨73,270841307,270841458⟩,
⟨128,475769981,475770243⟩]
theorem checked26492 : checkPrefixCuts (2^48) 3476291585 9 Manual.Count131072.C026492.packed 128 cuts26492 = true := by
 decide +kernel
def pointBounds26492 : List (Nat × Nat × Nat) := [(3476366336,103641095800472,103641478233190)]
theorem point_links_checked26492 : (cuts26492.take 1).map (fun c => (3476291585-1+2*2^9*c.k,103640824959165+c.lower,103641207391732+c.upper)) = pointBounds26492 := by
 decide +kernel
def cuts26493 : List PrefixCut := [⟨52,194561796,194561902⟩,
⟨128,480933831,480934097⟩]
theorem checked26493 : checkPrefixCuts (2^48) 3476422657 9 Manual.Count131072.C026493.packed 128 cuts26493 = true := by
 decide +kernel
def pointBounds26493 : List (Nat × Nat × Nat) := [(3476475904,103641495290942,103641877723877)]
theorem point_links_checked26493 : (cuts26493.take 1).map (fun c => (3476422657-1+2*2^9*c.k,103641300729146+c.lower,103641683161975+c.upper)) = pointBounds26493 := by
 decide +kernel
def cuts26494 : List PrefixCut := [⟨31,118935243,118935309⟩,
⟨128,490388334,490388611⟩]
theorem checked26494 : checkPrefixCuts (2^48) 3476553729 9 Manual.Count131072.C026494.packed 128 cuts26494 = true := by
 decide +kernel
def pointBounds26494 : List (Nat × Nat × Nat) := [(3476585472,103641900598220,103642283031381)]
theorem point_links_checked26494 : (cuts26494.take 1).map (fun c => (3476553729-1+2*2^9*c.k,103641781662977+c.lower,103642164096072+c.upper)) = pointBounds26494 := by
 decide +kernel
def cuts26495 : List PrefixCut := [⟨10,37727639,37727660⟩,
⟨117,438475714,438475963⟩,
⟨128,478792699,478792970⟩]
theorem checked26495 : checkPrefixCuts (2^48) 3476684801 9 Manual.Count131072.C026495.packed 128 cuts26495 = true := by
 decide +kernel
def pointBounds26495 : List (Nat × Nat × Nat) := [(3476695040,103642309778950,103642692212343),(3476804608,103642710527025,103643092960646)]
theorem point_links_checked26495 : (cuts26495.take 2).map (fun c => (3476684801-1+2*2^9*c.k,103642272051311+c.lower,103642654484683+c.upper)) = pointBounds26495 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000202
