import PlattAssemblyKernel
import PlattCertificates.Count131072.C021568
import PlattCertificates.Count131072.C021569
import PlattCertificates.Count131072.C021570
import PlattCertificates.Count131072.C021571
import PlattCertificates.Count131072.C021572
import PlattCertificates.Count131072.C021573
import PlattCertificates.Count131072.C021574
import PlattCertificates.Count131072.C021575
import PlattCertificates.Count131072.C021576
import PlattCertificates.Count131072.C021577
import PlattCertificates.Count131072.C021578
import PlattCertificates.Count131072.C021579
import PlattCertificates.Count131072.C021580
import PlattCertificates.Count131072.C021581
import PlattCertificates.Count131072.C021582
import PlattCertificates.Count131072.C021583
import PlattCertificates.Count131072.C021584
import PlattCertificates.Count131072.C021585
import PlattCertificates.Count131072.C021586
import PlattCertificates.Count131072.C021587
import PlattCertificates.Count131072.C021588
import PlattCertificates.Count131072.C021589
import PlattCertificates.Count131072.C021590
import PlattCertificates.Count131072.C021591
import PlattCertificates.Count131072.C021592
import PlattCertificates.Count131072.C021593
import PlattCertificates.Count131072.C021594
import PlattCertificates.Count131072.C021595
import PlattCertificates.Count131072.C021596
import PlattCertificates.Count131072.C021597
import PlattCertificates.Count131072.C021598
import PlattCertificates.Count131072.C021599
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21568 : List PrefixCut := [⟨82,385184954,385185181⟩,
⟨128,597857045,597857394⟩]
theorem checked21568 : checkPrefixCuts (2^48) 2830893057 9 Manual.Count131072.C021568.packed 128 cuts21568 = true := by
 decide +kernel
def pointBounds21568 : List (Nat × Nat × Nat) := [(2830977024,100997654720339,100998035657894)]
theorem point_links_checked21568 : (cuts21568.take 1).map (fun c => (2830893057-1+2*2^9*c.k,100997269535385+c.lower,100997650472713+c.upper)) = pointBounds21568 := by
 decide +kernel
def cuts21569 : List PrefixCut := [⟨41,192386151,192386263⟩,
⟨128,592858274,592858616⟩]
theorem checked21569 : checkPrefixCuts (2^48) 2831024129 9 Manual.Count131072.C021569.packed 128 cuts21569 = true := by
 decide +kernel
def pointBounds21569 : List (Nat × Nat × Nat) := [(2831066112,100998059778581,100998440716370),(2831155200,100998460250704,100998841188723)]
theorem point_links_checked21569 : (cuts21569.take 2).map (fun c => (2831024129-1+2*2^9*c.k,100997867392430+c.lower,100998248330107+c.upper)) = pointBounds21569 := by
 decide +kernel
def cuts21570 : List PrefixCut := [⟨87,406524061,406524303⟩,
⟨128,600287120,600287471⟩]
theorem checked21570 : checkPrefixCuts (2^48) 2831155201 9 Manual.Count131072.C021570.packed 128 cuts21570 = true := by
 decide +kernel
def pointBounds21570 : List (Nat × Nat × Nat) := [(2831244288,100998866774765,100999247713026)]
theorem point_links_checked21570 : (cuts21570.take 1).map (fun c => (2831155201-1+2*2^9*c.k,100998460250704+c.lower,100998841188723+c.upper)) = pointBounds21570 := by
 decide +kernel
def cuts21571 : List PrefixCut := [⟨46,213046528,213046651⟩,
⟨128,599563427,599563769⟩]
theorem checked21571 : checkPrefixCuts (2^48) 2831286273 9 Manual.Count131072.C021571.packed 128 cuts21571 = true := by
 decide +kernel
def pointBounds21571 : List (Nat × Nat × Nat) := [(2831333376,100999273584352,100999654522845)]
theorem point_links_checked21571 : (cuts21571.take 1).map (fun c => (2831286273-1+2*2^9*c.k,100999060537824+c.lower,100999441476194+c.upper)) = pointBounds21571 := by
 decide +kernel
def cuts21572 : List PrefixCut := [⟨5,21572234,21572248⟩,
⟨92,431040212,431040468⟩,
⟨128,599734483,599734835⟩]
theorem checked21572 : checkPrefixCuts (2^48) 2831417345 9 Manual.Count131072.C021572.packed 128 cuts21572 = true := by
 decide +kernel
def pointBounds21572 : List (Nat × Nat × Nat) := [(2831422464,100999681673485,101000062612211),(2831511552,101000091141463,101000472080431)]
theorem point_links_checked21572 : (cuts21572.take 2).map (fun c => (2831417345-1+2*2^9*c.k,100999660101251+c.lower,101000041039963+c.upper)) = pointBounds21572 := by
 decide +kernel
def cuts21573 : List PrefixCut := [⟨51,234796462,234796597⟩,
⟨128,588374604,588374943⟩]
theorem checked21573 : checkPrefixCuts (2^48) 2831548417 9 Manual.Count131072.C021573.packed 128 cuts21573 = true := by
 decide +kernel
def pointBounds21573 : List (Nat × Nat × Nat) := [(2831600640,101000494632196,101000875571395)]
theorem point_links_checked21573 : (cuts21573.take 1).map (fun c => (2831548417-1+2*2^9*c.k,101000259835734+c.lower,101000640774798+c.upper)) = pointBounds21573 := by
 decide +kernel
def cuts21574 : List PrefixCut := [⟨10,47911729,47911756⟩,
⟨97,459030891,459031149⟩,
⟨128,600871934,600872275⟩]
theorem checked21574 : checkPrefixCuts (2^48) 2831679489 9 Manual.Count131072.C021574.packed 128 cuts21574 = true := by
 decide +kernel
def pointBounds21574 : List (Nat × Nat × Nat) := [(2831689728,101000896122067,101001277061497),(2831778816,101001307241229,101001688180890)]
theorem point_links_checked21574 : (cuts21574.take 2).map (fun c => (2831679489-1+2*2^9*c.k,101000848210338+c.lower,101001229149741+c.upper)) = pointBounds21574 := by
 decide +kernel
def cuts21575 : List PrefixCut := [⟨56,262307384,262307536⟩,
⟨128,601837975,601838323⟩]
theorem checked21575 : checkPrefixCuts (2^48) 2831810561 9 Manual.Count131072.C021575.packed 128 cuts21575 = true := by
 decide +kernel
def pointBounds21575 : List (Nat × Nat × Nat) := [(2831867904,101001711389656,101002092329552)]
theorem point_links_checked21575 : (cuts21575.take 1).map (fun c => (2831810561-1+2*2^9*c.k,101001449082272+c.lower,101001830022016+c.upper)) = pointBounds21575 := by
 decide +kernel
def cuts21576 : List PrefixCut := [⟨15,69674239,69674279⟩,
⟨102,471610562,471610831⟩,
⟨128,592169139,592169477⟩]
theorem checked21576 : checkPrefixCuts (2^48) 2831941633 9 Manual.Count131072.C021576.packed 128 cuts21576 = true := by
 decide +kernel
def pointBounds21576 : List (Nat × Nat × Nat) := [(2831956992,101002120594486,101002501534618),(2832046080,101002522530809,101002903471170)]
theorem point_links_checked21576 : (cuts21576.take 2).map (fun c => (2831941633-1+2*2^9*c.k,101002050920247+c.lower,101002431860339+c.upper)) = pointBounds21576 := by
 decide +kernel
def cuts21577 : List PrefixCut := [⟨61,283849842,283850004⟩,
⟨128,595322141,595322482⟩]
theorem checked21577 : checkPrefixCuts (2^48) 2832072705 9 Manual.Count131072.C021577.packed 128 cuts21577 = true := by
 decide +kernel
def pointBounds21577 : List (Nat × Nat × Nat) := [(2832135168,101002926939228,101003307879820)]
theorem point_links_checked21577 : (cuts21577.take 1).map (fun c => (2832072705-1+2*2^9*c.k,101002643089386+c.lower,101003024029816+c.upper)) = pointBounds21577 := by
 decide +kernel
def cuts21578 : List PrefixCut := [⟨20,94612941,94612994⟩,
⟨107,498797149,498797434⟩,
⟨128,598375391,598375731⟩]
theorem checked21578 : checkPrefixCuts (2^48) 2832203777 9 Manual.Count131072.C021578.packed 128 cuts21578 = true := by
 decide +kernel
def pointBounds21578 : List (Nat × Nat × Nat) := [(2832224256,101003333024468,101003713965292),(2832313344,101003737208676,101004118149732)]
theorem point_links_checked21578 : (cuts21578.take 2).map (fun c => (2832203777-1+2*2^9*c.k,101003238411527+c.lower,101003619352298+c.upper)) = pointBounds21578 := by
 decide +kernel
def cuts21579 : List PrefixCut := [⟨66,305487753,305487930⟩,
⟨128,594670763,594671107⟩]
theorem checked21579 : checkPrefixCuts (2^48) 2832334849 9 Manual.Count131072.C021579.packed 128 cuts21579 = true := by
 decide +kernel
def pointBounds21579 : List (Nat × Nat × Nat) := [(2832402432,101004142274671,101004523215959)]
theorem point_links_checked21579 : (cuts21579.take 1).map (fun c => (2832334849-1+2*2^9*c.k,101003836786918+c.lower,101004217728029+c.upper)) = pointBounds21579 := by
 decide +kernel
def cuts21580 : List PrefixCut := [⟨25,117559504,117559573⟩,
⟨112,527568545,527568850⟩,
⟨128,600009420,600009765⟩]
theorem checked21580 : checkPrefixCuts (2^48) 2832465921 9 Manual.Count131072.C021580.packed 128 cuts21580 = true := by
 decide +kernel
def pointBounds21580 : List (Nat × Nat × Nat) := [(2832491520,101004549017185,101004929958709),(2832580608,101004959026226,101005339967986)]
theorem point_links_checked21580 : (cuts21580.take 2).map (fun c => (2832465921-1+2*2^9*c.k,101004431457681+c.lower,101004812399136+c.upper)) = pointBounds21580 := by
 decide +kernel
def cuts21581 : List PrefixCut := [⟨71,332884881,332885064⟩,
⟨128,598093626,598093966⟩]
theorem checked21581 : checkPrefixCuts (2^48) 2832596993 9 Manual.Count131072.C021581.packed 128 cuts21581 = true := by
 decide +kernel
def pointBounds21581 : List (Nat × Nat × Nat) := [(2832669696,101005364351982,101005745293965)]
theorem point_links_checked21581 : (cuts21581.take 1).map (fun c => (2832596993-1+2*2^9*c.k,101005031467101+c.lower,101005412408901+c.upper)) = pointBounds21581 := by
 decide +kernel
def cuts21582 : List PrefixCut := [⟨30,139210042,139210125⟩,
⟨117,542523075,542523388⟩,
⟨128,593594581,593594924⟩]
theorem checked21582 : checkPrefixCuts (2^48) 2832728065 9 Manual.Count131072.C021582.packed 128 cuts21582 = true := by
 decide +kernel
def pointBounds21582 : List (Nat × Nat × Nat) := [(2832758784,101005768770769,101006149712992),(2832847872,101006172083802,101006553026255)]
theorem point_links_checked21582 : (cuts21582.take 2).map (fun c => (2832728065-1+2*2^9*c.k,101005629560727+c.lower,101006010502867+c.upper)) = pointBounds21582 := by
 decide +kernel
def cuts21583 : List PrefixCut := [⟨76,350142282,350142486⟩,
⟨128,594659953,594660297⟩]
theorem checked21583 : checkPrefixCuts (2^48) 2832859137 9 Manual.Count131072.C021583.packed 128 cuts21583 = true := by
 decide +kernel
def pointBounds21583 : List (Nat × Nat × Nat) := [(2832936960,101006573297590,101006954240277)]
theorem point_links_checked21583 : (cuts21583.take 1).map (fun c => (2832859137-1+2*2^9*c.k,101006223155308+c.lower,101006604097791+c.upper)) = pointBounds21583 := by
 decide +kernel
def cuts21584 : List PrefixCut := [⟨35,165526241,165526336⟩,
⟨122,568999934,569000261⟩,
⟨128,597017092,597017434⟩]
theorem checked21584 : checkPrefixCuts (2^48) 2832990209 9 Manual.Count131072.C021584.packed 128 cuts21584 = true := by
 decide +kernel
def pointBounds21584 : List (Nat × Nat × Nat) := [(2833026048,101006983341502,101007364284424),(2833115136,101007386815195,101007767758349)]
theorem point_links_checked21584 : (cuts21584.take 2).map (fun c => (2832990209-1+2*2^9*c.k,101006817815261+c.lower,101007198758088+c.upper)) = pointBounds21584 := by
 decide +kernel
def cuts21585 : List PrefixCut := [⟨81,386372344,386372570⟩,
⟨128,606825036,606825389⟩]
theorem checked21585 : checkPrefixCuts (2^48) 2833121281 9 Manual.Count131072.C021585.packed 128 cuts21585 = true := by
 decide +kernel
def pointBounds21585 : List (Nat × Nat × Nat) := [(2833204224,101007801204697,101008182148092)]
theorem point_links_checked21585 : (cuts21585.take 1).map (fun c => (2833121281-1+2*2^9*c.k,101007414832353+c.lower,101007795775522+c.upper)) = pointBounds21585 := by
 decide +kernel
def cuts21586 : List PrefixCut := [⟨40,183790459,183790567⟩,
⟨127,591795956,591796288⟩,
⟨128,596465046,596465381⟩]
theorem checked21586 : checkPrefixCuts (2^48) 2833252353 9 Manual.Count131072.C021586.packed 128 cuts21586 = true := by
 decide +kernel
def pointBounds21586 : List (Nat × Nat × Nat) := [(2833293312,101008205447848,101008586391478),(2833382400,101008613453345,101008994397199)]
theorem point_links_checked21586 : (cuts21586.take 2).map (fun c => (2833252353-1+2*2^9*c.k,101008021657389+c.lower,101008402600911+c.upper)) = pointBounds21586 := by
 decide +kernel
def cuts21587 : List PrefixCut := [⟨86,400542033,400542266⟩,
⟨128,600609716,600610064⟩]
theorem checked21587 : checkPrefixCuts (2^48) 2833383425 9 Manual.Count131072.C021587.packed 128 cuts21587 = true := by
 decide +kernel
def pointBounds21587 : List (Nat × Nat × Nat) := [(2833471488,101009018664468,101009399608558)]
theorem point_links_checked21587 : (cuts21587.take 1).map (fun c => (2833383425-1+2*2^9*c.k,101008618122435+c.lower,101008999066292+c.upper)) = pointBounds21587 := by
 decide +kernel
def cuts21588 : List PrefixCut := [⟨45,214965086,214965211⟩,
⟨128,597304029,597304374⟩]
theorem checked21588 : checkPrefixCuts (2^48) 2833514497 9 Manual.Count131072.C021588.packed 128 cuts21588 = true := by
 decide +kernel
def pointBounds21588 : List (Nat × Nat × Nat) := [(2833560576,101009433697237,101009814641567)]
theorem point_links_checked21588 : (cuts21588.take 1).map (fun c => (2833514497-1+2*2^9*c.k,101009218732151+c.lower,101009599676356+c.upper)) = pointBounds21588 := by
 decide +kernel
def cuts21589 : List PrefixCut := [⟨4,17383285,17383297⟩,
⟨91,416099657,416099900⟩,
⟨128,587045216,587045559⟩]
theorem checked21589 : checkPrefixCuts (2^48) 2833645569 9 Manual.Count131072.C021589.packed 128 cuts21589 = true := by
 decide +kernel
def pointBounds21589 : List (Nat × Nat × Nat) := [(2833649664,101009833419465,101010214364027),(2833738752,101010232135837,101010613080630)]
theorem point_links_checked21589 : (cuts21589.take 2).map (fun c => (2833645569-1+2*2^9*c.k,101009816036180+c.lower,101010196980730+c.upper)) = pointBounds21589 := by
 decide +kernel
def cuts21590 : List PrefixCut := [⟨50,235207861,235208000⟩,
⟨128,597944039,597944391⟩]
theorem checked21590 : checkPrefixCuts (2^48) 2833776641 9 Manual.Count131072.C021590.packed 128 cuts21590 = true := by
 decide +kernel
def pointBounds21590 : List (Nat × Nat × Nat) := [(2833827840,101010638289257,101011019234289)]
theorem point_links_checked21590 : (cuts21590.take 1).map (fun c => (2833776641-1+2*2^9*c.k,101010403081396+c.lower,101010784026289+c.upper)) = pointBounds21590 := by
 decide +kernel
def cuts21591 : List PrefixCut := [⟨9,43404494,43404519⟩,
⟨96,451916135,451916396⟩,
⟨128,603776309,603776656⟩]
theorem checked21591 : checkPrefixCuts (2^48) 2833907713 9 Manual.Count131072.C021591.packed 128 cuts21591 = true := by
 decide +kernel
def pointBounds21591 : List (Nat × Nat × Nat) := [(2833916928,101011044429929,101011425375199),(2834006016,101011452941570,101011833887076)]
theorem point_links_checked21591 : (cuts21591.take 2).map (fun c => (2833907713-1+2*2^9*c.k,101011001025435+c.lower,101011381970680+c.upper)) = pointBounds21591 := by
 decide +kernel
def cuts21592 : List PrefixCut := [⟨55,259121613,259121764⟩,
⟨128,601563376,601563730⟩]
theorem checked21592 : checkPrefixCuts (2^48) 2834038785 9 Manual.Count131072.C021592.packed 128 cuts21592 = true := by
 decide +kernel
def pointBounds21592 : List (Nat × Nat × Nat) := [(2834095104,101011863923357,101012244869100)]
theorem point_links_checked21592 : (cuts21592.take 1).map (fun c => (2834038785-1+2*2^9*c.k,101011604801744+c.lower,101011985747336+c.upper)) = pointBounds21592 := by
 decide +kernel
def cuts21593 : List PrefixCut := [⟨14,66739349,66739388⟩,
⟨101,471736496,471736772⟩,
⟨128,602131361,602131713⟩]
theorem checked21593 : checkPrefixCuts (2^48) 2834169857 9 Manual.Count131072.C021593.packed 128 cuts21593 = true := by
 decide +kernel
def pointBounds21593 : List (Nat × Nat × Nat) := [(2834184192,101012273104469,101012654050454),(2834273280,101012678101616,101013059047838)]
theorem point_links_checked21593 : (cuts21593.take 2).map (fun c => (2834169857-1+2*2^9*c.k,101012206365120+c.lower,101012587311066+c.upper)) = pointBounds21593 := by
 decide +kernel
def cuts21594 : List PrefixCut := [⟨60,278561969,278562126⟩,
⟨128,595449933,595450274⟩]
theorem checked21594 : checkPrefixCuts (2^48) 2834300929 9 Manual.Count131072.C021594.packed 128 cuts21594 = true := by
 decide +kernel
def pointBounds21594 : List (Nat × Nat × Nat) := [(2834362368,101013087058450,101013468004905)]
theorem point_links_checked21594 : (cuts21594.take 1).map (fun c => (2834300929-1+2*2^9*c.k,101012808496481+c.lower,101013189442779+c.upper)) = pointBounds21594 := by
 decide +kernel
def cuts21595 : List PrefixCut := [⟨19,87487907,87487956⟩,
⟨106,493241313,493241603⟩,
⟨128,592145477,592145823⟩]
theorem checked21595 : checkPrefixCuts (2^48) 2834432001 9 Manual.Count131072.C021595.packed 128 cuts21595 = true := by
 decide +kernel
def pointBounds21595 : List (Nat × Nat × Nat) := [(2834451456,101013491434321,101013872381009),(2834540544,101013897187727,101014278134656)]
theorem point_links_checked21595 : (cuts21595.take 2).map (fun c => (2834432001-1+2*2^9*c.k,101013403946414+c.lower,101013784893053+c.upper)) = pointBounds21595 := by
 decide +kernel
def cuts21596 : List PrefixCut := [⟨65,305644855,305645025⟩,
⟨128,602743005,602743344⟩]
theorem checked21596 : checkPrefixCuts (2^48) 2834563073 9 Manual.Count131072.C021596.packed 128 cuts21596 = true := by
 decide +kernel
def pointBounds21596 : List (Nat × Nat × Nat) := [(2834629632,101014301736746,101014682683901)]
theorem point_links_checked21596 : (cuts21596.take 1).map (fun c => (2834563073-1+2*2^9*c.k,101013996091891+c.lower,101014377038876+c.upper)) = pointBounds21596 := by
 decide +kernel
def cuts21597 : List PrefixCut := [⟨24,111112174,111112237⟩,
⟨111,520699805,520700097⟩,
⟨128,599537739,599538075⟩]
theorem checked21597 : checkPrefixCuts (2^48) 2834694145 9 Manual.Count131072.C021597.packed 128 cuts21597 = true := by
 decide +kernel
def pointBounds21597 : List (Nat × Nat × Nat) := [(2834718720,101014709947070,101015090894457),(2834807808,101015119534701,101015500482317)]
theorem point_links_checked21597 : (cuts21597.take 2).map (fun c => (2834694145-1+2*2^9*c.k,101014598834896+c.lower,101014979782220+c.upper)) = pointBounds21597 := by
 decide +kernel
def cuts21598 : List PrefixCut := [⟨70,327162364,327162553⟩,
⟨128,600502898,600503244⟩]
theorem checked21598 : checkPrefixCuts (2^48) 2834825217 9 Manual.Count131072.C021598.packed 128 cuts21598 = true := by
 decide +kernel
def pointBounds21598 : List (Nat × Nat × Nat) := [(2834896896,101015525534999,101015906482848)]
theorem point_links_checked21598 : (cuts21598.take 1).map (fun c => (2834825217-1+2*2^9*c.k,101015198372635+c.lower,101015579320295+c.upper)) = pointBounds21598 := by
 decide +kernel
def cuts21599 : List PrefixCut := [⟨29,135327761,135327835⟩,
⟨116,540607523,540607831⟩,
⟨128,596702324,596702663⟩]
theorem checked21599 : checkPrefixCuts (2^48) 2834956289 9 Manual.Count131072.C021599.packed 128 cuts21599 = true := by
 decide +kernel
def pointBounds21599 : List (Nat × Nat × Nat) := [(2834985984,101015934203294,101016315151374),(2835075072,101016339483056,101016720431370)]
theorem point_links_checked21599 : (cuts21599.take 2).map (fun c => (2834956289-1+2*2^9*c.k,101015798875533+c.lower,101016179823539+c.upper)) = pointBounds21599 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000049
