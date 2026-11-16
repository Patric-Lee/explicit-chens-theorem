import PlattAssemblyKernel
import PlattCertificates.Count131072.C023648
import PlattCertificates.Count131072.C023649
import PlattCertificates.Count131072.C023650
import PlattCertificates.Count131072.C023651
import PlattCertificates.Count131072.C023652
import PlattCertificates.Count131072.C023653
import PlattCertificates.Count131072.C023654
import PlattCertificates.Count131072.C023655
import PlattCertificates.Count131072.C023656
import PlattCertificates.Count131072.C023657
import PlattCertificates.Count131072.C023658
import PlattCertificates.Count131072.C023659
import PlattCertificates.Count131072.C023660
import PlattCertificates.Count131072.C023661
import PlattCertificates.Count131072.C023662
import PlattCertificates.Count131072.C023663
import PlattCertificates.Count131072.C023664
import PlattCertificates.Count131072.C023665
import PlattCertificates.Count131072.C023666
import PlattCertificates.Count131072.C023667
import PlattCertificates.Count131072.C023668
import PlattCertificates.Count131072.C023669
import PlattCertificates.Count131072.C023670
import PlattCertificates.Count131072.C023671
import PlattCertificates.Count131072.C023672
import PlattCertificates.Count131072.C023673
import PlattCertificates.Count131072.C023674
import PlattCertificates.Count131072.C023675
import PlattCertificates.Count131072.C023676
import PlattCertificates.Count131072.C023677
import PlattCertificates.Count131072.C023678
import PlattCertificates.Count131072.C023679
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000114
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23648 : List PrefixCut := [⟨64,273171307,273171462⟩,
⟨128,548513449,548513760⟩]
theorem checked23648 : checkPrefixCuts (2^48) 3103522817 9 Manual.Count131072.C023648.packed 128 cuts23648 = true := by
 decide +kernel
def pointBounds23648 : List (Nat × Nat × Nat) := [(3103588352,102184060370631,102184441984800)]
theorem point_links_checked23648 : (cuts23648.take 1).map (fun c => (3103522817-1+2*2^9*c.k,102183787199324+c.lower,102184168813338+c.upper)) = pointBounds23648 := by
 decide +kernel
def cuts23649 : List PrefixCut := [⟨31,134313370,134313443⟩,
⟨126,537426495,537426802⟩,
⟨128,546404574,546404885⟩]
theorem checked23649 : checkPrefixCuts (2^48) 3103653889 9 Manual.Count131072.C023649.packed 128 cuts23649 = true := by
 decide +kernel
def pointBounds23649 : List (Nat × Nat × Nat) := [(3103685632,102184470026143,102184851640541),(3103782912,102184873139268,102185254753900)]
theorem point_links_checked23649 : (cuts23649.take 2).map (fun c => (3103653889-1+2*2^9*c.k,102184335712773+c.lower,102184717327098+c.upper)) = pointBounds23649 := by
 decide +kernel
def cuts23650 : List PrefixCut := [⟨93,397205743,397205971⟩,
⟨128,546653520,546653827⟩]
theorem checked23650 : checkPrefixCuts (2^48) 3103784961 9 Manual.Count131072.C023650.packed 128 cuts23650 = true := by
 decide +kernel
def pointBounds23650 : List (Nat × Nat × Nat) := [(3103880192,102185279323090,102185660937954)]
theorem point_links_checked23650 : (cuts23650.take 1).map (fun c => (3103784961-1+2*2^9*c.k,102184882117347+c.lower,102185263731983+c.upper)) = pointBounds23650 := by
 decide +kernel
def cuts23651 : List PrefixCut := [⟨60,261529506,261529655⟩,
⟨128,543003324,543003638⟩]
theorem checked23651 : checkPrefixCuts (2^48) 3103916033 9 Manual.Count131072.C023651.packed 128 cuts23651 = true := by
 decide +kernel
def pointBounds23651 : List (Nat × Nat × Nat) := [(3103977472,102185690300373,102186071915465)]
theorem point_links_checked23651 : (cuts23651.take 1).map (fun c => (3103916033-1+2*2^9*c.k,102185428770867+c.lower,102185810385810+c.upper)) = pointBounds23651 := by
 decide +kernel
def cuts23652 : List PrefixCut := [⟨27,115344411,115344476⟩,
⟨122,514870523,514870804⟩,
⟨128,541801365,541801660⟩]
theorem checked23652 : checkPrefixCuts (2^48) 3104047105 9 Manual.Count131072.C023652.packed 128 cuts23652 = true := by
 decide +kernel
def pointBounds23652 : List (Nat × Nat × Nat) := [(3104074752,102186087118602,102186468733924),(3104172032,102186486644714,102186868260252)]
theorem point_links_checked23652 : (cuts23652.take 2).map (fun c => (3104047105-1+2*2^9*c.k,102185971774191+c.lower,102186353389448+c.upper)) = pointBounds23652 := by
 decide +kernel
def cuts23653 : List PrefixCut := [⟨89,377025867,377026080⟩,
⟨128,540962461,540962766⟩]
theorem checked23653 : checkPrefixCuts (2^48) 3104178177 9 Manual.Count131072.C023653.packed 128 cuts23653 = true := by
 decide +kernel
def pointBounds23653 : List (Nat × Nat × Nat) := [(3104269312,102186890601423,102187272217188)]
theorem point_links_checked23653 : (cuts23653.take 1).map (fun c => (3104178177-1+2*2^9*c.k,102186513575556+c.lower,102186895191108+c.upper)) = pointBounds23653 := by
 decide +kernel
def cuts23654 : List PrefixCut := [⟨56,239735343,239735478⟩,
⟨128,536950125,536950437⟩]
theorem checked23654 : checkPrefixCuts (2^48) 3104309249 9 Manual.Count131072.C023654.packed 128 cuts23654 = true := by
 decide +kernel
def pointBounds23654 : List (Nat × Nat × Nat) := [(3104366592,102187294273360,102187675889352)]
theorem point_links_checked23654 : (cuts23654.take 1).map (fun c => (3104309249-1+2*2^9*c.k,102187054538017+c.lower,102187436153874+c.upper)) = pointBounds23654 := by
 decide +kernel
def cuts23655 : List PrefixCut := [⟨23,99734954,99735013⟩,
⟨118,499392365,499392646⟩,
⟨128,541551502,541551806⟩]
theorem checked23655 : checkPrefixCuts (2^48) 3104440321 9 Manual.Count131072.C023655.packed 128 cuts23655 = true := by
 decide +kernel
def pointBounds23655 : List (Nat × Nat × Nat) := [(3104463872,102187691223096,102188072839324),(3104561152,102188090880507,102188472496957)]
theorem point_links_checked23655 : (cuts23655.take 2).map (fun c => (3104440321-1+2*2^9*c.k,102187591488142+c.lower,102187973104311+c.upper)) = pointBounds23655 := by
 decide +kernel
def cuts23656 : List PrefixCut := [⟨85,361746913,361747118⟩,
⟨128,547512255,547512569⟩]
theorem checked23656 : checkPrefixCuts (2^48) 3104571393 9 Manual.Count131072.C023656.packed 128 cuts23656 = true := by
 decide +kernel
def pointBounds23656 : List (Nat × Nat × Nat) := [(3104658432,102188494786557,102188876403235)]
theorem point_links_checked23656 : (cuts23656.take 1).map (fun c => (3104571393-1+2*2^9*c.k,102188133039644+c.lower,102188514656117+c.upper)) = pointBounds23656 := by
 decide +kernel
def cuts23657 : List PrefixCut := [⟨52,218944008,218944134⟩,
⟨128,542956197,542956508⟩]
theorem checked23657 : checkPrefixCuts (2^48) 3104702465 9 Manual.Count131072.C023657.packed 128 cuts23657 = true := by
 decide +kernel
def pointBounds23657 : List (Nat × Nat × Nat) := [(3104755712,102188899495907,102189281112820)]
theorem point_links_checked23657 : (cuts23657.take 1).map (fun c => (3104702465-1+2*2^9*c.k,102188680551899+c.lower,102189062168686+c.upper)) = pointBounds23657 := by
 decide +kernel
def cuts23658 : List PrefixCut := [⟨19,84129441,84129484⟩,
⟨114,489810645,489810920⟩,
⟨128,550820372,550820678⟩]
theorem checked23658 : checkPrefixCuts (2^48) 3104833537 9 Manual.Count131072.C023658.packed 128 cuts23658 = true := by
 decide +kernel
def pointBounds23658 : List (Nat × Nat × Nat) := [(3104852992,102189307637537,102189689254678),(3104950272,102189713318741,102190094936114)]
theorem point_links_checked23658 : (cuts23658.take 2).map (fun c => (3104833537-1+2*2^9*c.k,102189223508096+c.lower,102189605125194+c.upper)) = pointBounds23658 := by
 decide +kernel
def cuts23659 : List PrefixCut := [⟨81,343298988,343299179⟩,
⟨128,543182339,543182640⟩]
theorem checked23659 : checkPrefixCuts (2^48) 3104964609 9 Manual.Count131072.C023659.packed 128 cuts23659 = true := by
 decide +kernel
def pointBounds23659 : List (Nat × Nat × Nat) := [(3105047552,102190117627456,102190499245051)]
theorem point_links_checked23659 : (cuts23659.take 1).map (fun c => (3104964609-1+2*2^9*c.k,102189774328468+c.lower,102190155945872+c.upper)) = pointBounds23659 := by
 decide +kernel
def cuts23660 : List PrefixCut := [⟨48,198883116,198883227⟩,
⟨128,535001114,535001414⟩]
theorem checked23660 : checkPrefixCuts (2^48) 3105095681 9 Manual.Count131072.C023660.packed 128 cuts23660 = true := by
 decide +kernel
def pointBounds23660 : List (Nat × Nat × Nat) := [(3105144832,102190516393923,102190898011739)]
theorem point_links_checked23660 : (cuts23660.take 1).map (fun c => (3105095681-1+2*2^9*c.k,102190317510807+c.lower,102190699128512+c.upper)) = pointBounds23660 := by
 decide +kernel
def cuts23661 : List PrefixCut := [⟨15,62635902,62635935⟩,
⟨110,465456313,465456576⟩,
⟨128,538876300,538876606⟩]
theorem checked23661 : checkPrefixCuts (2^48) 3105226753 9 Manual.Count131072.C023661.packed 128 cuts23661 = true := by
 decide +kernel
def pointBounds23661 : List (Nat × Nat × Nat) := [(3105242112,102190915147823,102191296765861),(3105339392,102191317968234,102191699586502)]
theorem point_links_checked23661 : (cuts23661.take 2).map (fun c => (3105226753-1+2*2^9*c.k,102190852511921+c.lower,102191234129926+c.upper)) = pointBounds23661 := by
 decide +kernel
def cuts23662 : List PrefixCut := [⟨77,333375896,333376081⟩,
⟨128,546376663,546376972⟩]
theorem checked23662 : checkPrefixCuts (2^48) 3105357825 9 Manual.Count131072.C023662.packed 128 cuts23662 = true := by
 decide +kernel
def pointBounds23662 : List (Nat × Nat × Nat) := [(3105436672,102191724764117,102192106382613)]
theorem point_links_checked23662 : (cuts23662.take 1).map (fun c => (3105357825-1+2*2^9*c.k,102191391388221+c.lower,102191773006532+c.upper)) = pointBounds23662 := by
 decide +kernel
def cuts23663 : List PrefixCut := [⟨44,183449704,183449809⟩,
⟨128,541096594,541096896⟩]
theorem checked23663 : checkPrefixCuts (2^48) 3105488897 9 Manual.Count131072.C023663.packed 128 cuts23663 = true := by
 decide +kernel
def pointBounds23663 : List (Nat × Nat × Nat) := [(3105533952,102192121214588,102192502833313)]
theorem point_links_checked23663 : (cuts23663.take 1).map (fun c => (3105488897-1+2*2^9*c.k,102191937764884+c.lower,102192319383504+c.upper)) = pointBounds23663 := by
 decide +kernel
def cuts23664 : List PrefixCut := [⟨11,45226308,45226333⟩,
⟨106,452709107,452709357⟩,
⟨128,544970998,544971302⟩]
theorem checked23664 : checkPrefixCuts (2^48) 3105619969 9 Manual.Count131072.C023664.packed 128 cuts23664 = true := by
 decide +kernel
def pointBounds23664 : List (Nat × Nat × Nat) := [(3105631232,102192524087786,102192905706733),(3105728512,102192931570585,102193313189757)]
theorem point_links_checked23664 : (cuts23664.take 2).map (fun c => (3105619969-1+2*2^9*c.k,102192478861478+c.lower,102192860480400+c.upper)) = pointBounds23664 := by
 decide +kernel
def cuts23665 : List PrefixCut := [⟨73,307957746,307957923⟩,
⟨128,539419672,539419981⟩]
theorem checked23665 : checkPrefixCuts (2^48) 3105751041 9 Manual.Count131072.C023665.packed 128 cuts23665 = true := by
 decide +kernel
def pointBounds23665 : List (Nat × Nat × Nat) := [(3105825792,102193331790222,102193713409625)]
theorem point_links_checked23665 : (cuts23665.take 1).map (fun c => (3105751041-1+2*2^9*c.k,102193023832476+c.lower,102193405451702+c.upper)) = pointBounds23665 := by
 decide +kernel
def cuts23666 : List PrefixCut := [⟨40,172460892,172460991⟩,
⟨128,549728082,549728394⟩]
theorem checked23666 : checkPrefixCuts (2^48) 3105882113 9 Manual.Count131072.C023666.packed 128 cuts23666 = true := by
 decide +kernel
def pointBounds23666 : List (Nat × Nat × Nat) := [(3105923072,102193735713040,102194117332674)]
theorem point_links_checked23666 : (cuts23666.take 1).map (fun c => (3105882113-1+2*2^9*c.k,102193563252148+c.lower,102193944871683+c.upper)) = pointBounds23666 := by
 decide +kernel
def cuts23667 : List PrefixCut := [⟨7,29452302,29452320⟩,
⟨102,432443646,432443891⟩,
⟨128,542545896,542546205⟩]
theorem checked23667 : checkPrefixCuts (2^48) 3106013185 9 Manual.Count131072.C023667.packed 128 cuts23667 = true := by
 decide +kernel
def pointBounds23667 : List (Nat × Nat × Nat) := [(3106020352,102194142432532,102194524052397),(3106117632,102194545423876,102194927043968)]
theorem point_links_checked23667 : (cuts23667.take 2).map (fun c => (3106013185-1+2*2^9*c.k,102194112980230+c.lower,102194494600077+c.upper)) = pointBounds23667 := by
 decide +kernel
def cuts23668 : List PrefixCut := [⟨69,298494712,298494882⟩,
⟨128,547960004,547960307⟩]
theorem checked23668 : checkPrefixCuts (2^48) 3106144257 9 Manual.Count131072.C023668.packed 128 cuts23668 = true := by
 decide +kernel
def pointBounds23668 : List (Nat × Nat × Nat) := [(3106214912,102194954020838,102195335641164)]
theorem point_links_checked23668 : (cuts23668.take 1).map (fun c => (3106144257-1+2*2^9*c.k,102194655526126+c.lower,102195037146282+c.upper)) = pointBounds23668 := by
 decide +kernel
def cuts23669 : List PrefixCut := [⟨36,153591371,153591458⟩,
⟨128,540325381,540325691⟩]
theorem checked23669 : checkPrefixCuts (2^48) 3106275329 9 Manual.Count131072.C023669.packed 128 cuts23669 = true := by
 decide +kernel
def pointBounds23669 : List (Nat × Nat × Nat) := [(3106312192,102195357077501,102195738698047)]
theorem point_links_checked23669 : (cuts23669.take 1).map (fun c => (3106275329-1+2*2^9*c.k,102195203486130+c.lower,102195585106589+c.upper)) = pointBounds23669 := by
 decide +kernel
def cuts23670 : List PrefixCut := [⟨3,13410436,13410444⟩,
⟨98,422603316,422603551⟩,
⟨128,547007709,547008014⟩]
theorem checked23670 : checkPrefixCuts (2^48) 3106406401 9 Manual.Count131072.C023670.packed 128 cuts23670 = true := by
 decide +kernel
def pointBounds23670 : List (Nat × Nat × Nat) := [(3106409472,102195757221947,102196138842724),(3106506752,102196166414827,102196548035831)]
theorem point_links_checked23670 : (cuts23670.take 2).map (fun c => (3106406401-1+2*2^9*c.k,102195743811511+c.lower,102196125432280+c.upper)) = pointBounds23670 := by
 decide +kernel
def cuts23671 : List PrefixCut := [⟨65,280788957,280789117⟩,
⟨128,544447757,544448066⟩]
theorem checked23671 : checkPrefixCuts (2^48) 3106537473 9 Manual.Count131072.C023671.packed 128 cuts23671 = true := by
 decide +kernel
def pointBounds23671 : List (Nat × Nat × Nat) := [(3106604032,102196571608177,102196953229411)]
theorem point_links_checked23671 : (cuts23671.take 1).map (fun c => (3106537473-1+2*2^9*c.k,102196290819220+c.lower,102196672440294+c.upper)) = pointBounds23671 := by
 decide +kernel
def cuts23672 : List PrefixCut := [⟨32,134817203,134817279⟩,
⟨127,538897979,538898282⟩,
⟨128,543427961,543428267⟩]
theorem checked23672 : checkPrefixCuts (2^48) 3106668545 9 Manual.Count131072.C023672.packed 128 cuts23672 = true := by
 decide +kernel
def pointBounds23672 : List (Nat × Nat × Nat) := [(3106701312,102196970084180,102197351705639),(3106798592,102197374164956,102197755786642)]
theorem point_links_checked23672 : (cuts23672.take 2).map (fun c => (3106668545-1+2*2^9*c.k,102196835266977+c.lower,102197216888360+c.upper)) = pointBounds23672 := by
 decide +kernel
def cuts23673 : List PrefixCut := [⟨94,402074933,402075151⟩,
⟨128,544945335,544945630⟩]
theorem checked23673 : checkPrefixCuts (2^48) 3106799617 9 Manual.Count131072.C023673.packed 128 cuts23673 = true := by
 decide +kernel
def pointBounds23673 : List (Nat × Nat × Nat) := [(3106895872,102197780769871,102198162391778)]
theorem point_links_checked23673 : (cuts23673.take 1).map (fun c => (3106799617-1+2*2^9*c.k,102197378694938+c.lower,102197760316627+c.upper)) = pointBounds23673 := by
 decide +kernel
def cuts23674 : List PrefixCut := [⟨61,259191990,259192137⟩,
⟨128,546824739,546825047⟩]
theorem checked23674 : checkPrefixCuts (2^48) 3106930689 9 Manual.Count131072.C023674.packed 128 cuts23674 = true := by
 decide +kernel
def pointBounds23674 : List (Nat × Nat × Nat) := [(3106993152,102198182832263,102198564454394)]
theorem point_links_checked23674 : (cuts23674.take 1).map (fun c => (3106930689-1+2*2^9*c.k,102197923640273+c.lower,102198305262257+c.upper)) = pointBounds23674 := by
 decide +kernel
def cuts23675 : List PrefixCut := [⟨28,119762053,119762120⟩,
⟨123,518628606,518628903⟩,
⟨128,540007429,540007739⟩]
theorem checked23675 : checkPrefixCuts (2^48) 3107061761 9 Manual.Count131072.C023675.packed 128 cuts23675 = true := by
 decide +kernel
def pointBounds23675 : List (Nat × Nat × Nat) := [(3107090432,102198590227065,102198971849424),(3107187712,102198989093618,102199370716207)]
theorem point_links_checked23675 : (cuts23675.take 2).map (fun c => (3107061761-1+2*2^9*c.k,102198470465012+c.lower,102198852087304+c.upper)) = pointBounds23675 := by
 decide +kernel
def cuts23676 : List PrefixCut := [⟨90,378199906,378200118⟩,
⟨128,542520919,542521226⟩]
theorem checked23676 : checkPrefixCuts (2^48) 3107192833 9 Manual.Count131072.C023676.packed 128 cuts23676 = true := by
 decide +kernel
def pointBounds23676 : List (Nat × Nat × Nat) := [(3107284992,102199388672347,102199770295161)]
theorem point_links_checked23676 : (cuts23676.take 1).map (fun c => (3107192833-1+2*2^9*c.k,102199010472441+c.lower,102199392095043+c.upper)) = pointBounds23676 := by
 decide +kernel
def cuts23677 : List PrefixCut := [⟨57,244213096,244213236⟩,
⟨128,544490972,544491280⟩]
theorem checked23677 : checkPrefixCuts (2^48) 3107323905 9 Manual.Count131072.C023677.packed 128 cuts23677 = true := by
 decide +kernel
def pointBounds23677 : List (Nat × Nat × Nat) := [(3107382272,102199797206456,102200178829505)]
theorem point_links_checked23677 : (cuts23677.take 1).map (fun c => (3107323905-1+2*2^9*c.k,102199552993360+c.lower,102199934616269+c.upper)) = pointBounds23677 := by
 decide +kernel
def cuts23678 : List PrefixCut := [⟨24,102808489,102808545⟩,
⟨119,512766319,512766606⟩,
⟨128,552710706,552711014⟩]
theorem checked23678 : checkPrefixCuts (2^48) 3107454977 9 Manual.Count131072.C023678.packed 128 cuts23678 = true := by
 decide +kernel
def pointBounds23678 : List (Nat × Nat × Nat) := [(3107479552,102200200292821,102200581916094),(3107576832,102200610250651,102200991874155)]
theorem point_links_checked23678 : (cuts23678.take 2).map (fun c => (3107454977-1+2*2^9*c.k,102200097484332+c.lower,102200479107549+c.upper)) = pointBounds23678 := by
 decide +kernel
def cuts23679 : List PrefixCut := [⟨86,364747220,364747422⟩,
⟨128,540188101,540188402⟩]
theorem checked23679 : checkPrefixCuts (2^48) 3107586049 9 Manual.Count131072.C023679.packed 128 cuts23679 = true := by
 decide +kernel
def pointBounds23679 : List (Nat × Nat × Nat) := [(3107674112,102201014942258,102201396565985)]
theorem point_links_checked23679 : (cuts23679.take 1).map (fun c => (3107586049-1+2*2^9*c.k,102200650195038+c.lower,102201031818563+c.upper)) = pointBounds23679 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000114
