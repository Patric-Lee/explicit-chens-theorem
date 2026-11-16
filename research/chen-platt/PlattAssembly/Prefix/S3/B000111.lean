import PlattAssemblyKernel
import PlattCertificates.Count131072.C023552
import PlattCertificates.Count131072.C023553
import PlattCertificates.Count131072.C023554
import PlattCertificates.Count131072.C023555
import PlattCertificates.Count131072.C023556
import PlattCertificates.Count131072.C023557
import PlattCertificates.Count131072.C023558
import PlattCertificates.Count131072.C023559
import PlattCertificates.Count131072.C023560
import PlattCertificates.Count131072.C023561
import PlattCertificates.Count131072.C023562
import PlattCertificates.Count131072.C023563
import PlattCertificates.Count131072.C023564
import PlattCertificates.Count131072.C023565
import PlattCertificates.Count131072.C023566
import PlattCertificates.Count131072.C023567
import PlattCertificates.Count131072.C023568
import PlattCertificates.Count131072.C023569
import PlattCertificates.Count131072.C023570
import PlattCertificates.Count131072.C023571
import PlattCertificates.Count131072.C023572
import PlattCertificates.Count131072.C023573
import PlattCertificates.Count131072.C023574
import PlattCertificates.Count131072.C023575
import PlattCertificates.Count131072.C023576
import PlattCertificates.Count131072.C023577
import PlattCertificates.Count131072.C023578
import PlattCertificates.Count131072.C023579
import PlattCertificates.Count131072.C023580
import PlattCertificates.Count131072.C023581
import PlattCertificates.Count131072.C023582
import PlattCertificates.Count131072.C023583
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000111
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23552 : List PrefixCut := [⟨2,9106447,9106452⟩,
⟨97,408964114,408964342⟩,
⟨128,540456355,540456653⟩]
theorem checked23552 : checkPrefixCuts (2^48) 3090939905 9 Manual.Count131072.C023552.packed 128 cuts23552 = true := by
 decide +kernel
def pointBounds23552 : List (Nat × Nat × Nat) := [(3090941952,102131550481950,102131932066320),(3091039232,102131950339617,102132331924210)]
theorem point_links_checked23552 : (cuts23552.take 2).map (fun c => (3090939905-1+2*2^9*c.k,102131541375503+c.lower,102131922959868+c.upper)) = pointBounds23552 := by
 decide +kernel
def cuts23553 : List PrefixCut := [⟨64,276457174,276457328⟩,
⟨128,545532779,545533090⟩]
theorem checked23553 : checkPrefixCuts (2^48) 3091070977 9 Manual.Count131072.C023553.packed 128 cuts23553 = true := by
 decide +kernel
def pointBounds23553 : List (Nat × Nat × Nat) := [(3091136512,102132358289032,102132739873849)]
theorem point_links_checked23553 : (cuts23553.take 1).map (fun c => (3091070977-1+2*2^9*c.k,102132081831858+c.lower,102132463416521+c.upper)) = pointBounds23553 := by
 decide +kernel
def cuts23554 : List PrefixCut := [⟨31,132122720,132122794⟩,
⟨126,539591255,539591564⟩,
⟨128,546966543,546966857⟩]
theorem checked23554 : checkPrefixCuts (2^48) 3091202049 9 Manual.Count131072.C023554.packed 128 cuts23554 = true := by
 decide +kernel
def pointBounds23554 : List (Nat × Nat × Nat) := [(3091233792,102132759487357,102133141072405),(3091331072,102133166955892,102133548541175)]
theorem point_links_checked23554 : (cuts23554.take 2).map (fun c => (3091202049-1+2*2^9*c.k,102132627364637+c.lower,102133008949611+c.upper)) = pointBounds23554 := by
 decide +kernel
def cuts23555 : List PrefixCut := [⟨93,400353492,400353717⟩,
⟨128,547944869,547945181⟩]
theorem checked23555 : checkPrefixCuts (2^48) 3091333121 9 Manual.Count131072.C023555.packed 128 cuts23555 = true := by
 decide +kernel
def pointBounds23555 : List (Nat × Nat × Nat) := [(3091428352,102133574684672,102133956270185)]
theorem point_links_checked23555 : (cuts23555.take 1).map (fun c => (3091333121-1+2*2^9*c.k,102133174331180+c.lower,102133555916468+c.upper)) = pointBounds23555 := by
 decide +kernel
def cuts23556 : List PrefixCut := [⟨60,255390035,255390173⟩,
⟨128,547102147,547102451⟩]
theorem checked23556 : checkPrefixCuts (2^48) 3091464193 9 Manual.Count131072.C023556.packed 128 cuts23556 = true := by
 decide +kernel
def pointBounds23556 : List (Nat × Nat × Nat) := [(3091525632,102133977666084,102134359251822)]
theorem point_links_checked23556 : (cuts23556.take 1).map (fun c => (3091464193-1+2*2^9*c.k,102133722276049+c.lower,102134103861649+c.upper)) = pointBounds23556 := by
 decide +kernel
def cuts23557 : List PrefixCut := [⟨27,114261210,114261275⟩,
⟨122,514668109,514668405⟩,
⟨128,539249294,539249604⟩]
theorem checked23557 : checkPrefixCuts (2^48) 3091595265 9 Manual.Count131072.C023557.packed 128 cuts23557 = true := by
 decide +kernel
def pointBounds23557 : List (Nat × Nat × Nat) := [(3091622912,102134383639406,102134765225375),(3091720192,102134784046305,102135165632505)]
theorem point_links_checked23557 : (cuts23557.take 2).map (fun c => (3091595265-1+2*2^9*c.k,102134269378196+c.lower,102134650964100+c.upper)) = pointBounds23557 := by
 decide +kernel
def cuts23558 : List PrefixCut := [⟨89,376086188,376086399⟩,
⟨128,538042904,538043205⟩]
theorem checked23558 : checkPrefixCuts (2^48) 3091726337 9 Manual.Count131072.C023558.packed 128 cuts23558 = true := by
 decide +kernel
def pointBounds23558 : List (Nat × Nat × Nat) := [(3091817472,102135184713678,102135566300103)]
theorem point_links_checked23558 : (cuts23558.take 1).map (fun c => (3091726337-1+2*2^9*c.k,102134808627490+c.lower,102135190213704+c.upper)) = pointBounds23558 := by
 decide +kernel
def cuts23559 : List PrefixCut := [⟨56,240427725,240427858⟩,
⟨128,552949884,552950198⟩]
theorem checked23559 : checkPrefixCuts (2^48) 3091857409 9 Manual.Count131072.C023559.packed 128 cuts23559 = true := by
 decide +kernel
def pointBounds23559 : List (Nat × Nat × Nat) := [(3091914752,102135587098119,102135968684767)]
theorem point_links_checked23559 : (cuts23559.take 1).map (fun c => (3091857409-1+2*2^9*c.k,102135346670394+c.lower,102135728256909+c.upper)) = pointBounds23559 := by
 decide +kernel
def cuts23560 : List PrefixCut := [⟨23,97951799,97951854⟩,
⟨118,506592166,506592447⟩,
⟨128,549103134,549103438⟩]
theorem checked23560 : checkPrefixCuts (2^48) 3091988481 9 Manual.Count131072.C023560.packed 128 cuts23560 = true := by
 decide +kernel
def pointBounds23560 : List (Nat × Nat × Nat) := [(3092012032,102135997572077,102136379158961),(3092109312,102136406212444,102136787799554)]
theorem point_links_checked23560 : (cuts23560.take 2).map (fun c => (3091988481-1+2*2^9*c.k,102135899620278+c.lower,102136281207107+c.upper)) = pointBounds23560 := by
 decide +kernel
def cuts23561 : List PrefixCut := [⟨85,361382996,361383202⟩,
⟨128,546257912,546258223⟩]
theorem checked23561 : checkPrefixCuts (2^48) 3092119553 9 Manual.Count131072.C023561.packed 128 cuts23561 = true := by
 decide +kernel
def pointBounds23561 : List (Nat × Nat × Nat) := [(3092206592,102136810106408,102137191693747)]
theorem point_links_checked23561 : (cuts23561.take 1).map (fun c => (3092119553-1+2*2^9*c.k,102136448723412+c.lower,102136830310545+c.upper)) = pointBounds23561 := by
 decide +kernel
def cuts23562 : List PrefixCut := [⟨52,221100012,221100136⟩,
⟨128,544687420,544687727⟩]
theorem checked23562 : checkPrefixCuts (2^48) 3092250625 9 Manual.Count131072.C023562.packed 128 cuts23562 = true := by
 decide +kernel
def pointBounds23562 : List (Nat × Nat × Nat) := [(3092303872,102137216081336,102137597668904)]
theorem point_links_checked23562 : (cuts23562.take 1).map (fun c => (3092250625-1+2*2^9*c.k,102136994981324+c.lower,102137376568768+c.upper)) = pointBounds23562 := by
 decide +kernel
def cuts23563 : List PrefixCut := [⟨19,79644038,79644086⟩,
⟨114,484774198,484774474⟩,
⟨128,545392447,545392758⟩]
theorem checked23563 : checkPrefixCuts (2^48) 3092381697 9 Manual.Count131072.C023563.packed 128 cuts23563 = true := by
 decide +kernel
def pointBounds23563 : List (Nat × Nat × Nat) := [(3092401152,102137619312782,102138000900581),(3092498432,102138024442942,102138406030969)]
theorem point_links_checked23563 : (cuts23563.take 2).map (fun c => (3092381697-1+2*2^9*c.k,102137539668744+c.lower,102137921256495+c.upper)) = pointBounds23563 := by
 decide +kernel
def cuts23564 : List PrefixCut := [⟨81,341677679,341677873⟩,
⟨128,538452171,538452476⟩]
theorem checked23564 : checkPrefixCuts (2^48) 3092512769 9 Manual.Count131072.C023564.packed 128 cuts23564 = true := by
 decide +kernel
def pointBounds23564 : List (Nat × Nat × Nat) := [(3092595712,102138426738870,102138808327126)]
theorem point_links_checked23564 : (cuts23564.take 1).map (fun c => (3092512769-1+2*2^9*c.k,102138085061191+c.lower,102138466649253+c.upper)) = pointBounds23564 := by
 decide +kernel
def cuts23565 : List PrefixCut := [⟨48,203597442,203597558⟩,
⟨128,547621549,547621861⟩]
theorem checked23565 : checkPrefixCuts (2^48) 3092643841 9 Manual.Count131072.C023565.packed 128 cuts23565 = true := by
 decide +kernel
def pointBounds23565 : List (Nat × Nat × Nat) := [(3092692992,102138827110804,102139208699287)]
theorem point_links_checked23565 : (cuts23565.take 1).map (fun c => (3092643841-1+2*2^9*c.k,102138623513362+c.lower,102139005101729+c.upper)) = pointBounds23565 := by
 decide +kernel
def cuts23566 : List PrefixCut := [⟨15,63980198,63980233⟩,
⟨110,470060566,470060830⟩,
⟨128,547780446,547780754⟩]
theorem checked23566 : checkPrefixCuts (2^48) 3092774913 9 Manual.Count131072.C023566.packed 128 cuts23566 = true := by
 decide +kernel
def pointBounds23566 : List (Nat × Nat × Nat) := [(3092790272,102139235115109,102139616703823),(3092887552,102139641195477,102140022784420)]
theorem point_links_checked23566 : (cuts23566.take 2).map (fun c => (3092774913-1+2*2^9*c.k,102139171134911+c.lower,102139552723590+c.upper)) = pointBounds23566 := by
 decide +kernel
def cuts23567 : List PrefixCut := [⟨77,325890530,325890720⟩,
⟨128,538292755,538293070⟩]
theorem checked23567 : checkPrefixCuts (2^48) 3092905985 9 Manual.Count131072.C023567.packed 128 cuts23567 = true := by
 decide +kernel
def pointBounds23567 : List (Nat × Nat × Nat) := [(3092984832,102140044805887,102140426395064)]
theorem point_links_checked23567 : (cuts23567.take 1).map (fun c => (3092905985-1+2*2^9*c.k,102139718915357+c.lower,102140100504344+c.upper)) = pointBounds23567 := by
 decide +kernel
def cuts23568 : List PrefixCut := [⟨44,188829337,188829444⟩,
⟨128,543092999,543093304⟩]
theorem checked23568 : checkPrefixCuts (2^48) 3093037057 9 Manual.Count131072.C023568.packed 128 cuts23568 = true := by
 decide +kernel
def pointBounds23568 : List (Nat × Nat × Nat) := [(3093082112,102140446037449,102140827626858)]
theorem point_links_checked23568 : (cuts23568.take 1).map (fun c => (3093037057-1+2*2^9*c.k,102140257208112+c.lower,102140638797414+c.upper)) = pointBounds23568 := by
 decide +kernel
def cuts23569 : List PrefixCut := [⟨11,49958308,49958334⟩,
⟨106,450072674,450072932⟩,
⟨128,541068047,541068356⟩]
theorem checked23569 : checkPrefixCuts (2^48) 3093168129 9 Manual.Count131072.C023569.packed 128 cuts23569 = true := by
 decide +kernel
def pointBounds23569 : List (Nat × Nat × Nat) := [(3093179392,102140850259419,102141231849052),(3093276672,102141250373785,102141631963650)]
theorem point_links_checked23569 : (cuts23569.take 2).map (fun c => (3093168129-1+2*2^9*c.k,102140800301111+c.lower,102141181890718+c.upper)) = pointBounds23569 := by
 decide +kernel
def cuts23570 : List PrefixCut := [⟨73,316021952,316022121⟩,
⟨128,551236302,551236602⟩]
theorem checked23570 : checkPrefixCuts (2^48) 3093299201 9 Manual.Count131072.C023570.packed 128 cuts23570 = true := by
 decide +kernel
def pointBounds23570 : List (Nat × Nat × Nat) := [(3093373952,102141657391110,102142038981195)]
theorem point_links_checked23570 : (cuts23570.take 1).map (fun c => (3093299201-1+2*2^9*c.k,102141341369158+c.lower,102141722959074+c.upper)) = pointBounds23570 := by
 decide +kernel
def cuts23571 : List PrefixCut := [⟨40,173974014,173974108⟩,
⟨128,547937334,547937645⟩]
theorem checked23571 : checkPrefixCuts (2^48) 3093430273 9 Manual.Count131072.C023571.packed 128 cuts23571 = true := by
 decide +kernel
def pointBounds23571 : List (Nat × Nat × Nat) := [(3093471232,102142066579474,102142448169784)]
theorem point_links_checked23571 : (cuts23571.take 1).map (fun c => (3093430273-1+2*2^9*c.k,102141892605460+c.lower,102142274195676+c.upper)) = pointBounds23571 := by
 decide +kernel
def cuts23572 : List PrefixCut := [⟨7,30207760,30207777⟩,
⟨102,434093142,434093388⟩,
⟨128,547186093,547186404⟩]
theorem checked23572 : checkPrefixCuts (2^48) 3093561345 9 Manual.Count131072.C023572.packed 128 cuts23572 = true := by
 decide +kernel
def pointBounds23572 : List (Nat × Nat × Nat) := [(3093568512,102142470750554,102142852341098),(3093665792,102142874635936,102143256226709)]
theorem point_links_checked23572 : (cuts23572.take 2).map (fun c => (3093561345-1+2*2^9*c.k,102142440542794+c.lower,102142822133321+c.upper)) = pointBounds23572 := by
 decide +kernel
def cuts23573 : List PrefixCut := [⟨69,293782334,293782505⟩,
⟨128,547345017,547345339⟩]
theorem checked23573 : checkPrefixCuts (2^48) 3093692417 9 Manual.Count131072.C023573.packed 128 cuts23573 = true := by
 decide +kernel
def pointBounds23573 : List (Nat × Nat × Nat) := [(3093763072,102143281511221,102143663102230)]
theorem point_links_checked23573 : (cuts23573.take 1).map (fun c => (3093692417-1+2*2^9*c.k,102142987728887+c.lower,102143369319725+c.upper)) = pointBounds23573 := by
 decide +kernel
def cuts23574 : List PrefixCut := [⟨36,155210313,155210403⟩,
⟨128,550960937,550961247⟩]
theorem checked23574 : checkPrefixCuts (2^48) 3093823489 9 Manual.Count131072.C023574.packed 128 cuts23574 = true := by
 decide +kernel
def pointBounds23574 : List (Nat × Nat × Nat) := [(3093860352,102143690284217,102144071875467)]
theorem point_links_checked23574 : (cuts23574.take 1).map (fun c => (3093823489-1+2*2^9*c.k,102143535073904+c.lower,102143916665064+c.upper)) = pointBounds23574 := by
 decide +kernel
def cuts23575 : List PrefixCut := [⟨3,12554649,12554657⟩,
⟨98,411840609,411840848⟩,
⟨128,539019979,539020293⟩]
theorem checked23575 : checkPrefixCuts (2^48) 3093954561 9 Manual.Count131072.C023575.packed 128 cuts23575 = true := by
 decide +kernel
def pointBounds23575 : List (Nat × Nat × Nat) := [(3093957632,102144098589490,102144480180968),(3094054912,102144497875450,102144879467159)]
theorem point_links_checked23575 : (cuts23575.take 2).map (fun c => (3093954561-1+2*2^9*c.k,102144086034841+c.lower,102144467626311+c.upper)) = pointBounds23575 := by
 decide +kernel
def cuts23576 : List PrefixCut := [⟨65,274368373,274368534⟩,
⟨128,544455348,544455661⟩]
theorem checked23576 : checkPrefixCuts (2^48) 3094085633 9 Manual.Count131072.C023576.packed 128 cuts23576 = true := by
 decide +kernel
def pointBounds23576 : List (Nat × Nat × Nat) := [(3094152192,102144899423193,102145281015138)]
theorem point_links_checked23576 : (cuts23576.take 1).map (fun c => (3094085633-1+2*2^9*c.k,102144625054820+c.lower,102145006646604+c.upper)) = pointBounds23576 := by
 decide +kernel
def cuts23577 : List PrefixCut := [⟨32,135359759,135359836⟩,
⟨127,541703381,541703682⟩,
⟨128,546342556,546342860⟩]
theorem checked23577 : checkPrefixCuts (2^48) 3094216705 9 Manual.Count131072.C023577.packed 128 cuts23577 = true := by
 decide +kernel
def pointBounds23577 : List (Nat × Nat × Nat) := [(3094249472,102145304869927,102145686462101),(3094346752,102145711213549,102146092805947)]
theorem point_links_checked23577 : (cuts23577.take 2).map (fun c => (3094216705-1+2*2^9*c.k,102145169510168+c.lower,102145551102265+c.upper)) = pointBounds23577 := by
 decide +kernel
def cuts23578 : List PrefixCut := [⟨94,392959296,392959519⟩,
⟨128,534858256,534858555⟩]
theorem checked23578 : checkPrefixCuts (2^48) 3094347777 9 Manual.Count131072.C023578.packed 128 cuts23578 = true := by
 decide +kernel
def pointBounds23578 : List (Nat × Nat × Nat) := [(3094444032,102146108812020,102146490404644)]
theorem point_links_checked23578 : (cuts23578.take 1).map (fun c => (3094347777-1+2*2^9*c.k,102145715852724+c.lower,102146097445125+c.upper)) = pointBounds23578 := by
 decide +kernel
def cuts23579 : List PrefixCut := [⟨61,260143968,260144111⟩,
⟨128,546205354,546205657⟩]
theorem checked23579 : checkPrefixCuts (2^48) 3094478849 9 Manual.Count131072.C023579.packed 128 cuts23579 = true := by
 decide +kernel
def pointBounds23579 : List (Nat × Nat × Nat) := [(3094541312,102146510854948,102146892447791)]
theorem point_links_checked23579 : (cuts23579.take 1).map (fun c => (3094478849-1+2*2^9*c.k,102146250710980+c.lower,102146632303680+c.upper)) = pointBounds23579 := by
 decide +kernel
def cuts23580 : List PrefixCut := [⟨28,120152974,120153042⟩,
⟨123,527900743,527901045⟩,
⟨128,549547491,549547804⟩]
theorem checked23580 : checkPrefixCuts (2^48) 3094609921 9 Manual.Count131072.C023580.packed 128 cuts23580 = true := by
 decide +kernel
def pointBounds23580 : List (Nat × Nat × Nat) := [(3094638592,102146917069308,102147298662379),(3094735872,102147324817077,102147706410382)]
theorem point_links_checked23580 : (cuts23580.take 2).map (fun c => (3094609921-1+2*2^9*c.k,102146796916334+c.lower,102147178509337+c.upper)) = pointBounds23580 := by
 decide +kernel
def cuts23581 : List PrefixCut := [⟨90,379630687,379630912⟩,
⟨128,537973537,537973851⟩]
theorem checked23581 : checkPrefixCuts (2^48) 3094740993 9 Manual.Count131072.C023581.packed 128 cuts23581 = true := by
 decide +kernel
def pointBounds23581 : List (Nat × Nat × Nat) := [(3094833152,102147726094512,102148107688053)]
theorem point_links_checked23581 : (cuts23581.take 1).map (fun c => (3094740993-1+2*2^9*c.k,102147346463825+c.lower,102147728057141+c.upper)) = pointBounds23581 := by
 decide +kernel
def cuts23582 : List PrefixCut := [⟨57,244195204,244195345⟩,
⟨128,546954513,546954831⟩]
theorem checked23582 : checkPrefixCuts (2^48) 3094872065 9 Manual.Count131072.C023582.packed 128 cuts23582 = true := by
 decide +kernel
def pointBounds23582 : List (Nat × Nat × Nat) := [(3094930432,102148128632566,102148510226337)]
theorem point_links_checked23582 : (cuts23582.take 1).map (fun c => (3094872065-1+2*2^9*c.k,102147884437362+c.lower,102148266030992+c.upper)) = pointBounds23582 := by
 decide +kernel
def cuts23583 : List PrefixCut := [⟨24,106223278,106223335⟩,
⟨119,506371583,506371867⟩,
⟨128,546385726,546386034⟩]
theorem checked23583 : checkPrefixCuts (2^48) 3095003137 9 Manual.Count131072.C023583.packed 128 cuts23583 = true := by
 decide +kernel
def pointBounds23583 : List (Nat × Nat × Nat) := [(3095027712,102148537615153,102148919209158),(3095124992,102148937763458,102149319357690)]
theorem point_links_checked23583 : (cuts23583.take 2).map (fun c => (3095003137-1+2*2^9*c.k,102148431391875+c.lower,102148812985823+c.upper)) = pointBounds23583 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000111
