import PlattAssemblyKernel
import PlattCertificates.Count131072.C017008
import PlattCertificates.Count131072.C017009
import PlattCertificates.Count131072.C017010
import PlattCertificates.Count131072.C017011
import PlattCertificates.Count131072.C017012
import PlattCertificates.Count131072.C017013
import PlattCertificates.Count131072.C017014
import PlattCertificates.Count131072.C017015
import PlattCertificates.Count131072.C017016
import PlattCertificates.Count131072.C017017
import PlattCertificates.Count131072.C017018
import PlattCertificates.Count131072.C017019
import PlattCertificates.Count131072.C017020
import PlattCertificates.Count131072.C017021
import PlattCertificates.Count131072.C017022
import PlattCertificates.Count131072.C017023
import PlattCertificates.Count131072.C017024
import PlattCertificates.Count131072.C017025
import PlattCertificates.Count131072.C017026
import PlattCertificates.Count131072.C017027
import PlattCertificates.Count131072.C017028
import PlattCertificates.Count131072.C017029
import PlattCertificates.Count131072.C017030
import PlattCertificates.Count131072.C017031
import PlattCertificates.Count131072.C017032
import PlattCertificates.Count131072.C017033
import PlattCertificates.Count131072.C017034
import PlattCertificates.Count131072.C017035
import PlattCertificates.Count131072.C017036
import PlattCertificates.Count131072.C017037
import PlattCertificates.Count131072.C017038
import PlattCertificates.Count131072.C017039
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000219
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17008 : List PrefixCut := [⟨46,272245246,272245412⟩,
⟨115,678711772,678712192⟩,
⟨128,755340308,755340775⟩]
theorem checked17008 : checkPrefixCuts (2^48) 2233204737 9 Manual.Count131072.C017008.packed 128 cuts17008 = true := by
 decide +kernel
def pointBounds17008 : List (Nat × Nat × Nat) := [(2233251840,97913451835766,97913830929915),(2233322496,97913858302292,97914237396695)]
theorem point_links_checked17008 : (cuts17008.take 2).map (fun c => (2233204737-1+2*2^9*c.k,97913179590520+c.lower,97913558684503+c.upper)) = pointBounds17008 := by
 decide +kernel
def cuts17009 : List PrefixCut := [⟨56,331589640,331589848⟩,
⟨125,743575744,743576214⟩,
⟨128,760967344,760967824⟩]
theorem checked17009 : checkPrefixCuts (2^48) 2233335809 9 Manual.Count131072.C017009.packed 128 cuts17009 = true := by
 decide +kernel
def pointBounds17009 : List (Nat × Nat × Nat) := [(2233393152,97914266520468,97914645615126),(2233463808,97914678506572,97915057601492)]
theorem point_links_checked17009 : (cuts17009.take 2).map (fun c => (2233335809-1+2*2^9*c.k,97913934930828+c.lower,97914314025278+c.upper)) = pointBounds17009 := by
 decide +kernel
def cuts17010 : List PrefixCut := [⟨66,388784305,388784546⟩,
⟨128,767979681,767980157⟩]
theorem checked17010 : checkPrefixCuts (2^48) 2233466881 9 Manual.Count131072.C017010.packed 128 cuts17010 = true := by
 decide +kernel
def pointBounds17010 : List (Nat × Nat × Nat) := [(2233534464,97915084682477,97915463777648)]
theorem point_links_checked17010 : (cuts17010.take 1).map (fun c => (2233466881-1+2*2^9*c.k,97914695898172+c.lower,97915074993102+c.upper)) = pointBounds17010 := by
 decide +kernel
def cuts17011 : List PrefixCut := [⟨7,41208015,41208039⟩,
⟨76,452902932,452903214⟩,
⟨128,758735766,758736246⟩]
theorem checked17011 : checkPrefixCuts (2^48) 2233597953 9 Manual.Count131072.C017011.packed 128 cuts17011 = true := by
 decide +kernel
def pointBounds17011 : List (Nat × Nat × Nat) := [(2233605120,97915505085868,97915884181298),(2233675776,97915916780785,97916295876473)]
theorem point_links_checked17011 : (cuts17011.take 2).map (fun c => (2233597953-1+2*2^9*c.k,97915463877853+c.lower,97915842973259+c.upper)) = pointBounds17011 := by
 decide +kernel
def cuts17012 : List PrefixCut := [⟨17,105596976,105597043⟩,
⟨86,529614663,529614993⟩,
⟨128,778978644,778979128⟩]
theorem checked17012 : checkPrefixCuts (2^48) 2233729025 9 Manual.Count131072.C017012.packed 128 cuts17012 = true := by
 decide +kernel
def pointBounds17012 : List (Nat × Nat × Nat) := [(2233746432,97916328210595,97916707306548),(2233817088,97916752228282,97917131324498)]
theorem point_links_checked17012 : (cuts17012.take 2).map (fun c => (2233729025-1+2*2^9*c.k,97916222613619+c.lower,97916601709505+c.upper)) = pointBounds17012 := by
 decide +kernel
def cuts17013 : List PrefixCut := [⟨27,158637817,158637915⟩,
⟨96,578848660,578849017⟩,
⟨128,774900542,774901022⟩]
theorem checked17013 : checkPrefixCuts (2^48) 2233860097 9 Manual.Count131072.C017013.packed 128 cuts17013 = true := by
 decide +kernel
def pointBounds17013 : List (Nat × Nat × Nat) := [(2233887744,97917160230080,97917539326548),(2233958400,97917580440923,97917959537650)]
theorem point_links_checked17013 : (cuts17013.take 2).map (fun c => (2233860097-1+2*2^9*c.k,97917001592263+c.lower,97917380688633+c.upper)) = pointBounds17013 := by
 decide +kernel
def cuts17014 : List PrefixCut := [⟨37,218349939,218350074⟩,
⟨106,634880440,634880837⟩,
⟨128,766539622,766540099⟩]
theorem checked17014 : checkPrefixCuts (2^48) 2233991169 9 Manual.Count131072.C017014.packed 128 cuts17014 = true := by
 decide +kernel
def pointBounds17014 : List (Nat × Nat × Nat) := [(2234029056,97917994842744,97918373939729),(2234099712,97918411373245,97918790470492)]
theorem point_links_checked17014 : (cuts17014.take 2).map (fun c => (2233991169-1+2*2^9*c.k,97917776492805+c.lower,97918155589655+c.upper)) = pointBounds17014 := by
 decide +kernel
def cuts17015 : List PrefixCut := [⟨47,283976207,283976387⟩,
⟨116,707409489,707409931⟩,
⟨128,776699580,776700064⟩]
theorem checked17015 : checkPrefixCuts (2^48) 2234122241 9 Manual.Count131072.C017015.packed 128 cuts17015 = true := by
 decide +kernel
def pointBounds17015 : List (Nat × Nat × Nat) := [(2234170368,97918827008634,97919206106141),(2234241024,97919250441916,97919629539685)]
theorem point_links_checked17015 : (cuts17015.take 2).map (fun c => (2234122241-1+2*2^9*c.k,97918543032427+c.lower,97918922129754+c.upper)) = pointBounds17015 := by
 decide +kernel
def cuts17016 : List PrefixCut := [⟨57,341531700,341531913⟩,
⟨126,752844501,752844974⟩,
⟨128,763804265,763804745⟩]
theorem checked17016 : checkPrefixCuts (2^48) 2234253313 9 Manual.Count131072.C017016.packed 128 cuts17016 = true := by
 decide +kernel
def pointBounds17016 : List (Nat × Nat × Nat) := [(2234311680,97919661263707,97920040361731),(2234382336,97920072576508,97920451674792)]
theorem point_links_checked17016 : (cuts17016.take 2).map (fun c => (2234253313-1+2*2^9*c.k,97919319732007+c.lower,97919698829818+c.upper)) = pointBounds17016 := by
 decide +kernel
def cuts17017 : List PrefixCut := [⟨67,403237454,403237707⟩,
⟨128,765019392,765019873⟩]
theorem checked17017 : checkPrefixCuts (2^48) 2234384385 9 Manual.Count131072.C017017.packed 128 cuts17017 = true := by
 decide +kernel
def pointBounds17017 : List (Nat × Nat × Nat) := [(2234452992,97920486773726,97920865872270)]
theorem point_links_checked17017 : (cuts17017.take 1).map (fun c => (2234384385-1+2*2^9*c.k,97920083536272+c.lower,97920462634563+c.upper)) = pointBounds17017 := by
 decide +kernel
def cuts17018 : List PrefixCut := [⟨8,49252953,49252984⟩,
⟨77,462164201,462164484⟩,
⟨128,772280037,772280515⟩]
theorem checked17018 : checkPrefixCuts (2^48) 2234515457 9 Manual.Count131072.C017018.packed 128 cuts17018 = true := by
 decide +kernel
def pointBounds17018 : List (Nat × Nat × Nat) := [(2234523648,97920897808617,97921276907420),(2234594304,97921310719865,97921689818920)]
theorem point_links_checked17018 : (cuts17018.take 2).map (fun c => (2234515457-1+2*2^9*c.k,97920848555664+c.lower,97921227654436+c.upper)) = pointBounds17018 := by
 decide +kernel
def cuts17019 : List PrefixCut := [⟨18,107065103,107065170⟩,
⟨87,520454204,520454527⟩,
⟨128,770471421,770471898⟩]
theorem checked17019 : checkPrefixCuts (2^48) 2234646529 9 Manual.Count131072.C017019.packed 128 cuts17019 = true := by
 decide +kernel
def pointBounds17019 : List (Nat × Nat × Nat) := [(2234664960,97921727900804,97922107000121),(2234735616,97922141289905,97922520389478)]
theorem point_links_checked17019 : (cuts17019.take 2).map (fun c => (2234646529-1+2*2^9*c.k,97921620835701+c.lower,97921999934951+c.upper)) = pointBounds17019 := by
 decide +kernel
def cuts17020 : List PrefixCut := [⟨28,170412080,170412185⟩,
⟨97,581885782,581886147⟩,
⟨128,768033370,768033851⟩]
theorem checked17020 : checkPrefixCuts (2^48) 2234777601 9 Manual.Count131072.C017020.packed 128 cuts17020 = true := by
 decide +kernel
def pointBounds17020 : List (Nat × Nat × Nat) := [(2234806272,97922561719202,97922940819034),(2234876928,97922973192904,97923352292996)]
theorem point_links_checked17020 : (cuts17020.take 2).map (fun c => (2234777601-1+2*2^9*c.k,97922391307122+c.lower,97922770406849+c.upper)) = pointBounds17020 := by
 decide +kernel
def cuts17021 : List PrefixCut := [⟨38,229091412,229091553⟩,
⟨107,639531485,639531882⟩,
⟨128,762950652,762951126⟩]
theorem checked17021 : checkPrefixCuts (2^48) 2234908673 9 Manual.Count131072.C017021.packed 128 cuts17021 = true := by
 decide +kernel
def pointBounds17021 : List (Nat × Nat × Nat) := [(2234947584,97923388431904,97923767532253),(2235018240,97923798871977,97924177972582)]
theorem point_links_checked17021 : (cuts17021.take 2).map (fun c => (2234908673-1+2*2^9*c.k,97923159340492+c.lower,97923538440700+c.upper)) = pointBounds17021 := by
 decide +kernel
def cuts17022 : List PrefixCut := [⟨48,285370788,285370965⟩,
⟨117,704474369,704474809⟩,
⟨128,771469260,771469742⟩]
theorem checked17022 : checkPrefixCuts (2^48) 2235039745 9 Manual.Count131072.C017022.packed 128 cuts17022 = true := by
 decide +kernel
def pointBounds17022 : List (Nat × Nat × Nat) := [(2235088896,97924207661932,97924586762791),(2235159552,97924626765513,97925005866635)]
theorem point_links_checked17022 : (cuts17022.take 2).map (fun c => (2235039745-1+2*2^9*c.k,97923922291144+c.lower,97924301391826+c.upper)) = pointBounds17022 := by
 decide +kernel
def cuts17023 : List PrefixCut := [⟨58,341517381,341517599⟩,
⟨127,758453735,758454213⟩,
⟨128,764623941,764624423⟩]
theorem checked17023 : checkPrefixCuts (2^48) 2235170817 9 Manual.Count131072.C017023.packed 128 cuts17023 = true := by
 decide +kernel
def pointBounds17023 : List (Nat × Nat × Nat) := [(2235230208,97925035277785,97925414379167),(2235300864,97925452214139,97925831315781)]
theorem point_links_checked17023 : (cuts17023.take 2).map (fun c => (2235170817-1+2*2^9*c.k,97924693760404+c.lower,97925072861568+c.upper)) = pointBounds17023 := by
 decide +kernel
def cuts17024 : List PrefixCut := [⟨68,407227131,407227390⟩,
⟨128,766593986,766594471⟩]
theorem checked17024 : checkPrefixCuts (2^48) 2235301889 9 Manual.Count131072.C017024.packed 128 cuts17024 = true := by
 decide +kernel
def pointBounds17024 : List (Nat × Nat × Nat) := [(2235371520,97925865611476,97926244713381)]
theorem point_links_checked17024 : (cuts17024.take 1).map (fun c => (2235301889-1+2*2^9*c.k,97925458384345+c.lower,97925837485991+c.upper)) = pointBounds17024 := by
 decide +kernel
def cuts17025 : List PrefixCut := [⟨9,54017493,54017526⟩,
⟨78,466633226,466633519⟩,
⟨128,761638511,761638988⟩]
theorem checked17025 : checkPrefixCuts (2^48) 2235432961 9 Manual.Count131072.C017025.packed 128 cuts17025 = true := by
 decide +kernel
def pointBounds17025 : List (Nat × Nat × Nat) := [(2235442176,97926278995824,97926658097988),(2235512832,97926691611557,97927070713981)]
theorem point_links_checked17025 : (cuts17025.take 2).map (fun c => (2235432961-1+2*2^9*c.k,97926224978331+c.lower,97926604080462+c.upper)) = pointBounds17025 := by
 decide +kernel
def cuts17026 : List PrefixCut := [⟨19,112309257,112309327⟩,
⟨88,527039275,527039604⟩,
⟨128,766252197,766252673⟩]
theorem checked17026 : checkPrefixCuts (2^48) 2235564033 9 Manual.Count131072.C017026.packed 128 cuts17026 = true := by
 decide +kernel
def pointBounds17026 : List (Nat × Nat × Nat) := [(2235583488,97927098926099,97927478028777),(2235654144,97927513656117,97927892759054)]
theorem point_links_checked17026 : (cuts17026.take 2).map (fun c => (2235564033-1+2*2^9*c.k,97926986616842+c.lower,97927365719450+c.upper)) = pointBounds17026 := by
 decide +kernel
def cuts17027 : List PrefixCut := [⟨29,172230592,172230697⟩,
⟨98,596376633,596377002⟩,
⟨128,770487848,770488327⟩]
theorem checked17027 : checkPrefixCuts (2^48) 2235695105 9 Manual.Count131072.C017027.packed 128 cuts17027 = true := by
 decide +kernel
def pointBounds17027 : List (Nat × Nat × Nat) := [(2235724800,97927925099631,97928304202820),(2235795456,97928349245672,97928728349125)]
theorem point_links_checked17027 : (cuts17027.take 2).map (fun c => (2235695105-1+2*2^9*c.k,97927752869039+c.lower,97928131972123+c.upper)) = pointBounds17027 := by
 decide +kernel
def cuts17028 : List PrefixCut := [⟨39,234662476,234662619⟩,
⟨108,645689359,645689762⟩,
⟨128,763896507,763896979⟩]
theorem checked17028 : checkPrefixCuts (2^48) 2235826177 9 Manual.Count131072.C017028.packed 128 cuts17028 = true := by
 decide +kernel
def pointBounds17028 : List (Nat × Nat × Nat) := [(2235866112,97928758019363,97929137123069),(2235936768,97929169046246,97929548150212)]
theorem point_links_checked17028 : (cuts17028.take 2).map (fun c => (2235826177-1+2*2^9*c.k,97928523356887+c.lower,97928902460450+c.upper)) = pointBounds17028 := by
 decide +kernel
def cuts17029 : List PrefixCut := [⟨49,296834978,296835164⟩,
⟨118,712871008,712871454⟩,
⟨128,772537439,772537922⟩]
theorem checked17029 : checkPrefixCuts (2^48) 2235957249 9 Manual.Count131072.C017029.packed 128 cuts17029 = true := by
 decide +kernel
def pointBounds17029 : List (Nat × Nat × Nat) := [(2236007424,97929584088372,97929963192593),(2236078080,97930000124402,97930379228883)]
theorem point_links_checked17029 : (cuts17029.take 2).map (fun c => (2235957249-1+2*2^9*c.k,97929287253394+c.lower,97929666357429+c.upper)) = pointBounds17029 := by
 decide +kernel
def cuts17030 : List PrefixCut := [⟨59,358244613,358244832⟩,
⟨128,777904770,777905248⟩]
theorem checked17030 : checkPrefixCuts (2^48) 2236088321 9 Manual.Count131072.C017030.packed 128 cuts17030 = true := by
 decide +kernel
def pointBounds17030 : List (Nat × Nat × Nat) := [(2236148736,97930418035446,97930797140183),(2236219392,97930837695603,97931216800599)]
theorem point_links_checked17030 : (cuts17030.take 2).map (fun c => (2236088321-1+2*2^9*c.k,97930059790833+c.lower,97930438895351+c.upper)) = pointBounds17030 := by
 decide +kernel
def cuts17031 : List PrefixCut := [⟨69,413353379,413353638⟩,
⟨128,766531072,766531557⟩]
theorem checked17031 : checkPrefixCuts (2^48) 2236219393 9 Manual.Count131072.C017031.packed 128 cuts17031 = true := by
 decide +kernel
def pointBounds17031 : List (Nat × Nat × Nat) := [(2236290048,97931251048982,97931630154237)]
theorem point_links_checked17031 : (cuts17031.take 1).map (fun c => (2236219393-1+2*2^9*c.k,97930837695603+c.lower,97931216800599+c.upper)) = pointBounds17031 := by
 decide +kernel
def cuts17032 : List PrefixCut := [⟨10,59785023,59785060⟩,
⟨79,474370938,474371236⟩,
⟨128,765101831,765102314⟩]
theorem checked17032 : checkPrefixCuts (2^48) 2236350465 9 Manual.Count131072.C017032.packed 128 cuts17032 = true := by
 decide +kernel
def pointBounds17032 : List (Nat × Nat × Nat) := [(2236360704,97931664011698,97932043117216),(2236431360,97932078597613,97932457703392)]
theorem point_links_checked17032 : (cuts17032.take 2).map (fun c => (2236350465-1+2*2^9*c.k,97931604226675+c.lower,97931983332156+c.upper)) = pointBounds17032 := by
 decide +kernel
def cuts17033 : List PrefixCut := [⟨20,119688645,119688720⟩,
⟨89,540918583,540918919⟩,
⟨128,774244239,774244720⟩]
theorem checked17033 : checkPrefixCuts (2^48) 2236481537 9 Manual.Count131072.C017033.packed 128 cuts17033 = true := by
 decide +kernel
def pointBounds17033 : List (Nat × Nat × Nat) := [(2236502016,97932489017151,97932868123190),(2236572672,97932910247089,97933289353389)]
theorem point_links_checked17033 : (cuts17033.take 2).map (fun c => (2236481537-1+2*2^9*c.k,97932369328506+c.lower,97932748434470+c.upper)) = pointBounds17033 := by
 decide +kernel
def cuts17034 : List PrefixCut := [⟨30,176942125,176942237⟩,
⟨99,597264567,597264936⟩,
⟨128,766522333,766522807⟩]
theorem checked17034 : checkPrefixCuts (2^48) 2236612609 9 Manual.Count131072.C017034.packed 128 cuts17034 = true := by
 decide +kernel
def pointBounds17034 : List (Nat × Nat × Nat) := [(2236643328,97933320514870,97933699621427),(2236713984,97933740837312,97934119944126)]
theorem point_links_checked17034 : (cuts17034.take 2).map (fun c => (2236612609-1+2*2^9*c.k,97933143572745+c.lower,97933522679190+c.upper)) = pointBounds17034 := by
 decide +kernel
def cuts17035 : List PrefixCut := [⟨40,240732358,240732509⟩,
⟨109,658385646,658386057⟩,
⟨128,770378392,770378873⟩]
theorem checked17035 : checkPrefixCuts (2^48) 2236743681 9 Manual.Count131072.C017035.packed 128 cuts17035 = true := by
 decide +kernel
def pointBounds17035 : List (Nat × Nat × Nat) := [(2236784640,97934150827436,97934529934506),(2236855296,97934568480724,97934947588054)]
theorem point_links_checked17035 : (cuts17035.take 2).map (fun c => (2236743681-1+2*2^9*c.k,97933910095078+c.lower,97934289201997+c.upper)) = pointBounds17035 := by
 decide +kernel
def cuts17036 : List PrefixCut := [⟨50,298474811,298474998⟩,
⟨119,713333413,713333860⟩,
⟨128,765551573,765552053⟩]
theorem checked17036 : checkPrefixCuts (2^48) 2236874753 9 Manual.Count131072.C017036.packed 128 cuts17036 = true := by
 decide +kernel
def pointBounds17036 : List (Nat × Nat × Nat) := [(2236925952,97934978948281,97935358055868),(2236996608,97935393806883,97935772914730)]
theorem point_links_checked17036 : (cuts17036.take 2).map (fun c => (2236874753-1+2*2^9*c.k,97934680473470+c.lower,97935059580870+c.upper)) = pointBounds17036 := by
 decide +kernel
def cuts17037 : List PrefixCut := [⟨60,358600892,358601113⟩,
⟨128,775698166,775698646⟩]
theorem checked17037 : checkPrefixCuts (2^48) 2237005825 9 Manual.Count131072.C017037.packed 128 cuts17037 = true := by
 decide +kernel
def pointBounds17037 : List (Nat × Nat × Nat) := [(2237067264,97935804625935,97936183734036)]
theorem point_links_checked17037 : (cuts17037.take 1).map (fun c => (2237005825-1+2*2^9*c.k,97935446025043+c.lower,97935825132923+c.upper)) = pointBounds17037 := by
 decide +kernel
def cuts17038 : List PrefixCut := [⟨1,5787684,5787688⟩,
⟨70,418468120,418468384⟩,
⟨128,768229839,768230319⟩]
theorem checked17038 : checkPrefixCuts (2^48) 2237136897 9 Manual.Count131072.C017038.packed 128 cuts17038 = true := by
 decide +kernel
def pointBounds17038 : List (Nat × Nat × Nat) := [(2237137920,97936227510893,97936606619257),(2237208576,97936640191329,97937019299953)]
theorem point_links_checked17038 : (cuts17038.take 2).map (fun c => (2237136897-1+2*2^9*c.k,97936221723209+c.lower,97936600831569+c.upper)) = pointBounds17038 := by
 decide +kernel
def cuts17039 : List PrefixCut := [⟨11,68064057,68064099⟩,
⟨80,477069992,477070290⟩,
⟨128,763404190,763404666⟩]
theorem checked17039 : checkPrefixCuts (2^48) 2237267969 9 Manual.Count131072.C017039.packed 128 cuts17039 = true := by
 decide +kernel
def pointBounds17039 : List (Nat × Nat × Nat) := [(2237279232,97937058017105,97937437125987),(2237349888,97937467023040,97937846132178)]
theorem point_links_checked17039 : (cuts17039.take 2).map (fun c => (2237267969-1+2*2^9*c.k,97936989953048+c.lower,97937369061888+c.upper)) = pointBounds17039 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000219
