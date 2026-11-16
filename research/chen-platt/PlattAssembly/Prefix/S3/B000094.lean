import PlattAssemblyKernel
import PlattCertificates.Count131072.C023008
import PlattCertificates.Count131072.C023009
import PlattCertificates.Count131072.C023010
import PlattCertificates.Count131072.C023011
import PlattCertificates.Count131072.C023012
import PlattCertificates.Count131072.C023013
import PlattCertificates.Count131072.C023014
import PlattCertificates.Count131072.C023015
import PlattCertificates.Count131072.C023016
import PlattCertificates.Count131072.C023017
import PlattCertificates.Count131072.C023018
import PlattCertificates.Count131072.C023019
import PlattCertificates.Count131072.C023020
import PlattCertificates.Count131072.C023021
import PlattCertificates.Count131072.C023022
import PlattCertificates.Count131072.C023023
import PlattCertificates.Count131072.C023024
import PlattCertificates.Count131072.C023025
import PlattCertificates.Count131072.C023026
import PlattCertificates.Count131072.C023027
import PlattCertificates.Count131072.C023028
import PlattCertificates.Count131072.C023029
import PlattCertificates.Count131072.C023030
import PlattCertificates.Count131072.C023031
import PlattCertificates.Count131072.C023032
import PlattCertificates.Count131072.C023033
import PlattCertificates.Count131072.C023034
import PlattCertificates.Count131072.C023035
import PlattCertificates.Count131072.C023036
import PlattCertificates.Count131072.C023037
import PlattCertificates.Count131072.C023038
import PlattCertificates.Count131072.C023039
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000094
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23008 : List PrefixCut := [⟨68,293809783,293809951⟩,
⟨128,559463183,559463502⟩]
theorem checked23008 : checkPrefixCuts (2^48) 3019636737 9 Manual.Count131072.C023008.packed 128 cuts23008 = true := by
 decide +kernel
def pointBounds23008 : List (Nat × Nat × Nat) := [(3019706368,101830995683700,101831377097777)]
theorem point_links_checked23008 : (cuts23008.take 1).map (fun c => (3019636737-1+2*2^9*c.k,101830701873917+c.lower,101831083287826+c.upper)) = pointBounds23008 := by
 decide +kernel
def cuts23009 : List PrefixCut := [⟨33,141679585,141679670⟩,
⟨126,550863805,550864119⟩,
⟨128,559159206,559159526⟩]
theorem checked23009 : checkPrefixCuts (2^48) 3019767809 9 Manual.Count131072.C023009.packed 128 cuts23009 = true := by
 decide +kernel
def pointBounds23009 : List (Nat × Nat × Nat) := [(3019801600,101831403016685,101831784430998),(3019896832,101831812200905,101832193615447)]
theorem point_links_checked23009 : (cuts23009.take 2).map (fun c => (3019767809-1+2*2^9*c.k,101831261337100+c.lower,101831642751328+c.upper)) = pointBounds23009 := by
 decide +kernel
def cuts23010 : List PrefixCut := [⟨91,397334055,397334280⟩,
⟨128,561744625,561744937⟩]
theorem checked23010 : checkPrefixCuts (2^48) 3019898881 9 Manual.Count131072.C023010.packed 128 cuts23010 = true := by
 decide +kernel
def pointBounds23010 : List (Nat × Nat × Nat) := [(3019992064,101832217830361,101832599245134)]
theorem point_links_checked23010 : (cuts23010.take 1).map (fun c => (3019898881-1+2*2^9*c.k,101831820496306+c.lower,101832201910854+c.upper)) = pointBounds23010 := by
 decide +kernel
def cuts23011 : List PrefixCut := [⟨56,247357587,247357730⟩,
⟨128,558085650,558085966⟩]
theorem checked23011 : checkPrefixCuts (2^48) 3020029953 9 Manual.Count131072.C023011.packed 128 cuts23011 = true := by
 decide +kernel
def pointBounds23011 : List (Nat × Nat × Nat) := [(3020087296,101832629598518,101833011013521)]
theorem point_links_checked23011 : (cuts23011.take 1).map (fun c => (3020029953-1+2*2^9*c.k,101832382240931+c.lower,101832763655791+c.upper)) = pointBounds23011 := by
 decide +kernel
def cuts23012 : List PrefixCut := [⟨21,93011911,93011960⟩,
⟨114,505779241,505779519⟩,
⟨128,566915038,566915350⟩]
theorem checked23012 : checkPrefixCuts (2^48) 3020161025 9 Manual.Count131072.C023012.packed 128 cuts23012 = true := by
 decide +kernel
def pointBounds23012 : List (Nat × Nat × Nat) := [(3020182528,101833033338492,101833414753717),(3020277760,101833446105822,101833827521276)]
theorem point_links_checked23012 : (cuts23012.take 2).map (fun c => (3020161025-1+2*2^9*c.k,101832940326581+c.lower,101833321741757+c.upper)) = pointBounds23012 := by
 decide +kernel
def cuts23013 : List PrefixCut := [⟨79,347424777,347424970⟩,
⟨128,558969071,558969383⟩]
theorem checked23013 : checkPrefixCuts (2^48) 3020292097 9 Manual.Count131072.C023013.packed 128 cuts23013 = true := by
 decide +kernel
def pointBounds23013 : List (Nat × Nat × Nat) := [(3020372992,101833854666396,101834236082077)]
theorem point_links_checked23013 : (cuts23013.take 1).map (fun c => (3020292097-1+2*2^9*c.k,101833507241619+c.lower,101833888657107+c.upper)) = pointBounds23013 := by
 decide +kernel
def cuts23014 : List PrefixCut := [⟨44,190386865,190386977⟩,
⟨128,556335520,556335845⟩]
theorem checked23014 : checkPrefixCuts (2^48) 3020423169 9 Manual.Count131072.C023014.packed 128 cuts23014 = true := by
 decide +kernel
def pointBounds23014 : List (Nat × Nat × Nat) := [(3020468224,101834256597555,101834638013467)]
theorem point_links_checked23014 : (cuts23014.take 1).map (fun c => (3020423169-1+2*2^9*c.k,101834066210690+c.lower,101834447626490+c.upper)) = pointBounds23014 := by
 decide +kernel
def cuts23015 : List PrefixCut := [⟨9,40722442,40722464⟩,
⟨102,445330650,445330891⟩,
⟨128,561716062,561716367⟩]
theorem checked23015 : checkPrefixCuts (2^48) 3020554241 9 Manual.Count131072.C023015.packed 128 cuts23015 = true := by
 decide +kernel
def pointBounds23015 : List (Nat × Nat × Nat) := [(3020563456,101834663268652,101835044684799),(3020658688,101835067876860,101835449293226)]
theorem point_links_checked23015 : (cuts23015.take 2).map (fun c => (3020554241-1+2*2^9*c.k,101834622546210+c.lower,101835003962335+c.upper)) = pointBounds23015 := by
 decide +kernel
def cuts23016 : List PrefixCut := [⟨67,291471396,291471557⟩,
⟨128,554330422,554330732⟩]
theorem checked23016 : checkPrefixCuts (2^48) 3020685313 9 Manual.Count131072.C023016.packed 128 cuts23016 = true := by
 decide +kernel
def pointBounds23016 : List (Nat × Nat × Nat) := [(3020753920,101835475733668,101835857150259)]
theorem point_links_checked23016 : (cuts23016.take 1).map (fun c => (3020685313-1+2*2^9*c.k,101835184262272+c.lower,101835565678702+c.upper)) = pointBounds23016 := by
 decide +kernel
def cuts23017 : List PrefixCut := [⟨32,141909953,141910038⟩,
⟨125,543870915,543871224⟩,
⟨128,557194857,557195175⟩]
theorem checked23017 : checkPrefixCuts (2^48) 3020816385 9 Manual.Count131072.C023017.packed 128 cuts23017 = true := by
 decide +kernel
def pointBounds23017 : List (Nat × Nat × Nat) := [(3020849152,101835880502647,101836261919472),(3020944384,101836282463609,101836663880658)]
theorem point_links_checked23017 : (cuts23017.take 2).map (fun c => (3020816385-1+2*2^9*c.k,101835738592694+c.lower,101836120009434+c.upper)) = pointBounds23017 := by
 decide +kernel
def cuts23018 : List PrefixCut := [⟨90,397941716,397941944⟩,
⟨128,560431828,560432150⟩]
theorem checked23018 : checkPrefixCuts (2^48) 3020947457 9 Manual.Count131072.C023018.packed 128 cuts23018 = true := by
 decide +kernel
def pointBounds23018 : List (Nat × Nat × Nat) := [(3021039616,101836693729267,101837075146553)]
theorem point_links_checked23018 : (cuts23018.take 1).map (fun c => (3020947457-1+2*2^9*c.k,101836295787551+c.lower,101836677204609+c.upper)) = pointBounds23018 := by
 decide +kernel
def cuts23019 : List PrefixCut := [⟨55,241122584,241122722⟩,
⟨128,559941539,559941862⟩]
theorem checked23019 : checkPrefixCuts (2^48) 3021078529 9 Manual.Count131072.C023019.packed 128 cuts23019 = true := by
 decide +kernel
def pointBounds23019 : List (Nat × Nat × Nat) := [(3021134848,101837097341963,101837478759481)]
theorem point_links_checked23019 : (cuts23019.take 1).map (fun c => (3021078529-1+2*2^9*c.k,101836856219379+c.lower,101837237636759+c.upper)) = pointBounds23019 := by
 decide +kernel
def cuts23020 : List PrefixCut := [⟨20,91209497,91209546⟩,
⟨113,489952234,489952515⟩,
⟨128,556190765,556191083⟩]
theorem checked23020 : checkPrefixCuts (2^48) 3021209601 9 Manual.Count131072.C023020.packed 128 cuts23020 = true := by
 decide +kernel
def pointBounds23020 : List (Nat × Nat × Nat) := [(3021230080,101837507370415,101837888788167),(3021325312,101837906113152,101838287531136)]
theorem point_links_checked23020 : (cuts23020.take 2).map (fun c => (3021209601-1+2*2^9*c.k,101837416160918+c.lower,101837797578621+c.upper)) = pointBounds23020 := by
 decide +kernel
def cuts23021 : List PrefixCut := [⟨78,337522327,337522518⟩,
⟨128,554117007,554117317⟩]
theorem checked23021 : checkPrefixCuts (2^48) 3021340673 9 Manual.Count131072.C023021.packed 128 cuts23021 = true := by
 decide +kernel
def pointBounds23021 : List (Nat × Nat × Nat) := [(3021420544,101838309874010,101838691292222)]
theorem point_links_checked23021 : (cuts23021.take 1).map (fun c => (3021340673-1+2*2^9*c.k,101837972351683+c.lower,101838353769704+c.upper)) = pointBounds23021 := by
 decide +kernel
def cuts23022 : List PrefixCut := [⟨43,186035587,186035695⟩,
⟨128,558378240,558378558⟩]
theorem checked23022 : checkPrefixCuts (2^48) 3021471745 9 Manual.Count131072.C023022.packed 128 cuts23022 = true := by
 decide +kernel
def pointBounds23022 : List (Nat × Nat × Nat) := [(3021515776,101838712504277,101839093922716)]
theorem point_links_checked23022 : (cuts23022.take 1).map (fun c => (3021471745-1+2*2^9*c.k,101838526468690+c.lower,101838907887021+c.upper)) = pointBounds23022 := by
 decide +kernel
def cuts23023 : List PrefixCut := [⟨8,34653303,34653323⟩,
⟨101,444896706,444896960⟩,
⟨128,564036263,564036588⟩]
theorem checked23023 : checkPrefixCuts (2^48) 3021602817 9 Manual.Count131072.C023023.packed 128 cuts23023 = true := by
 decide +kernel
def pointBounds23023 : List (Nat × Nat × Nat) := [(3021611008,101839119500233,101839500918902),(3021706240,101839529743636,101839911162539)]
theorem point_links_checked23023 : (cuts23023.take 2).map (fun c => (3021602817-1+2*2^9*c.k,101839084846930+c.lower,101839466265579+c.upper)) = pointBounds23023 := by
 decide +kernel
def cuts23024 : List PrefixCut := [⟨66,287644399,287644561⟩,
⟨128,564850054,564850371⟩]
theorem checked23024 : checkPrefixCuts (2^48) 3021733889 9 Manual.Count131072.C023024.packed 128 cuts23024 = true := by
 decide +kernel
def pointBounds23024 : List (Nat × Nat × Nat) := [(3021801472,101839936527592,101840317946728)]
theorem point_links_checked23024 : (cuts23024.take 1).map (fun c => (3021733889-1+2*2^9*c.k,101839648883193+c.lower,101840030302167+c.upper)) = pointBounds23024 := by
 decide +kernel
def cuts23025 : List PrefixCut := [⟨31,135154258,135154339⟩,
⟨124,537348490,537348794⟩,
⟨128,554114069,554114383⟩]
theorem checked23025 : checkPrefixCuts (2^48) 3021864961 9 Manual.Count131072.C023025.packed 128 cuts23025 = true := by
 decide +kernel
def pointBounds23025 : List (Nat × Nat × Nat) := [(3021896704,101840348887505,101840730306877),(3021991936,101840751081737,101841132501332)]
theorem point_links_checked23025 : (cuts23025.take 2).map (fun c => (3021864961-1+2*2^9*c.k,101840213733247+c.lower,101840595152538+c.upper)) = pointBounds23025 := by
 decide +kernel
def cuts23026 : List PrefixCut := [⟨89,386719937,386720166⟩,
⟨128,554928306,554928627⟩]
theorem checked23026 : checkPrefixCuts (2^48) 3021996033 9 Manual.Count131072.C023026.packed 128 cuts23026 = true := by
 decide +kernel
def pointBounds23026 : List (Nat × Nat × Nat) := [(3022087168,101841154567253,101841535987087)]
theorem point_links_checked23026 : (cuts23026.take 1).map (fun c => (3021996033-1+2*2^9*c.k,101840767847316+c.lower,101841149266921+c.upper)) = pointBounds23026 := by
 decide +kernel
def cuts23027 : List PrefixCut := [⟨54,239548766,239548906⟩,
⟨128,560678727,560679054⟩]
theorem checked23027 : checkPrefixCuts (2^48) 3022127105 9 Manual.Count131072.C023027.packed 128 cuts23027 = true := by
 decide +kernel
def pointBounds23027 : List (Nat × Nat × Nat) := [(3022182400,101841562324388,101841943744454)]
theorem point_links_checked23027 : (cuts23027.take 1).map (fun c => (3022127105-1+2*2^9*c.k,101841322775622+c.lower,101841704195548+c.upper)) = pointBounds23027 := by
 decide +kernel
def cuts23028 : List PrefixCut := [⟨19,85869241,85869286⟩,
⟨112,495649547,495649831⟩,
⟨128,565124656,565124978⟩]
theorem checked23028 : checkPrefixCuts (2^48) 3022258177 9 Manual.Count131072.C023028.packed 128 cuts23028 = true := by
 decide +kernel
def pointBounds23028 : List (Nat × Nat × Nat) := [(3022277632,101841969323590,101842350743888),(3022372864,101842379103896,101842760524433)]
theorem point_links_checked23028 : (cuts23028.take 2).map (fun c => (3022258177-1+2*2^9*c.k,101841883454349+c.lower,101842264874602+c.upper)) = pointBounds23028 := by
 decide +kernel
def cuts23029 : List PrefixCut := [⟨77,335822160,335822346⟩,
⟨128,562399409,562399721⟩]
theorem checked23029 : checkPrefixCuts (2^48) 3022389249 9 Manual.Count131072.C023029.packed 128 cuts23029 = true := by
 decide +kernel
def pointBounds23029 : List (Nat × Nat × Nat) := [(3022468096,101842784401165,101843165821926)]
theorem point_links_checked23029 : (cuts23029.take 1).map (fun c => (3022389249-1+2*2^9*c.k,101842448579005+c.lower,101842829999580+c.upper)) = pointBounds23029 := by
 decide +kernel
def cuts23030 : List PrefixCut := [⟨42,181966697,181966805⟩,
⟨128,553528259,553528577⟩]
theorem checked23030 : checkPrefixCuts (2^48) 3022520321 9 Manual.Count131072.C023030.packed 128 cuts23030 = true := by
 decide +kernel
def pointBounds23030 : List (Nat × Nat × Nat) := [(3022563328,101843192945111,101843574366106)]
theorem point_links_checked23030 : (cuts23030.take 1).map (fun c => (3022520321-1+2*2^9*c.k,101843010978414+c.lower,101843392399301+c.upper)) = pointBounds23030 := by
 decide +kernel
def cuts23031 : List PrefixCut := [⟨7,29426472,29426488⟩,
⟨100,435430369,435430619⟩,
⟨128,554621734,554622057⟩]
theorem checked23031 : checkPrefixCuts (2^48) 3022651393 9 Manual.Count131072.C023031.packed 128 cuts23031 = true := by
 decide +kernel
def pointBounds23031 : List (Nat × Nat × Nat) := [(3022658560,101843593933145,101843975354366),(3022753792,101843999937042,101844381358497)]
theorem point_links_checked23031 : (cuts23031.take 2).map (fun c => (3022651393-1+2*2^9*c.k,101843564506673+c.lower,101843945927878+c.upper)) = pointBounds23031 := by
 decide +kernel
def cuts23032 : List PrefixCut := [⟨65,282050765,282050925⟩,
⟨128,562140004,562140327⟩]
theorem checked23032 : checkPrefixCuts (2^48) 3022782465 9 Manual.Count131072.C023032.packed 128 cuts23032 = true := by
 decide +kernel
def pointBounds23032 : List (Nat × Nat × Nat) := [(3022849024,101844401179172,101844782600860)]
theorem point_links_checked23032 : (cuts23032.take 1).map (fun c => (3022782465-1+2*2^9*c.k,101844119128407+c.lower,101844500549935+c.upper)) = pointBounds23032 := by
 decide +kernel
def cuts23033 : List PrefixCut := [⟨30,130917301,130917379⟩,
⟨123,538372693,538373004⟩,
⟨128,561091489,561091812⟩]
theorem checked23033 : checkPrefixCuts (2^48) 3022913537 9 Manual.Count131072.C023033.packed 128 cuts23033 = true := by
 decide +kernel
def pointBounds23033 : List (Nat × Nat × Nat) := [(3022944256,101844812185712,101845193607641),(3023039488,101845219641104,101845601063266)]
theorem point_links_checked23033 : (cuts23033.take 2).map (fun c => (3022913537-1+2*2^9*c.k,101844681268411+c.lower,101845062690262+c.upper)) = pointBounds23033 := by
 decide +kernel
def cuts23034 : List PrefixCut := [⟨88,383606415,383606628⟩,
⟨128,557808364,557808676⟩]
theorem checked23034 : checkPrefixCuts (2^48) 3023044609 9 Manual.Count131072.C023034.packed 128 cuts23034 = true := by
 decide +kernel
def pointBounds23034 : List (Nat × Nat × Nat) := [(3023134720,101845625966315,101846007388702)]
theorem point_links_checked23034 : (cuts23034.take 1).map (fun c => (3023044609-1+2*2^9*c.k,101845242359900+c.lower,101845623782074+c.upper)) = pointBounds23034 := by
 decide +kernel
def cuts23035 : List PrefixCut := [⟨53,232110436,232110569⟩,
⟨128,556108349,556108668⟩]
theorem checked23035 : checkPrefixCuts (2^48) 3023175681 9 Manual.Count131072.C023035.packed 128 cuts23035 = true := by
 decide +kernel
def pointBounds23035 : List (Nat × Nat × Nat) := [(3023229952,101846032278700,101846413701319)]
theorem point_links_checked23035 : (cuts23035.take 1).map (fun c => (3023175681-1+2*2^9*c.k,101845800168264+c.lower,101846181590750+c.upper)) = pointBounds23035 := by
 decide +kernel
def cuts23036 : List PrefixCut := [⟨18,79043079,79043123⟩,
⟨111,491753774,491754045⟩,
⟨128,568931929,568932242⟩]
theorem checked23036 : checkPrefixCuts (2^48) 3023306753 9 Manual.Count131072.C023036.packed 128 cuts23036 = true := by
 decide +kernel
def pointBounds23036 : List (Nat × Nat × Nat) := [(3023325184,101846435319692,101846816742541),(3023420416,101846848030387,101847229453463)]
theorem point_links_checked23036 : (cuts23036.take 2).map (fun c => (3023306753-1+2*2^9*c.k,101846356276613+c.lower,101846737699418+c.upper)) = pointBounds23036 := by
 decide +kernel
def cuts23037 : List PrefixCut := [⟨76,333005932,333006118⟩,
⟨128,562762964,562763276⟩]
theorem checked23037 : checkPrefixCuts (2^48) 3023437825 9 Manual.Count131072.C023037.packed 128 cuts23037 = true := by
 decide +kernel
def pointBounds23037 : List (Nat × Nat × Nat) := [(3023515648,101847258214474,101847639637778)]
theorem point_links_checked23037 : (cuts23037.take 1).map (fun c => (3023437825-1+2*2^9*c.k,101846925208542+c.lower,101847306631660+c.upper)) = pointBounds23037 := by
 decide +kernel
def cuts23038 : List PrefixCut := [⟨41,177900630,177900730⟩,
⟨128,557432452,557432765⟩]
theorem checked23038 : checkPrefixCuts (2^48) 3023568897 9 Manual.Count131072.C023038.packed 128 cuts23038 = true := by
 decide +kernel
def pointBounds23038 : List (Nat × Nat × Nat) := [(3023610880,101847665872136,101848047295666)]
theorem point_links_checked23038 : (cuts23038.take 1).map (fun c => (3023568897-1+2*2^9*c.k,101847487971506+c.lower,101847869394936+c.upper)) = pointBounds23038 := by
 decide +kernel
def cuts23039 : List PrefixCut := [⟨6,25506514,25506527⟩,
⟨99,427367085,427367323⟩,
⟨128,549588970,549589279⟩]
theorem checked23039 : checkPrefixCuts (2^48) 3023699969 9 Manual.Count131072.C023039.packed 128 cuts23039 = true := by
 decide +kernel
def pointBounds23039 : List (Nat × Nat × Nat) := [(3023706112,101848070910472,101848452334228),(3023801344,101848472771043,101848854195024)]
theorem point_links_checked23039 : (cuts23039.take 2).map (fun c => (3023699969-1+2*2^9*c.k,101848045403958+c.lower,101848426827701+c.upper)) = pointBounds23039 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000094
