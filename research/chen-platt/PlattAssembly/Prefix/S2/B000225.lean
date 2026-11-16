import PlattAssemblyKernel
import PlattCertificates.Count131072.C017200
import PlattCertificates.Count131072.C017201
import PlattCertificates.Count131072.C017202
import PlattCertificates.Count131072.C017203
import PlattCertificates.Count131072.C017204
import PlattCertificates.Count131072.C017205
import PlattCertificates.Count131072.C017206
import PlattCertificates.Count131072.C017207
import PlattCertificates.Count131072.C017208
import PlattCertificates.Count131072.C017209
import PlattCertificates.Count131072.C017210
import PlattCertificates.Count131072.C017211
import PlattCertificates.Count131072.C017212
import PlattCertificates.Count131072.C017213
import PlattCertificates.Count131072.C017214
import PlattCertificates.Count131072.C017215
import PlattCertificates.Count131072.C017216
import PlattCertificates.Count131072.C017217
import PlattCertificates.Count131072.C017218
import PlattCertificates.Count131072.C017219
import PlattCertificates.Count131072.C017220
import PlattCertificates.Count131072.C017221
import PlattCertificates.Count131072.C017222
import PlattCertificates.Count131072.C017223
import PlattCertificates.Count131072.C017224
import PlattCertificates.Count131072.C017225
import PlattCertificates.Count131072.C017226
import PlattCertificates.Count131072.C017227
import PlattCertificates.Count131072.C017228
import PlattCertificates.Count131072.C017229
import PlattCertificates.Count131072.C017230
import PlattCertificates.Count131072.C017231
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000225
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17200 : List PrefixCut := [⟨34,197546958,197547082⟩,
⟨103,600732841,600733214⟩,
⟨128,754899842,754900310⟩]
theorem checked17200 : checkPrefixCuts (2^48) 2258370561 9 Manual.Count131072.C017200.packed 128 cuts17200 = true := by
 decide +kernel
def pointBounds17200 : List (Nat × Nat × Nat) := [(2258405376,98059876680856,98060255866319),(2258476032,98060279866739,98060659052451)]
theorem point_links_checked17200 : (cuts17200.take 2).map (fun c => (2258370561-1+2*2^9*c.k,98059679133898+c.lower,98060058319237+c.upper)) = pointBounds17200 := by
 decide +kernel
def cuts17201 : List PrefixCut := [⟨44,259101227,259101389⟩,
⟨113,669614702,669615118⟩,
⟨128,755105552,755106022⟩]
theorem checked17201 : checkPrefixCuts (2^48) 2258501633 9 Manual.Count131072.C017201.packed 128 cuts17201 = true := by
 decide +kernel
def pointBounds17201 : List (Nat × Nat × Nat) := [(2258546688,98060693134967,98061072320936),(2258617344,98061103648442,98061482834665)]
theorem point_links_checked17201 : (cuts17201.take 2).map (fun c => (2258501633-1+2*2^9*c.k,98060434033740+c.lower,98060813219547+c.upper)) = pointBounds17201 := by
 decide +kernel
def cuts17202 : List PrefixCut := [⟨54,319152567,319152763⟩,
⟨123,738861959,738862410⟩,
⟨128,765903354,765903821⟩]
theorem checked17202 : checkPrefixCuts (2^48) 2258632705 9 Manual.Count131072.C017202.packed 128 cuts17202 = true := by
 decide +kernel
def pointBounds17202 : List (Nat × Nat × Nat) := [(2258688000,98061508291859,98061887478332),(2258758656,98061928001251,98062307187979)]
theorem point_links_checked17202 : (cuts17202.take 2).map (fun c => (2258632705-1+2*2^9*c.k,98061189139292+c.lower,98061568325569+c.upper)) = pointBounds17202 := by
 decide +kernel
def cuts17203 : List PrefixCut := [⟨64,380318130,380318365⟩,
⟨128,758506850,758507322⟩]
theorem checked17203 : checkPrefixCuts (2^48) 2258763777 9 Manual.Count131072.C017203.packed 128 cuts17203 = true := by
 decide +kernel
def pointBounds17203 : List (Nat × Nat × Nat) := [(2258829312,98062335360776,98062714547755)]
theorem point_links_checked17203 : (cuts17203.take 1).map (fun c => (2258763777-1+2*2^9*c.k,98061955042646+c.lower,98062334229390+c.upper)) = pointBounds17203 := by
 decide +kernel
def cuts17204 : List PrefixCut := [⟨5,31899443,31899464⟩,
⟨74,444591619,444591898⟩,
⟨128,772418480,772418967⟩]
theorem checked17204 : checkPrefixCuts (2^48) 2258894849 9 Manual.Count131072.C017204.packed 128 cuts17204 = true := by
 decide +kernel
def pointBounds17204 : List (Nat × Nat × Nat) := [(2258899968,98062745448939,98063124636176),(2258970624,98063158141115,98063537328610)]
theorem point_links_checked17204 : (cuts17204.take 2).map (fun c => (2258894849-1+2*2^9*c.k,98062713549496+c.lower,98063092736712+c.upper)) = pointBounds17204 := by
 decide +kernel
def cuts17205 : List PrefixCut := [⟨15,87593576,87593631⟩,
⟨84,492285677,492285990⟩,
⟨128,755802254,755802729⟩]
theorem checked17205 : checkPrefixCuts (2^48) 2259025921 9 Manual.Count131072.C017205.packed 128 cuts17205 = true := by
 decide +kernel
def pointBounds17205 : List (Nat × Nat × Nat) := [(2259041280,98063573561552,98063952749310),(2259111936,98063978253653,98064357441669)]
theorem point_links_checked17205 : (cuts17205.take 2).map (fun c => (2259025921-1+2*2^9*c.k,98063485967976+c.lower,98063865155679+c.upper)) = pointBounds17205 := by
 decide +kernel
def cuts17206 : List PrefixCut := [⟨25,148140112,148140202⟩,
⟨94,562151122,562151468⟩,
⟨128,765102736,765103210⟩]
theorem checked17206 : checkPrefixCuts (2^48) 2259156993 9 Manual.Count131072.C017206.packed 128 cuts17206 = true := by
 decide +kernel
def pointBounds17206 : List (Nat × Nat × Nat) := [(2259182592,98064389910342,98064769098610),(2259253248,98064803921352,98065183109876)]
theorem point_links_checked17206 : (cuts17206.take 2).map (fun c => (2259156993-1+2*2^9*c.k,98064241770230+c.lower,98064620958408+c.upper)) = pointBounds17206 := by
 decide +kernel
def cuts17207 : List PrefixCut := [⟨35,206935114,206935246⟩,
⟨104,607839139,607839522⟩,
⟨128,747866032,747866499⟩]
theorem checked17207 : checkPrefixCuts (2^48) 2259288065 9 Manual.Count131072.C017207.packed 128 cuts17207 = true := by
 decide +kernel
def pointBounds17207 : List (Nat × Nat × Nat) := [(2259323904,98065213808080,98065592996864),(2259394560,98065614712105,98065993901140)]
theorem point_links_checked17207 : (cuts17207.take 2).map (fun c => (2259288065-1+2*2^9*c.k,98065006872966+c.lower,98065386061618+c.upper)) = pointBounds17207 := by
 decide +kernel
def cuts17208 : List PrefixCut := [⟨45,266470536,266470698⟩,
⟨114,667474100,667474517⟩,
⟨128,750314219,750314687⟩]
theorem checked17208 : checkPrefixCuts (2^48) 2259419137 9 Manual.Count131072.C017208.packed 128 cuts17208 = true := by
 decide +kernel
def pointBounds17208 : List (Nat × Nat × Nat) := [(2259465216,98066021209534,98066400398815),(2259535872,98066422213098,98066801402634)]
theorem point_links_checked17208 : (cuts17208.take 2).map (fun c => (2259419137-1+2*2^9*c.k,98065754738998+c.lower,98066133928117+c.upper)) = pointBounds17208 := by
 decide +kernel
def cuts17209 : List PrefixCut := [⟨55,325251405,325251602⟩,
⟨124,739932149,739932602⟩,
⟨128,764969532,764970001⟩]
theorem checked17209 : checkPrefixCuts (2^48) 2259550209 9 Manual.Count131072.C017209.packed 128 cuts17209 = true := by
 decide +kernel
def pointBounds17209 : List (Nat × Nat × Nat) := [(2259606528,98066830304622,98067209494406),(2259677184,98067244985366,98067624175406)]
theorem point_links_checked17209 : (cuts17209.take 2).map (fun c => (2259550209-1+2*2^9*c.k,98066505053217+c.lower,98066884242804+c.upper)) = pointBounds17209 := by
 decide +kernel
def cuts17210 : List PrefixCut := [⟨65,386142598,386142838⟩,
⟨128,761811101,761811572⟩]
theorem checked17210 : checkPrefixCuts (2^48) 2259681281 9 Manual.Count131072.C017210.packed 128 cuts17210 = true := by
 decide +kernel
def pointBounds17210 : List (Nat × Nat × Nat) := [(2259747840,98067656165347,98068035355643)]
theorem point_links_checked17210 : (cuts17210.take 1).map (fun c => (2259681281-1+2*2^9*c.k,98067270022749+c.lower,98067649212805+c.upper)) = pointBounds17210 := by
 decide +kernel
def cuts17211 : List PrefixCut := [⟨6,35623182,35623204⟩,
⟨75,439553254,439553529⟩,
⟨128,759898462,759898936⟩]
theorem checked17211 : checkPrefixCuts (2^48) 2259812353 9 Manual.Count131072.C017211.packed 128 cuts17211 = true := by
 decide +kernel
def pointBounds17211 : List (Nat × Nat × Nat) := [(2259818496,98068067457032,98068446647581),(2259889152,98068471387104,98068850577906)]
theorem point_links_checked17211 : (cuts17211.take 2).map (fun c => (2259812353-1+2*2^9*c.k,98068031833850+c.lower,98068411024377+c.upper)) = pointBounds17211 := by
 decide +kernel
def cuts17212 : List PrefixCut := [⟨16,97397377,97397435⟩,
⟨85,506657703,506658021⟩,
⟨128,759605571,759606046⟩]
theorem checked17212 : checkPrefixCuts (2^48) 2259943425 9 Manual.Count131072.C017212.packed 128 cuts17212 = true := by
 decide +kernel
def pointBounds17212 : List (Nat × Nat × Nat) := [(2259959808,98068889129689,98069268320748),(2260030464,98069298390015,98069677581334)]
theorem point_links_checked17212 : (cuts17212.take 2).map (fun c => (2259943425-1+2*2^9*c.k,98068791732312+c.lower,98069170923313+c.upper)) = pointBounds17212 := by
 decide +kernel
def cuts17213 : List PrefixCut := [⟨26,151567101,151567195⟩,
⟨95,560926486,560926832⟩,
⟨128,757070686,757071159⟩]
theorem checked17213 : checkPrefixCuts (2^48) 2260074497 9 Manual.Count131072.C017213.packed 128 cuts17213 = true := by
 decide +kernel
def pointBounds17213 : List (Nat × Nat × Nat) := [(2260101120,98069702904984,98070082096554),(2260171776,98070112264369,98070491456191)]
theorem point_links_checked17213 : (cuts17213.take 2).map (fun c => (2260074497-1+2*2^9*c.k,98069551337883+c.lower,98069930529359+c.upper)) = pointBounds17213 := by
 decide +kernel
def cuts17214 : List PrefixCut := [⟨36,220425311,220425448⟩,
⟨105,623407968,623408357⟩,
⟨128,760264795,760265269⟩]
theorem checked17214 : checkPrefixCuts (2^48) 2260205569 9 Manual.Count131072.C017214.packed 128 cuts17214 = true := by
 decide +kernel
def pointBounds17214 : List (Nat × Nat × Nat) := [(2260242432,98070528833880,98070908025966),(2260313088,98070931816537,98071311008875)]
theorem point_links_checked17214 : (cuts17214.take 2).map (fun c => (2260205569-1+2*2^9*c.k,98070308408569+c.lower,98070687600518+c.upper)) = pointBounds17214 := by
 decide +kernel
def cuts17215 : List PrefixCut := [⟨46,270596222,270596391⟩,
⟨115,681398676,681399098⟩,
⟨128,760718560,760719032⟩]
theorem checked17215 : checkPrefixCuts (2^48) 2260336641 9 Manual.Count131072.C017215.packed 128 cuts17215 = true := by
 decide +kernel
def pointBounds17215 : List (Nat × Nat × Nat) := [(2260383744,98071339269586,98071718462178),(2260454400,98071750072040,98072129264885)]
theorem point_links_checked17215 : (cuts17215.take 2).map (fun c => (2260336641-1+2*2^9*c.k,98071068673364+c.lower,98071447865787+c.upper)) = pointBounds17215 := by
 decide +kernel
def cuts17216 : List PrefixCut := [⟨56,326115381,326115581⟩,
⟨125,736767588,736768047⟩,
⟨128,753950452,753950921⟩]
theorem checked17216 : checkPrefixCuts (2^48) 2260467713 9 Manual.Count131072.C017216.packed 128 cuts17216 = true := by
 decide +kernel
def pointBounds17216 : List (Nat × Nat × Nat) := [(2260525056,98072155507305,98072534700400),(2260595712,98072566159512,98072945352866)]
theorem point_links_checked17216 : (cuts17216.take 2).map (fun c => (2260467713-1+2*2^9*c.k,98071829391924+c.lower,98072208584819+c.upper)) = pointBounds17216 := by
 decide +kernel
def cuts17217 : List PrefixCut := [⟨66,391339750,391339997⟩,
⟨128,761501924,761502403⟩]
theorem checked17217 : checkPrefixCuts (2^48) 2260598785 9 Manual.Count131072.C017217.packed 128 cuts17217 = true := by
 decide +kernel
def pointBounds17217 : List (Nat × Nat × Nat) := [(2260666368,98072974682126,98073353875737)]
theorem point_links_checked17217 : (cuts17217.take 1).map (fun c => (2260598785-1+2*2^9*c.k,98072583342376+c.lower,98072962535740+c.upper)) = pointBounds17217 := by
 decide +kernel
def cuts17218 : List PrefixCut := [⟨7,39094887,39094911⟩,
⟨76,450331180,450331467⟩,
⟨128,760586380,760586860⟩]
theorem checked17218 : checkPrefixCuts (2^48) 2260729857 9 Manual.Count131072.C017218.packed 128 cuts17218 = true := by
 decide +kernel
def pointBounds17218 : List (Nat × Nat × Nat) := [(2260737024,98073383939187,98073763133054),(2260807680,98073795175480,98074174369610)]
theorem point_links_checked17218 : (cuts17218.take 2).map (fun c => (2260729857-1+2*2^9*c.k,98073344844300+c.lower,98073724038143+c.upper)) = pointBounds17218 := by
 decide +kernel
def cuts17219 : List PrefixCut := [⟨17,97482327,97482390⟩,
⟨86,506203011,506203330⟩,
⟨128,754317471,754317943⟩]
theorem checked17219 : checkPrefixCuts (2^48) 2260860929 9 Manual.Count131072.C017219.packed 128 cuts17219 = true := by
 decide +kernel
def pointBounds17219 : List (Nat × Nat × Nat) := [(2260878336,98074202913007,98074582107393),(2260948992,98074611633691,98074990828333)]
theorem point_links_checked17219 : (cuts17219.take 2).map (fun c => (2260860929-1+2*2^9*c.k,98074105430680+c.lower,98074484625003+c.upper)) = pointBounds17219 := by
 decide +kernel
def cuts17220 : List PrefixCut := [⟨27,158477055,158477151⟩,
⟨96,569786425,569786774⟩,
⟨128,765602043,765602513⟩]
theorem checked17220 : checkPrefixCuts (2^48) 2260992001 9 Manual.Count131072.C017220.packed 128 cuts17220 = true := by
 decide +kernel
def pointBounds17220 : List (Nat × Nat × Nat) := [(2261019648,98075018225206,98075397420097),(2261090304,98075429534576,98075808729720)]
theorem point_links_checked17220 : (cuts17220.take 2).map (fun c => (2260992001-1+2*2^9*c.k,98074859748151+c.lower,98075238942946+c.upper)) = pointBounds17220 := by
 decide +kernel
def cuts17221 : List PrefixCut := [⟨38,222327478,222327617⟩,
⟨108,637718722,637719121⟩,
⟨128,754230028,754230500⟩]
theorem checked17221 : checkPrefixCuts (2^48) 2261123073 9 Manual.Count131072.C017221.packed 128 cuts17221 = true := by
 decide +kernel
def pointBounds17221 : List (Nat × Nat × Nat) := [(2261161984,98075847677672,98076226873076),(2261233664,98076263068916,98076642264580)]
theorem point_links_checked17221 : (cuts17221.take 2).map (fun c => (2261123073-1+2*2^9*c.k,98075625350194+c.lower,98076004545459+c.upper)) = pointBounds17221 := by
 decide +kernel
def cuts17222 : List PrefixCut := [⟨50,298617706,298617890⟩,
⟨120,713982609,713983053⟩,
⟨128,764144159,764144635⟩]
theorem checked17222 : checkPrefixCuts (2^48) 2261254145 9 Manual.Count131072.C017222.packed 128 cuts17222 = true := by
 decide +kernel
def pointBounds17222 : List (Nat × Nat × Nat) := [(2261305344,98076678197928,98077057393849),(2261377024,98077093562831,98077472759012)]
theorem point_links_checked17222 : (cuts17222.take 2).map (fun c => (2261254145-1+2*2^9*c.k,98076379580222+c.lower,98076758775959+c.upper)) = pointBounds17222 := by
 decide +kernel
def cuts17223 : List PrefixCut := [⟨62,372409371,372409597⟩,
⟨128,763602106,763602575⟩]
theorem checked17223 : checkPrefixCuts (2^48) 2261385217 9 Manual.Count131072.C017223.packed 128 cuts17223 = true := by
 decide +kernel
def pointBounds17223 : List (Nat × Nat × Nat) := [(2261448704,98077516133752,98077895330191)]
theorem point_links_checked17223 : (cuts17223.take 1).map (fun c => (2261385217-1+2*2^9*c.k,98077143724381+c.lower,98077522920594+c.upper)) = pointBounds17223 := by
 decide +kernel
def cuts17224 : List PrefixCut := [⟨4,24145783,24145798⟩,
⟨74,437728791,437729063⟩,
⟨128,758330600,758331074⟩]
theorem checked17224 : checkPrefixCuts (2^48) 2261516289 9 Manual.Count131072.C017224.packed 128 cuts17224 = true := by
 decide +kernel
def pointBounds17224 : List (Nat × Nat × Nat) := [(2261520384,98077931472270,98078310668967),(2261592064,98078345055278,98078724252232)]
theorem point_links_checked17224 : (cuts17224.take 2).map (fun c => (2261516289-1+2*2^9*c.k,98077907326487+c.lower,98078286523169+c.upper)) = pointBounds17224 := by
 decide +kernel
def cuts17225 : List PrefixCut := [⟨16,93590349,93590408⟩,
⟨86,511751804,511752122⟩,
⟨128,758411036,758411508⟩]
theorem checked17225 : checkPrefixCuts (2^48) 2261647361 9 Manual.Count131072.C017225.packed 128 cuts17225 = true := by
 decide +kernel
def pointBounds17225 : List (Nat × Nat × Nat) := [(2261663744,98078759247436,98079138444651),(2261735424,98079177408891,98079556606365)]
theorem point_links_checked17225 : (cuts17225.take 2).map (fun c => (2261647361-1+2*2^9*c.k,98078665657087+c.lower,98079044854243+c.upper)) = pointBounds17225 := by
 decide +kernel
def cuts17226 : List PrefixCut := [⟨28,165515451,165515553⟩,
⟨98,576308212,576308577⟩,
⟨128,759113667,759114143⟩]
theorem checked17226 : checkPrefixCuts (2^48) 2261778433 9 Manual.Count131072.C017226.packed 128 cuts17226 = true := by
 decide +kernel
def pointBounds17226 : List (Nat × Nat × Nat) := [(2261807104,98079589583574,98079968781304),(2261878784,98080000376335,98080379574328)]
theorem point_links_checked17226 : (cuts17226.take 2).map (fun c => (2261778433-1+2*2^9*c.k,98079424068123+c.lower,98079803265751+c.upper)) = pointBounds17226 := by
 decide +kernel
def cuts17227 : List PrefixCut := [⟨40,236062890,236063040⟩,
⟨110,651184815,651185224⟩,
⟨128,763424798,763425275⟩]
theorem checked17227 : checkPrefixCuts (2^48) 2261909505 9 Manual.Count131072.C017227.packed 128 cuts17227 = true := by
 decide +kernel
def pointBounds17227 : List (Nat × Nat × Nat) := [(2261950464,98080419244680,98080798442934),(2262022144,98080834366605,98081213565118)]
theorem point_links_checked17227 : (cuts17227.take 2).map (fun c => (2261909505-1+2*2^9*c.k,98080183181790+c.lower,98080562379894+c.upper)) = pointBounds17227 := by
 decide +kernel
def cuts17228 : List PrefixCut := [⟨52,302868896,302869083⟩,
⟨122,718959978,718960426⟩,
⟨128,753052977,753053447⟩]
theorem checked17228 : checkPrefixCuts (2^48) 2262040577 9 Manual.Count131072.C017228.packed 128 cuts17228 = true := by
 decide +kernel
def pointBounds17228 : List (Nat × Nat × Nat) := [(2262093824,98081249475484,98081628674252),(2262165504,98081665566566,98082044765595)]
theorem point_links_checked17228 : (cuts17228.take 2).map (fun c => (2262040577-1+2*2^9*c.k,98080946606588+c.lower,98081325805169+c.upper)) = pointBounds17228 := by
 decide +kernel
def cuts17229 : List PrefixCut := [⟨64,387832963,387833203⟩,
⟨128,760723955,760724421⟩]
theorem checked17229 : checkPrefixCuts (2^48) 2262171649 9 Manual.Count131072.C017229.packed 128 cuts17229 = true := by
 decide +kernel
def pointBounds17229 : List (Nat × Nat × Nat) := [(2262237184,98082087492528,98082466691819)]
theorem point_links_checked17229 : (cuts17229.take 1).map (fun c => (2262171649-1+2*2^9*c.k,98081699659565+c.lower,98082078858616+c.upper)) = pointBounds17229 := by
 decide +kernel
def cuts17230 : List PrefixCut := [⟨6,33095579,33095601⟩,
⟨76,453626149,453626432⟩,
⟨128,764785274,764785754⟩]
theorem checked17230 : checkPrefixCuts (2^48) 2262302721 9 Manual.Count131072.C017230.packed 128 cuts17230 = true := by
 decide +kernel
def pointBounds17230 : List (Nat × Nat × Nat) := [(2262308864,98082493479099,98082872678638),(2262380544,98082914009669,98083293209469)]
theorem point_links_checked17230 : (cuts17230.take 2).map (fun c => (2262302721-1+2*2^9*c.k,98082460383520+c.lower,98082839583037+c.upper)) = pointBounds17230 := by
 decide +kernel
def cuts17231 : List PrefixCut := [⟨18,105128067,105128131⟩,
⟨88,522148502,522148831⟩,
⟨128,759142589,759143064⟩]
theorem checked17231 : checkPrefixCuts (2^48) 2262433793 9 Manual.Count131072.C017231.packed 128 cuts17231 = true := by
 decide +kernel
def pointBounds17231 : List (Nat × Nat × Nat) := [(2262452224,98083330296861,98083709496922),(2262523904,98083747317296,98084126517622)]
theorem point_links_checked17231 : (cuts17231.take 2).map (fun c => (2262433793-1+2*2^9*c.k,98083225168794+c.lower,98083604368791+c.upper)) = pointBounds17231 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000225
