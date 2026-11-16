import PlattAssemblyKernel
import PlattCertificates.Count131072.C012304
import PlattCertificates.Count131072.C012305
import PlattCertificates.Count131072.C012306
import PlattCertificates.Count131072.C012307
import PlattCertificates.Count131072.C012308
import PlattCertificates.Count131072.C012309
import PlattCertificates.Count131072.C012310
import PlattCertificates.Count131072.C012311
import PlattCertificates.Count131072.C012312
import PlattCertificates.Count131072.C012313
import PlattCertificates.Count131072.C012314
import PlattCertificates.Count131072.C012315
import PlattCertificates.Count131072.C012316
import PlattCertificates.Count131072.C012317
import PlattCertificates.Count131072.C012318
import PlattCertificates.Count131072.C012319
import PlattCertificates.Count131072.C012320
import PlattCertificates.Count131072.C012321
import PlattCertificates.Count131072.C012322
import PlattCertificates.Count131072.C012323
import PlattCertificates.Count131072.C012324
import PlattCertificates.Count131072.C012325
import PlattCertificates.Count131072.C012326
import PlattCertificates.Count131072.C012327
import PlattCertificates.Count131072.C012328
import PlattCertificates.Count131072.C012329
import PlattCertificates.Count131072.C012330
import PlattCertificates.Count131072.C012331
import PlattCertificates.Count131072.C012332
import PlattCertificates.Count131072.C012333
import PlattCertificates.Count131072.C012334
import PlattCertificates.Count131072.C012335
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000072
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12304 : List PrefixCut := [⟨36,299293075,299293298⟩,
⟨86,718013344,718013883⟩,
⟨128,1070215645,1070216445⟩]
theorem checked12304 : checkPrefixCuts (2^48) 1616642049 9 Manual.Count131072.C012304.packed 128 cuts12304 = true := by
 decide +kernel
def pointBounds12304 : List (Nat × Nat × Nat) := [(1616678912,93657078954460,93657455142130),(1616730112,93657497674729,93657873862715)]
theorem point_links_checked12304 : (cuts12304.take 2).map (fun c => (1616642049-1+2*2^9*c.k,93656779661385+c.lower,93657155848832+c.upper)) = pointBounds12304 := by
 decide +kernel
def cuts12305 : List PrefixCut := [⟨8,66330679,66330727⟩,
⟨58,479279410,479279769⟩,
⟨108,901267689,901268367⟩,
⟨128,1070477026,1070477828⟩]
theorem checked12305 : checkPrefixCuts (2^48) 1616773121 9 Manual.Count131072.C012305.packed 128 cuts12305 = true := by
 decide +kernel
def pointBounds12305 : List (Nat × Nat × Nat) := [(1616781312,93657916207709,93658292396004),(1616832512,93658329156440,93658705345046),(1616883712,93658751144719,93659127333644)]
theorem point_links_checked12305 : (cuts12305.take 3).map (fun c => (1616773121-1+2*2^9*c.k,93657849877030+c.lower,93658226065277+c.upper)) = pointBounds12305 := by
 decide +kernel
def cuts12306 : List PrefixCut := [⟨30,252591422,252591612⟩,
⟨80,677512206,677512718⟩,
⟨128,1090408813,1090409640⟩]
theorem checked12306 : checkPrefixCuts (2^48) 1616904193 9 Manual.Count131072.C012306.packed 128 cuts12306 = true := by
 decide +kernel
def pointBounds12306 : List (Nat × Nat × Nat) := [(1616934912,93659172945478,93659549134717),(1616986112,93659597866262,93659974055823)]
theorem point_links_checked12306 : (cuts12306.take 2).map (fun c => (1616904193-1+2*2^9*c.k,93658920354056+c.lower,93659296543105+c.upper)) = pointBounds12306 := by
 decide +kernel
def cuts12307 : List PrefixCut := [⟨2,15492085,15492097⟩,
⟨52,425416313,425416638⟩,
⟨102,847337749,847338388⟩,
⟨128,1072565964,1072566771⟩]
theorem checked12307 : checkPrefixCuts (2^48) 1617035265 9 Manual.Count131072.C012307.packed 128 cuts12307 = true := by
 decide +kernel
def pointBounds12307 : List (Nat × Nat × Nat) := [(1617037312,93660026254954,93660402444842),(1617088512,93660436179182,93660812369383),(1617139712,93660858100618,93661234291133)]
theorem point_links_checked12307 : (cuts12307.take 3).map (fun c => (1617035265-1+2*2^9*c.k,93660010762869+c.lower,93660386952745+c.upper)) = pointBounds12307 := by
 decide +kernel
def cuts12308 : List PrefixCut := [⟨24,205208567,205208722⟩,
⟨74,618923027,618923501⟩,
⟨124,1047069953,1047070750⟩,
⟨128,1077875119,1077875938⟩]
theorem checked12308 : checkPrefixCuts (2^48) 1617166337 9 Manual.Count131072.C012308.packed 128 cuts12308 = true := by
 decide +kernel
def pointBounds12308 : List (Nat × Nat × Nat) := [(1617190912,93661288537400,93661664728238),(1617242112,93661702251860,93662078443017),(1617293312,93662130398786,93662506590266)]
theorem point_links_checked12308 : (cuts12308.take 3).map (fun c => (1617166337-1+2*2^9*c.k,93661083328833+c.lower,93661459519516+c.upper)) = pointBounds12308 := by
 decide +kernel
def cuts12309 : List PrefixCut := [⟨46,390540579,390540875⟩,
⟨96,805259840,805260451⟩,
⟨128,1068738082,1068738891⟩]
theorem checked12309 : checkPrefixCuts (2^48) 1617297409 9 Manual.Count131072.C012309.packed 128 cuts12309 = true := by
 decide +kernel
def pointBounds12309 : List (Nat × Nat × Nat) := [(1617344512,93662551744531,93662927936329),(1617395712,93662966463792,93663342655905)]
theorem point_links_checked12309 : (cuts12309.take 2).map (fun c => (1617297409-1+2*2^9*c.k,93662161203952+c.lower,93662537395454+c.upper)) = pointBounds12309 := by
 decide +kernel
def cuts12310 : List PrefixCut := [⟨18,148443458,148443569⟩,
⟨68,570271483,570271909⟩,
⟨118,990519931,990520672⟩,
⟨128,1075090058,1075090861⟩]
theorem checked12310 : checkPrefixCuts (2^48) 1617428481 9 Manual.Count131072.C012310.packed 128 cuts12310 = true := by
 decide +kernel
def pointBounds12310 : List (Nat × Nat × Nat) := [(1617446912,93663378385492,93663754577914),(1617498112,93663800213517,93664176406254),(1617549312,93664220461965,93664596655017)]
theorem point_links_checked12310 : (cuts12310.take 3).map (fun c => (1617428481-1+2*2^9*c.k,93663229942034+c.lower,93663606134345+c.upper)) = pointBounds12310 := by
 decide +kernel
def cuts12311 : List PrefixCut := [⟨40,328704599,328704848⟩,
⟨90,748056359,748056924⟩,
⟨128,1062996431,1062997228⟩]
theorem checked12311 : checkPrefixCuts (2^48) 1617559553 9 Manual.Count131072.C012311.packed 128 cuts12311 = true := by
 decide +kernel
def pointBounds12311 : List (Nat × Nat × Nat) := [(1617600512,93664633736691,93665009930054),(1617651712,93665053088451,93665429282130)]
theorem point_links_checked12311 : (cuts12311.take 2).map (fun c => (1617559553-1+2*2^9*c.k,93664305032092+c.lower,93664681225206+c.upper)) = pointBounds12311 := by
 decide +kernel
def cuts12312 : List PrefixCut := [⟨12,98134483,98134558⟩,
⟨62,518851681,518852070⟩,
⟨112,943731297,943732008⟩,
⟨128,1074915790,1074916601⟩]
theorem checked12312 : checkPrefixCuts (2^48) 1617690625 9 Manual.Count131072.C012312.packed 128 cuts12312 = true := by
 decide +kernel
def pointBounds12312 : List (Nat × Nat × Nat) := [(1617702912,93665466163006,93665842356992),(1617754112,93665886880204,93666263074504),(1617805312,93666311759820,93666687954442)]
theorem point_links_checked12312 : (cuts12312.take 3).map (fun c => (1617690625-1+2*2^9*c.k,93665368028523+c.lower,93665744222434+c.upper)) = pointBounds12312 := by
 decide +kernel
def cuts12313 : List PrefixCut := [⟨34,285330477,285330689⟩,
⟨84,702702177,702702703⟩,
⟨128,1062476631,1062477429⟩]
theorem checked12313 : checkPrefixCuts (2^48) 1617821697 9 Manual.Count131072.C012313.packed 128 cuts12313 = true := by
 decide +kernel
def pointBounds12313 : List (Nat × Nat × Nat) := [(1617856512,93666728274790,93667104469724),(1617907712,93667145646490,93667521841738)]
theorem point_links_checked12313 : (cuts12313.take 2).map (fun c => (1617821697-1+2*2^9*c.k,93666442944313+c.lower,93666819139035+c.upper)) = pointBounds12313 := by
 decide +kernel
def cuts12314 : List PrefixCut := [⟨6,46623813,46623849⟩,
⟨56,477712479,477712841⟩,
⟨106,899741541,899742221⟩,
⟨128,1088484767,1088485591⟩]
theorem checked12314 : checkPrefixCuts (2^48) 1617952769 9 Manual.Count131072.C012314.packed 128 cuts12314 = true := by
 decide +kernel
def pointBounds12314 : List (Nat × Nat × Nat) := [(1617958912,93667552044757,93667928240313),(1618010112,93667983133423,93668359329305),(1618061312,93668405162485,93668781358685)]
theorem point_links_checked12314 : (cuts12314.take 3).map (fun c => (1617952769-1+2*2^9*c.k,93667505420944+c.lower,93667881616464+c.upper)) = pointBounds12314 := by
 decide +kernel
def cuts12315 : List PrefixCut := [⟨28,235881813,235881992⟩,
⟨78,650926161,650926650⟩,
⟨128,1077089901,1077090711⟩]
theorem checked12315 : checkPrefixCuts (2^48) 1618083841 9 Manual.Count131072.C012315.packed 128 cuts12315 = true := by
 decide +kernel
def pointBounds12315 : List (Nat × Nat × Nat) := [(1618112512,93668829787524,93669205984047),(1618163712,93669244831872,93669621028705),(1618214912,93669670995612,93670047192766)]
theorem point_links_checked12315 : (cuts12315.take 3).map (fun c => (1618083841-1+2*2^9*c.k,93668593905711+c.lower,93668970102055+c.upper)) = pointBounds12315 := by
 decide +kernel
def cuts12316 : List PrefixCut := [⟨50,418496829,418497143⟩,
⟨100,836458695,836459325⟩,
⟨128,1068306102,1068306908⟩]
theorem checked12316 : checkPrefixCuts (2^48) 1618214913 9 Manual.Count131072.C012316.packed 128 cuts12316 = true := by
 decide +kernel
def pointBounds12316 : List (Nat × Nat × Nat) := [(1618266112,93670089492441,93670465689909),(1618317312,93670507454307,93670883652091)]
theorem point_links_checked12316 : (cuts12316.take 2).map (fun c => (1618214913-1+2*2^9*c.k,93669670995612+c.lower,93670047192766+c.upper)) = pointBounds12316 := by
 decide +kernel
def cuts12317 : List PrefixCut := [⟨22,187666480,187666617⟩,
⟨72,602471245,602471696⟩,
⟨122,1028567448,1028568218⟩,
⟨128,1076915468,1076916275⟩]
theorem checked12317 : checkPrefixCuts (2^48) 1618345985 9 Manual.Count131072.C012317.packed 128 cuts12317 = true := by
 decide +kernel
def pointBounds12317 : List (Nat × Nat × Nat) := [(1618368512,93670926968194,93671303166291),(1618419712,93671341772959,93671717971370),(1618470912,93671767869162,93672144067892)]
theorem point_links_checked12317 : (cuts12317.take 3).map (fun c => (1618345985-1+2*2^9*c.k,93670739301714+c.lower,93671115499674+c.upper)) = pointBounds12317 := by
 decide +kernel
def cuts12318 : List PrefixCut := [⟨44,362082725,362082996⟩,
⟨94,774413479,774414064⟩,
⟨128,1062741693,1062742494⟩]
theorem checked12318 : checkPrefixCuts (2^48) 1618477057 9 Manual.Count131072.C012318.packed 128 cuts12318 = true := by
 decide +kernel
def pointBounds12318 : List (Nat × Nat × Nat) := [(1618522112,93672178299907,93672554498945),(1618573312,93672590630661,93672966830013)]
theorem point_links_checked12318 : (cuts12318.take 2).map (fun c => (1618477057-1+2*2^9*c.k,93671816217182+c.lower,93672192415949+c.upper)) = pointBounds12318 := by
 decide +kernel
def cuts12319 : List PrefixCut := [⟨16,135119106,135119208⟩,
⟨66,559770197,559770615⟩,
⟨116,983712415,983713151⟩,
⟨128,1085261794,1085262605⟩]
theorem checked12319 : checkPrefixCuts (2^48) 1618608129 9 Manual.Count131072.C012319.packed 128 cuts12319 = true := by
 decide +kernel
def pointBounds12319 : List (Nat × Nat × Nat) := [(1618624512,93673014077981,93673390277651),(1618675712,93673438729072,93673814929058),(1618726912,93673862671290,93674238871594)]
theorem point_links_checked12319 : (cuts12319.take 3).map (fun c => (1618608129-1+2*2^9*c.k,93672878958875+c.lower,93673255158443+c.upper)) = pointBounds12319 := by
 decide +kernel
def cuts12320 : List PrefixCut := [⟨38,320814393,320814633⟩,
⟨88,733949292,733949845⟩,
⟨128,1071611415,1071612221⟩]
theorem checked12320 : checkPrefixCuts (2^48) 1618739201 9 Manual.Count131072.C012320.packed 128 cuts12320 = true := by
 decide +kernel
def pointBounds12320 : List (Nat × Nat × Nat) := [(1618778112,93674285035062,93674661235681),(1618829312,93674698169961,93675074370893)]
theorem point_links_checked12320 : (cuts12320.take 2).map (fun c => (1618739201-1+2*2^9*c.k,93673964220669+c.lower,93674340421048+c.upper)) = pointBounds12320 := by
 decide +kernel
def cuts12321 : List PrefixCut := [⟨10,81545322,81545383⟩,
⟨60,501782607,501782984⟩,
⟨110,917660101,917660792⟩,
⟨128,1074827833,1074828641⟩]
theorem checked12321 : checkPrefixCuts (2^48) 1618870273 9 Manual.Count131072.C012321.packed 128 cuts12321 = true := by
 decide +kernel
def pointBounds12321 : List (Nat × Nat × Nat) := [(1618880512,93675117377406,93675493578652),(1618931712,93675537614691,93675913816253),(1618982912,93675953492185,93676329694061)]
theorem point_links_checked12321 : (cuts12321.take 3).map (fun c => (1618870273-1+2*2^9*c.k,93675035832084+c.lower,93675412033269+c.upper)) = pointBounds12321 := by
 decide +kernel
def cuts12322 : List PrefixCut := [⟨32,272083594,272083797⟩,
⟨82,688108584,688109099⟩,
⟨128,1065005709,1065006504⟩]
theorem checked12322 : checkPrefixCuts (2^48) 1619001345 9 Manual.Count131072.C012322.packed 128 cuts12322 = true := by
 decide +kernel
def pointBounds12322 : List (Nat × Nat × Nat) := [(1619034112,93676382743511,93676758945707),(1619085312,93676798768501,93677174971009)]
theorem point_links_checked12322 : (cuts12322.take 2).map (fun c => (1619001345-1+2*2^9*c.k,93676110659917+c.lower,93676486861910+c.upper)) = pointBounds12322 := by
 decide +kernel
def cuts12323 : List PrefixCut := [⟨4,34594716,34594742⟩,
⟨54,451114924,451115262⟩,
⟨104,872837096,872837748⟩,
⟨128,1077261488,1077262295⟩]
theorem checked12323 : checkPrefixCuts (2^48) 1619132417 9 Manual.Count131072.C012323.packed 128 cuts12323 = true := by
 decide +kernel
def pointBounds12323 : List (Nat × Nat × Nat) := [(1619136512,93677210260342,93677586463156),(1619187712,93677626780550,93678002983676),(1619238912,93678048502722,93678424706162)]
theorem point_links_checked12323 : (cuts12323.take 3).map (fun c => (1619132417-1+2*2^9*c.k,93677175665626+c.lower,93677551868414+c.upper)) = pointBounds12323 := by
 decide +kernel
def cuts12324 : List PrefixCut := [⟨26,214677017,214677179⟩,
⟨76,636024796,636025273⟩,
⟨126,1049885159,1049885946⟩,
⟨128,1067266658,1067267458⟩]
theorem checked12324 : checkPrefixCuts (2^48) 1619263489 9 Manual.Count131072.C012324.packed 128 cuts12324 = true := by
 decide +kernel
def pointBounds12324 : List (Nat × Nat × Nat) := [(1619290112,93678467604131,93678843807888),(1619341312,93678888951910,93679265155982),(1619392512,93679302812273,93679679016655)]
theorem point_links_checked12324 : (cuts12324.take 3).map (fun c => (1619263489-1+2*2^9*c.k,93678252927114+c.lower,93678629130709+c.upper)) = pointBounds12324 := by
 decide +kernel
def cuts12325 : List PrefixCut := [⟨48,404808684,404808987⟩,
⟨98,817600022,817600632⟩,
⟨128,1081258358,1081259165⟩]
theorem checked12325 : checkPrefixCuts (2^48) 1619394561 9 Manual.Count131072.C012325.packed 128 cuts12325 = true := by
 decide +kernel
def pointBounds12325 : List (Nat × Nat × Nat) := [(1619443712,93679725002456,93680101207154),(1619494912,93680137793794,93680513998799)]
theorem point_links_checked12325 : (cuts12325.take 2).map (fun c => (1619394561-1+2*2^9*c.k,93679320193772+c.lower,93679696398167+c.upper)) = pointBounds12325 := by
 decide +kernel
def cuts12326 : List PrefixCut := [⟨20,166500138,166500262⟩,
⟨70,595775947,595776389⟩,
⟨120,1014610766,1014611519⟩,
⟨128,1084473222,1084474028⟩]
theorem checked12326 : checkPrefixCuts (2^48) 1619525633 9 Manual.Count131072.C012326.packed 128 cuts12326 = true := by
 decide +kernel
def pointBounds12326 : List (Nat × Nat × Nat) := [(1619546112,93680567952268,93680944157594),(1619597312,93680997228077,93681373433721),(1619648512,93681416062896,93681792268851)]
theorem point_links_checked12326 : (cuts12326.take 3).map (fun c => (1619525633-1+2*2^9*c.k,93680401452130+c.lower,93680777657332+c.upper)) = pointBounds12326 := by
 decide +kernel
def cuts12327 : List PrefixCut := [⟨42,347742683,347742948⟩,
⟨92,759947320,759947896⟩,
⟨128,1064226752,1064227557⟩]
theorem checked12327 : checkPrefixCuts (2^48) 1619656705 9 Manual.Count131072.C012327.packed 128 cuts12327 = true := by
 decide +kernel
def pointBounds12327 : List (Nat × Nat × Nat) := [(1619699712,93681833668035,93682209874308),(1619750912,93682245872672,93682622079256)]
theorem point_links_checked12327 : (cuts12327.take 2).map (fun c => (1619656705-1+2*2^9*c.k,93681485925352+c.lower,93681862131360+c.upper)) = pointBounds12327 := by
 decide +kernel
def cuts12328 : List PrefixCut := [⟨14,114168163,114168248⟩,
⟨64,526520528,526520925⟩,
⟨114,945984233,945984945⟩,
⟨128,1058754082,1058754879⟩]
theorem checked12328 : checkPrefixCuts (2^48) 1619787777 9 Manual.Count131072.C012328.packed 128 cuts12328 = true := by
 decide +kernel
def pointBounds12328 : List (Nat × Nat × Nat) := [(1619802112,93682664320267,93683040527165),(1619853312,93683076672632,93683452879842),(1619904512,93683496136337,93683872343862)]
theorem point_links_checked12328 : (cuts12328.take 3).map (fun c => (1619787777-1+2*2^9*c.k,93682550152104+c.lower,93682926358917+c.upper)) = pointBounds12328 := by
 decide +kernel
def cuts12329 : List PrefixCut := [⟨36,295560081,295560302⟩,
⟨86,713433431,713433967⟩,
⟨128,1068919525,1068920328⟩]
theorem checked12329 : checkPrefixCuts (2^48) 1619918849 9 Manual.Count131072.C012329.packed 128 cuts12329 = true := by
 decide +kernel
def pointBounds12329 : List (Nat × Nat × Nat) := [(1619955712,93683904466267,93684280674098),(1620006912,93684322339617,93684698547763)]
theorem point_links_checked12329 : (cuts12329.take 2).map (fun c => (1619918849-1+2*2^9*c.k,93683608906186+c.lower,93683985113796+c.upper)) = pointBounds12329 := by
 decide +kernel
def cuts12330 : List PrefixCut := [⟨8,68455188,68455241⟩,
⟨58,479005031,479005395⟩,
⟨108,901529524,901530207⟩,
⟨128,1069354252,1069355061⟩]
theorem checked12330 : checkPrefixCuts (2^48) 1620049921 9 Manual.Count131072.C012330.packed 128 cuts12330 = true := by
 decide +kernel
def pointBounds12330 : List (Nat × Nat × Nat) := [(1620058112,93684746280899,93685122489365),(1620109312,93685156830742,93685533039519),(1620160512,93685579355235,93685955564331)]
theorem point_links_checked12330 : (cuts12330.take 3).map (fun c => (1620049921-1+2*2^9*c.k,93684677825711+c.lower,93685054034124+c.upper)) = pointBounds12330 := by
 decide +kernel
def cuts12331 : List PrefixCut := [⟨30,243915329,243915518⟩,
⟨80,660506639,660507140⟩,
⟨128,1072047090,1072047901⟩]
theorem checked12331 : checkPrefixCuts (2^48) 1620180993 9 Manual.Count131072.C012331.packed 128 cuts12331 = true := by
 decide +kernel
def pointBounds12331 : List (Nat × Nat × Nat) := [(1620211712,93685991095292,93686367304703),(1620262912,93686407686602,93686783896325)]
theorem point_links_checked12331 : (cuts12331.take 2).map (fun c => (1620180993-1+2*2^9*c.k,93685747179963+c.lower,93686123389185+c.upper)) = pointBounds12331 := by
 decide +kernel
def cuts12332 : List PrefixCut := [⟨2,15113323,15113334⟩,
⟨52,440537741,440538069⟩,
⟨102,862648163,862648803⟩,
⟨128,1078214597,1078215400⟩]
theorem checked12332 : checkPrefixCuts (2^48) 1620312065 9 Manual.Count131072.C012332.packed 128 cuts12332 = true := by
 decide +kernel
def pointBounds12332 : List (Nat × Nat × Nat) := [(1620314112,93686834340376,93687210550420),(1620365312,93687259764794,93687635975155),(1620416512,93687681875216,93688058085889)]
theorem point_links_checked12332 : (cuts12332.take 3).map (fun c => (1620312065-1+2*2^9*c.k,93686819227053+c.lower,93687195437086+c.upper)) = pointBounds12332 := by
 decide +kernel
def cuts12333 : List PrefixCut := [⟨24,210178307,210178462⟩,
⟨74,634172718,634173189⟩,
⟨124,1051553520,1051554303⟩,
⟨128,1084033285,1084034091⟩]
theorem checked12333 : checkPrefixCuts (2^48) 1620443137 9 Manual.Count131072.C012333.packed 128 cuts12333 = true := by
 decide +kernel
def pointBounds12333 : List (Nat × Nat × Nat) := [(1620467712,93688107619957,93688483830948),(1620518912,93688531614368,93688907825675),(1620570112,93688948995170,93689325206789)]
theorem point_links_checked12333 : (cuts12333.take 3).map (fun c => (1620443137-1+2*2^9*c.k,93687897441650+c.lower,93688273652486+c.upper)) = pointBounds12333 := by
 decide +kernel
def cuts12334 : List PrefixCut := [⟨46,382108782,382109067⟩,
⟨96,806931418,806932019⟩,
⟨128,1076476674,1076477479⟩]
theorem checked12334 : checkPrefixCuts (2^48) 1620574209 9 Manual.Count131072.C012334.packed 128 cuts12334 = true := by
 decide +kernel
def pointBounds12334 : List (Nat × Nat × Nat) := [(1620621312,93689363583717,93689739795644),(1620672512,93689788406353,93690164618596)]
theorem point_links_checked12334 : (cuts12334.take 2).map (fun c => (1620574209-1+2*2^9*c.k,93688981474935+c.lower,93689357686577+c.upper)) = pointBounds12334 := by
 decide +kernel
def cuts12335 : List PrefixCut := [⟨18,153179876,153179992⟩,
⟨68,575023271,575023704⟩,
⟨118,1001021249,1001022000⟩,
⟨128,1082989154,1082989968⟩]
theorem checked12335 : checkPrefixCuts (2^48) 1620705281 9 Manual.Count131072.C012335.packed 128 cuts12335 = true := by
 decide +kernel
def pointBounds12335 : List (Nat × Nat × Nat) := [(1620723712,93690211131485,93690587344048),(1620774912,93690632974880,93691009187760),(1620826112,93691058972858,93691435186056)]
theorem point_links_checked12335 : (cuts12335.take 3).map (fun c => (1620705281-1+2*2^9*c.k,93690057951609+c.lower,93690434164056+c.upper)) = pointBounds12335 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000072
