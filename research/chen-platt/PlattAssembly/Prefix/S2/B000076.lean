import PlattAssemblyKernel
import PlattCertificates.Count131072.C012432
import PlattCertificates.Count131072.C012433
import PlattCertificates.Count131072.C012434
import PlattCertificates.Count131072.C012435
import PlattCertificates.Count131072.C012436
import PlattCertificates.Count131072.C012437
import PlattCertificates.Count131072.C012438
import PlattCertificates.Count131072.C012439
import PlattCertificates.Count131072.C012440
import PlattCertificates.Count131072.C012441
import PlattCertificates.Count131072.C012442
import PlattCertificates.Count131072.C012443
import PlattCertificates.Count131072.C012444
import PlattCertificates.Count131072.C012445
import PlattCertificates.Count131072.C012446
import PlattCertificates.Count131072.C012447
import PlattCertificates.Count131072.C012448
import PlattCertificates.Count131072.C012449
import PlattCertificates.Count131072.C012450
import PlattCertificates.Count131072.C012451
import PlattCertificates.Count131072.C012452
import PlattCertificates.Count131072.C012453
import PlattCertificates.Count131072.C012454
import PlattCertificates.Count131072.C012455
import PlattCertificates.Count131072.C012456
import PlattCertificates.Count131072.C012457
import PlattCertificates.Count131072.C012458
import PlattCertificates.Count131072.C012459
import PlattCertificates.Count131072.C012460
import PlattCertificates.Count131072.C012461
import PlattCertificates.Count131072.C012462
import PlattCertificates.Count131072.C012463
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000076
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12432 : List PrefixCut := [⟨2,15509014,15509025⟩,
⟨52,431488449,431488771⟩,
⟨102,851073481,851074114⟩,
⟨128,1061981022,1061981812⟩]
theorem checked12432 : checkPrefixCuts (2^48) 1633419265 9 Manual.Count131072.C012432.packed 128 cuts12432 = true := by
 decide +kernel
def pointBounds12432 : List (Nat × Nat × Nat) := [(1633421312,93793847351765,93794223641990),(1633472512,93794263331200,93794639621736),(1633523712,93794682916232,93795059207079)]
theorem point_links_checked12432 : (cuts12432.take 3).map (fun c => (1633419265-1+2*2^9*c.k,93793831842751+c.lower,93794208132965+c.upper)) = pointBounds12432 := by
 decide +kernel
def cuts12433 : List PrefixCut := [⟨24,205735021,205735177⟩,
⟨74,628222906,628223376⟩,
⟨124,1038636703,1038637480⟩,
⟨128,1073095714,1073096517⟩]
theorem checked12433 : checkPrefixCuts (2^48) 1633550337 9 Manual.Count131072.C012433.packed 128 cuts12433 = true := by
 decide +kernel
def pointBounds12433 : List (Nat × Nat × Nat) := [(1633574912,93795099558794,93795475849954),(1633626112,93795522046679,93795898338153),(1633677312,93795932460476,93796308752257)]
theorem point_links_checked12433 : (cuts12433.take 3).map (fun c => (1633550337-1+2*2^9*c.k,93794893823773+c.lower,93795270114777+c.upper)) = pointBounds12433 := by
 decide +kernel
def cuts12434 : List PrefixCut := [⟨46,384384200,384384489⟩,
⟨96,793910799,793911392⟩,
⟨128,1067323522,1067324318⟩]
theorem checked12434 : checkPrefixCuts (2^48) 1633681409 9 Manual.Count131072.C012434.packed 128 cuts12434 = true := by
 decide +kernel
def pointBounds12434 : List (Nat × Nat × Nat) := [(1633728512,93796351303687,93796727595783),(1633779712,93796760830286,93797137122686)]
theorem point_links_checked12434 : (cuts12434.take 2).map (fun c => (1633681409-1+2*2^9*c.k,93795966919487+c.lower,93796343211294+c.upper)) = pointBounds12434 := by
 decide +kernel
def cuts12435 : List PrefixCut := [⟨18,153673810,153673923⟩,
⟨68,569376616,569377040⟩,
⟨118,982999205,982999934⟩,
⟨128,1065687718,1065688509⟩]
theorem checked12435 : checkPrefixCuts (2^48) 1633812481 9 Manual.Count131072.C012435.packed 128 cuts12435 = true := by
 decide +kernel
def pointBounds12435 : List (Nat × Nat × Nat) := [(1633830912,93797187916819,93797564209535),(1633882112,93797603619625,93797979912652),(1633933312,93798017242214,93798393535546)]
theorem point_links_checked12435 : (cuts12435.take 3).map (fun c => (1633812481-1+2*2^9*c.k,93797034243009+c.lower,93797410535612+c.upper)) = pointBounds12435 := by
 decide +kernel
def cuts12436 : List PrefixCut := [⟨40,337294926,337295174⟩,
⟨90,756403993,756404555⟩,
⟨128,1069047576,1069048365⟩]
theorem checked12436 : checkPrefixCuts (2^48) 1633943553 9 Manual.Count131072.C012436.packed 128 cuts12436 = true := by
 decide +kernel
def pointBounds12436 : List (Nat × Nat × Nat) := [(1633984512,93798437225653,93798813519295),(1634035712,93798856334720,93799232628676)]
theorem point_links_checked12436 : (cuts12436.take 2).map (fun c => (1633943553-1+2*2^9*c.k,93798099930727+c.lower,93798476224121+c.upper)) = pointBounds12436 := by
 decide +kernel
def cuts12437 : List PrefixCut := [⟨12,98873055,98873129⟩,
⟨62,513821814,513822199⟩,
⟨112,926518398,926519091⟩,
⟨128,1058110066,1058110858⟩]
theorem checked12437 : checkPrefixCuts (2^48) 1634074625 9 Manual.Count131072.C012437.packed 128 cuts12437 = true := by
 decide +kernel
def pointBounds12437 : List (Nat × Nat × Nat) := [(1634086912,93799267851358,93799644145615),(1634138112,93799682800117,93800059094685),(1634189312,93800095496701,93800471791577)]
theorem point_links_checked12437 : (cuts12437.take 3).map (fun c => (1634074625-1+2*2^9*c.k,93799168978303+c.lower,93799545272486+c.upper)) = pointBounds12437 := by
 decide +kernel
def cuts12438 : List PrefixCut := [⟨34,287636975,287637190⟩,
⟨84,713225151,713225681⟩,
⟨128,1079037714,1079038517⟩]
theorem checked12438 : checkPrefixCuts (2^48) 1634205697 9 Manual.Count131072.C012438.packed 128 cuts12438 = true := by
 decide +kernel
def pointBounds12438 : List (Nat × Nat × Nat) := [(1634240512,93800514725344,93800891020534),(1634291712,93800940313520,93801316609025)]
theorem point_links_checked12438 : (cuts12438.take 2).map (fun c => (1634205697-1+2*2^9*c.k,93800227088369+c.lower,93800603383344+c.upper)) = pointBounds12438 := by
 decide +kernel
def cuts12439 : List PrefixCut := [⟨6,48050893,48050930⟩,
⟨56,457423627,457423970⟩,
⟨106,875911001,875911656⟩,
⟨128,1060523453,1060524244⟩]
theorem checked12439 : checkPrefixCuts (2^48) 1634336769 9 Manual.Count131072.C012439.packed 128 cuts12439 = true := by
 decide +kernel
def pointBounds12439 : List (Nat × Nat × Nat) := [(1634342912,93801354176976,93801730472791),(1634394112,93801763549710,93802139845831),(1634445312,93802182037084,93802558333517)]
theorem point_links_checked12439 : (cuts12439.take 3).map (fun c => (1634336769-1+2*2^9*c.k,93801306126083+c.lower,93801682421861+c.upper)) = pointBounds12439 := by
 decide +kernel
def cuts12440 : List PrefixCut := [⟨28,234378370,234378543⟩,
⟨78,649050975,649051456⟩,
⟨128,1067499015,1067499807⟩]
theorem checked12440 : checkPrefixCuts (2^48) 1634467841 9 Manual.Count131072.C012440.packed 128 cuts12440 = true := by
 decide +kernel
def pointBounds12440 : List (Nat × Nat × Nat) := [(1634496512,93802601027906,93802977324648),(1634547712,93803015700511,93803391997561),(1634598912,93803434148551,93803810445912)]
theorem point_links_checked12440 : (cuts12440.take 3).map (fun c => (1634467841-1+2*2^9*c.k,93802366649536+c.lower,93802742946105+c.upper)) = pointBounds12440 := by
 decide +kernel
def cuts12441 : List PrefixCut := [⟨50,402248529,402248826⟩,
⟨100,825835951,825836573⟩,
⟨128,1055531821,1055532615⟩]
theorem checked12441 : checkPrefixCuts (2^48) 1634598913 9 Manual.Count131072.C012441.packed 128 cuts12441 = true := by
 decide +kernel
def pointBounds12441 : List (Nat × Nat × Nat) := [(1634650112,93803836397080,93804212694738),(1634701312,93804259984502,93804636282485)]
theorem point_links_checked12441 : (cuts12441.take 2).map (fun c => (1634598913-1+2*2^9*c.k,93803434148551+c.lower,93803810445912+c.upper)) = pointBounds12441 := by
 decide +kernel
def cuts12442 : List PrefixCut := [⟨22,180103575,180103706⟩,
⟨72,589373585,589374026⟩,
⟨122,1012749094,1012749854⟩,
⟨128,1063022981,1063023779⟩]
theorem checked12442 : checkPrefixCuts (2^48) 1634729985 9 Manual.Count131072.C012442.packed 128 cuts12442 = true := by
 decide +kernel
def pointBounds12442 : List (Nat × Nat × Nat) := [(1634752512,93804669783947,93805046082233),(1634803712,93805079053957,93805455352553),(1634854912,93805502429466,93805878728381)]
theorem point_links_checked12442 : (cuts12442.take 3).map (fun c => (1634729985-1+2*2^9*c.k,93804489680372+c.lower,93804865978527+c.upper)) = pointBounds12442 := by
 decide +kernel
def cuts12443 : List PrefixCut := [⟨44,367751134,367751415⟩,
⟨94,780598171,780598756⟩,
⟨128,1058978555,1058979349⟩]
theorem checked12443 : checkPrefixCuts (2^48) 1634861057 9 Manual.Count131072.C012443.packed 128 cuts12443 = true := by
 decide +kernel
def pointBounds12443 : List (Nat × Nat × Nat) := [(1634906112,93805920454487,93806296753721),(1634957312,93806333301524,93806709601062)]
theorem point_links_checked12443 : (cuts12443.take 2).map (fun c => (1634861057-1+2*2^9*c.k,93805552703353+c.lower,93805929002306+c.upper)) = pointBounds12443 := by
 decide +kernel
def cuts12444 : List PrefixCut := [⟨16,133420774,133420873⟩,
⟨66,555538233,555538644⟩,
⟨116,966797153,966797877⟩,
⟨128,1069394706,1069395509⟩]
theorem checked12444 : checkPrefixCuts (2^48) 1634992129 9 Manual.Count131072.C012444.packed 128 cuts12444 = true := by
 decide +kernel
def pointBounds12444 : List (Nat × Nat × Nat) := [(1635008512,93806745102682,93807121402528),(1635059712,93807167220141,93807543520299),(1635110912,93807578479061,93807954779532)]
theorem point_links_checked12444 : (cuts12444.take 3).map (fun c => (1634992129-1+2*2^9*c.k,93806611681908+c.lower,93806987981655+c.upper)) = pointBounds12444 := by
 decide +kernel
def cuts12445 : List PrefixCut := [⟨38,322591969,322592208⟩,
⟨88,736407251,736407800⟩,
⟨128,1065177983,1065178780⟩]
theorem checked12445 : checkPrefixCuts (2^48) 1635123201 9 Manual.Count131072.C012445.packed 128 cuts12445 = true := by
 decide +kernel
def pointBounds12445 : List (Nat × Nat × Nat) := [(1635162112,93808003668583,93808379969372),(1635213312,93808417483865,93808793784964)]
theorem point_links_checked12445 : (cuts12445.take 2).map (fun c => (1635123201-1+2*2^9*c.k,93807681076614+c.lower,93808057377164+c.upper)) = pointBounds12445 := by
 decide +kernel
def cuts12446 : List PrefixCut := [⟨10,79695535,79695596⟩,
⟨60,503468135,503468508⟩,
⟨110,919482069,919482754⟩,
⟨128,1070944413,1070945210⟩]
theorem checked12446 : checkPrefixCuts (2^48) 1635254273 9 Manual.Count131072.C012446.packed 128 cuts12446 = true := by
 decide +kernel
def pointBounds12446 : List (Nat × Nat × Nat) := [(1635264512,93808825950132,93809202251540),(1635315712,93809249722732,93809626024452),(1635366912,93809665736666,93810042038698)]
theorem point_links_checked12446 : (cuts12446.take 3).map (fun c => (1635254273-1+2*2^9*c.k,93808746254597+c.lower,93809122555944+c.upper)) = pointBounds12446 := by
 decide +kernel
def cuts12447 : List PrefixCut := [⟨32,273316388,273316590⟩,
⟨82,686206357,686206862⟩,
⟨128,1057262610,1057263393⟩]
theorem checked12447 : checkPrefixCuts (2^48) 1635385345 9 Manual.Count131072.C012447.packed 128 cuts12447 = true := by
 decide +kernel
def pointBounds12447 : List (Nat × Nat × Nat) := [(1635418112,93810090515398,93810466817744),(1635469312,93810503405367,93810879708016)]
theorem point_links_checked12447 : (cuts12447.take 2).map (fun c => (1635385345-1+2*2^9*c.k,93809817199010+c.lower,93810193501154+c.upper)) = pointBounds12447 := by
 decide +kernel
def cuts12448 : List PrefixCut := [⟨4,35280769,35280797⟩,
⟨54,454340279,454340611⟩,
⟨104,871149588,871150229⟩,
⟨128,1066986884,1066987672⟩]
theorem checked12448 : checkPrefixCuts (2^48) 1635516417 9 Manual.Count131072.C012448.packed 128 cuts12448 = true := by
 decide +kernel
def pointBounds12448 : List (Nat × Nat × Nat) := [(1635520512,93810909742389,93811286045344),(1635571712,93811328801899,93811705105158),(1635622912,93811745611208,93812121914776)]
theorem point_links_checked12448 : (cuts12448.take 3).map (fun c => (1635516417-1+2*2^9*c.k,93810874461620+c.lower,93811250764547+c.upper)) = pointBounds12448 := by
 decide +kernel
def cuts12449 : List PrefixCut := [⟨26,213214959,213215118⟩,
⟨76,637053483,637053960⟩,
⟨126,1039196970,1039197745⟩,
⟨128,1057092670,1057093459⟩]
theorem checked12449 : checkPrefixCuts (2^48) 1635647489 9 Manual.Count131072.C012449.packed 128 cuts12449 = true := by
 decide +kernel
def pointBounds12449 : List (Nat × Nat × Nat) := [(1635674112,93812154663463,93812530967337),(1635725312,93812578501987,93812954806179),(1635776512,93812980645474,93813356949964)]
theorem point_links_checked12449 : (cuts12449.take 3).map (fun c => (1635647489-1+2*2^9*c.k,93811941448504+c.lower,93812317752219+c.upper)) = pointBounds12449 := by
 decide +kernel
def cuts12450 : List PrefixCut := [⟨48,396108352,396108649⟩,
⟨98,812164147,812164752⟩,
⟨128,1064406678,1064407470⟩]
theorem checked12450 : checkPrefixCuts (2^48) 1635778561 9 Manual.Count131072.C012450.packed 128 cuts12450 = true := by
 decide +kernel
def pointBounds12450 : List (Nat × Nat × Nat) := [(1635827712,93813394649526,93813770954327),(1635878912,93813810705321,93814187010430)]
theorem point_links_checked12450 : (cuts12450.take 2).map (fun c => (1635778561-1+2*2^9*c.k,93812998541174+c.lower,93813374845678+c.upper)) = pointBounds12450 := by
 decide +kernel
def cuts12451 : List PrefixCut := [⟨20,165692909,165693033⟩,
⟨70,583099140,583099579⟩,
⟨120,989997257,989998003⟩,
⟨128,1056407321,1056408118⟩]
theorem checked12451 : checkPrefixCuts (2^48) 1635909633 9 Manual.Count131072.C012451.packed 128 cuts12451 = true := by
 decide +kernel
def pointBounds12451 : List (Nat × Nat × Nat) := [(1635930112,93814228640761,93814604946181),(1635981312,93814646046992,93815022352727),(1636032512,93815052945109,93815429251151)]
theorem point_links_checked12451 : (cuts12451.take 3).map (fun c => (1635909633-1+2*2^9*c.k,93814062947852+c.lower,93814439253148+c.upper)) = pointBounds12451 := by
 decide +kernel
def cuts12452 : List PrefixCut := [⟨42,349077539,349077794⟩,
⟨92,760767255,760767818⟩,
⟨128,1060279381,1060280171⟩]
theorem checked12452 : checkPrefixCuts (2^48) 1636040705 9 Manual.Count131072.C012452.packed 128 cuts12452 = true := by
 decide +kernel
def pointBounds12452 : List (Nat × Nat × Nat) := [(1636083712,93815468432712,93815844739060),(1636134912,93815880122428,93816256429084)]
theorem point_links_checked12452 : (cuts12452.take 2).map (fun c => (1636040705-1+2*2^9*c.k,93815119355173+c.lower,93815495661266+c.upper)) = pointBounds12452 := by
 decide +kernel
def cuts12453 : List PrefixCut := [⟨14,123690893,123690985⟩,
⟨64,543440081,543440484⟩,
⟨114,959907841,959908554⟩,
⟨128,1073440757,1073441557⟩]
theorem checked12453 : checkPrefixCuts (2^48) 1636171777 9 Manual.Count131072.C012453.packed 128 cuts12453 = true := by
 decide +kernel
def pointBounds12453 : List (Nat × Nat × Nat) := [(1636186112,93816303325447,93816679632422),(1636237312,93816723074635,93817099381921),(1636288512,93817139542395,93817515849991)]
theorem point_links_checked12453 : (cuts12453.take 3).map (fun c => (1636171777-1+2*2^9*c.k,93816179634554+c.lower,93816555941437+c.upper)) = pointBounds12453 := by
 decide +kernel
def cuts12454 : List PrefixCut := [⟨36,301889582,301889803⟩,
⟨86,715923054,715923588⟩,
⟨128,1057185570,1057186362⟩]
theorem checked12454 : checkPrefixCuts (2^48) 1636302849 9 Manual.Count131072.C012454.packed 128 cuts12454 = true := by
 decide +kernel
def pointBounds12454 : List (Nat × Nat × Nat) := [(1636339712,93817554964893,93817931272797),(1636390912,93817968998365,93818345306582)]
theorem point_links_checked12454 : (cuts12454.take 2).map (fun c => (1636302849-1+2*2^9*c.k,93817253075311+c.lower,93817629382994+c.upper)) = pointBounds12454 := by
 decide +kernel
def cuts12455 : List PrefixCut := [⟨8,65361748,65361797⟩,
⟨58,485561381,485561742⟩,
⟨108,906263782,906264457⟩,
⟨128,1071032429,1071033223⟩]
theorem checked12455 : checkPrefixCuts (2^48) 1636433921 9 Manual.Count131072.C012455.packed 128 cuts12455 = true := by
 decide +kernel
def pointBounds12455 : List (Nat × Nat × Nat) := [(1636442112,93818375622629,93818751931153),(1636493312,93818795822262,93819172131098),(1636544512,93819216524663,93819592833813)]
theorem point_links_checked12455 : (cuts12455.take 3).map (fun c => (1636433921-1+2*2^9*c.k,93818310260881+c.lower,93818686569356+c.upper)) = pointBounds12455 := by
 decide +kernel
def cuts12456 : List PrefixCut := [⟨30,248525013,248525196⟩,
⟨80,670405044,670405538⟩,
⟨128,1064755332,1064756116⟩]
theorem checked12456 : checkPrefixCuts (2^48) 1636564993 9 Manual.Count131072.C012456.packed 128 cuts12456 = true := by
 decide +kernel
def pointBounds12456 : List (Nat × Nat × Nat) := [(1636595712,93819629818323,93820006127775),(1636646912,93820051698354,93820428008117)]
theorem point_links_checked12456 : (cuts12456.take 2).map (fun c => (1636564993-1+2*2^9*c.k,93819381293310+c.lower,93819757602579+c.upper)) = pointBounds12456 := by
 decide +kernel
def cuts12457 : List PrefixCut := [⟨2,17025760,17025773⟩,
⟨52,430968640,430968959⟩,
⟨102,854700784,854701419⟩,
⟨128,1071892694,1071893489⟩]
theorem checked12457 : checkPrefixCuts (2^48) 1636696065 9 Manual.Count131072.C012457.packed 128 cuts12457 = true := by
 decide +kernel
def pointBounds12457 : List (Nat × Nat × Nat) := [(1636698112,93820463074402,93820839384468),(1636749312,93820877017282,93821253327654),(1636800512,93821300749426,93821677060114)]
theorem point_links_checked12457 : (cuts12457.take 3).map (fun c => (1636696065-1+2*2^9*c.k,93820446048642+c.lower,93820822358695+c.upper)) = pointBounds12457 := by
 decide +kernel
def cuts12458 : List PrefixCut := [⟨24,202743686,202743840⟩,
⟨74,609941309,609941767⟩,
⟨124,1028131220,1028131990⟩,
⟨128,1060801749,1060802544⟩]
theorem checked12458 : checkPrefixCuts (2^48) 1636827137 9 Manual.Count131072.C012458.packed 128 cuts12458 = true := by
 decide +kernel
def pointBounds12458 : List (Nat × Nat × Nat) := [(1636851712,93821720685022,93822096996024),(1636902912,93822127882645,93822504193951),(1636954112,93822546072556,93822922384174)]
theorem point_links_checked12458 : (cuts12458.take 3).map (fun c => (1636827137-1+2*2^9*c.k,93821517941336+c.lower,93821894252184+c.upper)) = pointBounds12458 := by
 decide +kernel
def cuts12459 : List PrefixCut := [⟨46,373641811,373642095⟩,
⟨96,791289714,791290306⟩,
⟨128,1062435793,1062436585⟩]
theorem checked12459 : checkPrefixCuts (2^48) 1636958209 9 Manual.Count131072.C012459.packed 128 cuts12459 = true := by
 decide +kernel
def pointBounds12459 : List (Nat × Nat × Nat) := [(1637005312,93822952384896,93823328696823),(1637056512,93823370032799,93823746345034)]
theorem point_links_checked12459 : (cuts12459.take 2).map (fun c => (1636958209-1+2*2^9*c.k,93822578743085+c.lower,93822955054728+c.upper)) = pointBounds12459 := by
 decide +kernel
def cuts12460 : List PrefixCut := [⟨18,147348467,147348578⟩,
⟨68,565829851,565830272⟩,
⟨118,986361189,986361923⟩,
⟨128,1066305355,1066306150⟩]
theorem checked12460 : checkPrefixCuts (2^48) 1637089281 9 Manual.Count131072.C012460.packed 128 cuts12460 = true := by
 decide +kernel
def pointBounds12460 : List (Nat × Nat × Nat) := [(1637107712,93823788527345,93824164839891),(1637158912,93824207008729,93824583321585),(1637210112,93824627540067,93825003853236)]
theorem point_links_checked12460 : (cuts12460.take 3).map (fun c => (1637089281-1+2*2^9*c.k,93823641178878+c.lower,93824017491313+c.upper)) = pointBounds12460 := by
 decide +kernel
def cuts12461 : List PrefixCut := [⟨40,332837638,332837888⟩,
⟨90,746466123,746466686⟩,
⟨128,1057280688,1057281484⟩]
theorem checked12461 : checkPrefixCuts (2^48) 1637220353 9 Manual.Count131072.C012461.packed 128 cuts12461 = true := by
 decide +kernel
def pointBounds12461 : List (Nat × Nat × Nat) := [(1637261312,93825040321871,93825416635351),(1637312512,93825453950356,93825830264149)]
theorem point_links_checked12461 : (cuts12461.take 2).map (fun c => (1637220353-1+2*2^9*c.k,93824707484233+c.lower,93825083797463+c.upper)) = pointBounds12461 := by
 decide +kernel
def cuts12462 : List PrefixCut := [⟨12,103316711,103316788⟩,
⟨62,515372078,515372461⟩,
⟨112,929305586,929306279⟩,
⟨128,1064071843,1064072640⟩]
theorem checked12462 : checkPrefixCuts (2^48) 1637351425 9 Manual.Count131072.C012462.packed 128 cuts12462 = true := by
 decide +kernel
def pointBounds12462 : List (Nat × Nat × Nat) := [(1637363712,93825868081632,93826244395735),(1637414912,93826280136999,93826656451408),(1637466112,93826694070507,93827070385226)]
theorem point_links_checked12462 : (cuts12462.take 3).map (fun c => (1637351425-1+2*2^9*c.k,93825764764921+c.lower,93826141078947+c.upper)) = pointBounds12462 := by
 decide +kernel
def cuts12463 : List PrefixCut := [⟨34,276403997,276404201⟩,
⟨84,687905086,687905596⟩,
⟨128,1055391994,1055392777⟩]
theorem checked12463 : checkPrefixCuts (2^48) 1637482497 9 Manual.Count131072.C012463.packed 128 cuts12463 = true := by
 decide +kernel
def pointBounds12463 : List (Nat × Nat × Nat) := [(1637517312,93827105240761,93827481555788),(1637568512,93827516741850,93827893057183)]
theorem point_links_checked12463 : (cuts12463.take 2).map (fun c => (1637482497-1+2*2^9*c.k,93826828836764+c.lower,93827205151587+c.upper)) = pointBounds12463 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000076
