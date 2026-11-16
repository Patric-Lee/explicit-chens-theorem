import PlattAssemblyKernel
import PlattCertificates.Count131072.C017424
import PlattCertificates.Count131072.C017425
import PlattCertificates.Count131072.C017426
import PlattCertificates.Count131072.C017427
import PlattCertificates.Count131072.C017428
import PlattCertificates.Count131072.C017429
import PlattCertificates.Count131072.C017430
import PlattCertificates.Count131072.C017431
import PlattCertificates.Count131072.C017432
import PlattCertificates.Count131072.C017433
import PlattCertificates.Count131072.C017434
import PlattCertificates.Count131072.C017435
import PlattCertificates.Count131072.C017436
import PlattCertificates.Count131072.C017437
import PlattCertificates.Count131072.C017438
import PlattCertificates.Count131072.C017439
import PlattCertificates.Count131072.C017440
import PlattCertificates.Count131072.C017441
import PlattCertificates.Count131072.C017442
import PlattCertificates.Count131072.C017443
import PlattCertificates.Count131072.C017444
import PlattCertificates.Count131072.C017445
import PlattCertificates.Count131072.C017446
import PlattCertificates.Count131072.C017447
import PlattCertificates.Count131072.C017448
import PlattCertificates.Count131072.C017449
import PlattCertificates.Count131072.C017450
import PlattCertificates.Count131072.C017451
import PlattCertificates.Count131072.C017452
import PlattCertificates.Count131072.C017453
import PlattCertificates.Count131072.C017454
import PlattCertificates.Count131072.C017455
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000232
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17424 : List PrefixCut := [⟨24,138046455,138046541⟩,
⟨94,547132782,547133115⟩,
⟨128,749764192,749764651⟩]
theorem checked17424 : checkPrefixCuts (2^48) 2287730689 9 Manual.Count131072.C017424.packed 128 cuts17424 = true := by
 decide +kernel
def pointBounds17424 : List (Nat × Nat × Nat) := [(2287755264,98228716365028,98229095655221),(2287826944,98229125451355,98229504741795)]
theorem point_links_checked17424 : (cuts17424.take 2).map (fun c => (2287730689-1+2*2^9*c.k,98228578318573+c.lower,98228957608680+c.upper)) = pointBounds17424 := by
 decide +kernel
def cuts17425 : List PrefixCut := [⟨36,206196073,206196199⟩,
⟨106,615379760,615380136⟩,
⟨128,742831818,742832274⟩]
theorem checked17425 : checkPrefixCuts (2^48) 2287861761 9 Manual.Count131072.C017425.packed 128 cuts17425 = true := by
 decide +kernel
def pointBounds17425 : List (Nat × Nat × Nat) := [(2287898624,98229534278838,98229913569530),(2287970304,98229943462525,98230322753467)]
theorem point_links_checked17425 : (cuts17425.take 2).map (fun c => (2287861761-1+2*2^9*c.k,98229328082765+c.lower,98229707373331+c.upper)) = pointBounds17425 := by
 decide +kernel
def cuts17426 : List PrefixCut := [⟨48,282210854,282211029⟩,
⟨118,686079169,686079593⟩,
⟨128,743404557,743405016⟩]
theorem checked17426 : checkPrefixCuts (2^48) 2287992833 9 Manual.Count131072.C017426.packed 128 cuts17426 = true := by
 decide +kernel
def pointBounds17426 : List (Nat × Nat × Nat) := [(2288041984,98230353125437,98230732416634),(2288113664,98230756993752,98231136285198)]
theorem point_links_checked17426 : (cuts17426.take 2).map (fun c => (2287992833-1+2*2^9*c.k,98230070914583+c.lower,98230450205605+c.upper)) = pointBounds17426 := by
 decide +kernel
def cuts17427 : List PrefixCut := [⟨60,350712709,350712926⟩,
⟨128,754678876,754679338⟩]
theorem checked17427 : checkPrefixCuts (2^48) 2288123905 9 Manual.Count131072.C017427.packed 128 cuts17427 = true := by
 decide +kernel
def pointBounds17427 : List (Nat × Nat × Nat) := [(2288185344,98231165031849,98231544323547)]
theorem point_links_checked17427 : (cuts17427.take 1).map (fun c => (2288123905-1+2*2^9*c.k,98230814319140+c.lower,98231193610621+c.upper)) = pointBounds17427 := by
 decide +kernel
def cuts17428 : List PrefixCut := [⟨2,10701737,10701745⟩,
⟨72,427078766,427079032⟩,
⟨128,756849926,756850397⟩]
theorem checked17428 : checkPrefixCuts (2^48) 2288254977 9 Manual.Count131072.C017428.packed 128 cuts17428 = true := by
 decide +kernel
def pointBounds17428 : List (Nat × Nat × Nat) := [(2288257024,98231579699753,98231958991704),(2288328704,98231996076782,98232375368991)]
theorem point_links_checked17428 : (cuts17428.take 2).map (fun c => (2288254977-1+2*2^9*c.k,98231568998016+c.lower,98231948289959+c.upper)) = pointBounds17428 := by
 decide +kernel
def cuts17429 : List PrefixCut := [⟨14,81180727,81180777⟩,
⟨84,485231752,485232056⟩,
⟨128,736880844,736881307⟩]
theorem checked17429 : checkPrefixCuts (2^48) 2288386049 9 Manual.Count131072.C017429.packed 128 cuts17429 = true := by
 decide +kernel
def pointBounds17429 : List (Nat × Nat × Nat) := [(2288400384,98232407028669,98232786321133),(2288472064,98232811079694,98233190372412)]
theorem point_links_checked17429 : (cuts17429.take 2).map (fun c => (2288386049-1+2*2^9*c.k,98232325847942+c.lower,98232705140356+c.upper)) = pointBounds17429 := by
 decide +kernel
def cuts17430 : List PrefixCut := [⟨26,150913302,150913399⟩,
⟨96,561088579,561088933⟩,
⟨128,754180181,754180655⟩]
theorem checked17430 : checkPrefixCuts (2^48) 2288517121 9 Manual.Count131072.C017430.packed 128 cuts17430 = true := by
 decide +kernel
def pointBounds17430 : List (Nat × Nat × Nat) := [(2288543744,98233213642088,98233592935062),(2288615424,98233623817365,98234003110596)]
theorem point_links_checked17430 : (cuts17430.take 2).map (fun c => (2288517121-1+2*2^9*c.k,98233062728786+c.lower,98233442021663+c.upper)) = pointBounds17430 := by
 decide +kernel
def cuts17431 : List PrefixCut := [⟨38,218054818,218054952⟩,
⟨108,628573338,628573726⟩,
⟨128,746757987,746758451⟩]
theorem checked17431 : checkPrefixCuts (2^48) 2288648193 9 Manual.Count131072.C017431.packed 128 cuts17431 = true := by
 decide +kernel
def pointBounds17431 : List (Nat × Nat × Nat) := [(2288687104,98234034963785,98234414257270),(2288758784,98234445482305,98234824776044)]
theorem point_links_checked17431 : (cuts17431.take 2).map (fun c => (2288648193-1+2*2^9*c.k,98233816908967+c.lower,98234196202318+c.upper)) = pointBounds17431 := by
 decide +kernel
def cuts17432 : List PrefixCut := [⟨50,290968257,290968439⟩,
⟨120,705642265,705642702⟩,
⟨128,753847892,753848357⟩]
theorem checked17432 : checkPrefixCuts (2^48) 2288779265 9 Manual.Count131072.C017432.packed 128 cuts17432 = true := by
 decide +kernel
def pointBounds17432 : List (Nat × Nat × Nat) := [(2288830464,98234854635211,98235233929208),(2288902144,98235269309219,98235648603471)]
theorem point_links_checked17432 : (cuts17432.take 2).map (fun c => (2288779265-1+2*2^9*c.k,98234563666954+c.lower,98234942960769+c.upper)) = pointBounds17432 := by
 decide +kernel
def cuts17433 : List PrefixCut := [⟨62,362520310,362520538⟩,
⟨128,753927765,753928236⟩]
theorem checked17433 : checkPrefixCuts (2^48) 2288910337 9 Manual.Count131072.C017433.packed 128 cuts17433 = true := by
 decide +kernel
def pointBounds17433 : List (Nat × Nat × Nat) := [(2288973824,98235680035156,98236059329664)]
theorem point_links_checked17433 : (cuts17433.take 1).map (fun c => (2288910337-1+2*2^9*c.k,98235317514846+c.lower,98235696809126+c.upper)) = pointBounds17433 := by
 decide +kernel
def cuts17434 : List PrefixCut := [⟨4,22133910,22133924⟩,
⟨74,431604509,431604780⟩,
⟨128,752531976,752532440⟩]
theorem checked17434 : checkPrefixCuts (2^48) 2289041409 9 Manual.Count131072.C017434.packed 128 cuts17434 = true := by
 decide +kernel
def pointBounds17434 : List (Nat × Nat × Nat) := [(2289045504,98236093576521,98236472871286),(2289117184,98236503047120,98236882342142)]
theorem point_links_checked17434 : (cuts17434.take 2).map (fun c => (2289041409-1+2*2^9*c.k,98236071442611+c.lower,98236450737362+c.upper)) = pointBounds17434 := by
 decide +kernel
def cuts17435 : List PrefixCut := [⟨16,91358372,91358427⟩,
⟨86,499081853,499082160⟩,
⟨128,745111479,745111943⟩]
theorem checked17435 : checkPrefixCuts (2^48) 2289172481 9 Manual.Count131072.C017435.packed 128 cuts17435 = true := by
 decide +kernel
def pointBounds17435 : List (Nat × Nat × Nat) := [(2289188864,98236915332959,98237294628229),(2289260544,98237323056440,98237702351962)]
theorem point_links_checked17435 : (cuts17435.take 2).map (fun c => (2289172481-1+2*2^9*c.k,98236823974587+c.lower,98237203269802+c.upper)) = pointBounds17435 := by
 decide +kernel
def cuts17436 : List PrefixCut := [⟨28,160943423,160943524⟩,
⟨98,576018292,576018648⟩,
⟨128,749986847,749987309⟩]
theorem checked17436 : checkPrefixCuts (2^48) 2289303553 9 Manual.Count131072.C017436.packed 128 cuts17436 = true := by
 decide +kernel
def pointBounds17436 : List (Nat × Nat × Nat) := [(2289332224,98237730029489,98238109325269),(2289403904,98238145104358,98238524400393)]
theorem point_links_checked17436 : (cuts17436.take 2).map (fun c => (2289303553-1+2*2^9*c.k,98237569086066+c.lower,98237948381745+c.upper)) = pointBounds17436 := by
 decide +kernel
def cuts17437 : List PrefixCut := [⟨40,237159082,237159229⟩,
⟨110,645200462,645200859⟩,
⟨128,751419425,751419889⟩]
theorem checked17437 : checkPrefixCuts (2^48) 2289434625 9 Manual.Count131072.C017437.packed 128 cuts17437 = true := by
 decide +kernel
def pointBounds17437 : List (Nat × Nat × Nat) := [(2289475584,98238556231995,98238935528283),(2289547264,98238964273375,98239343569913)]
theorem point_links_checked17437 : (cuts17437.take 2).map (fun c => (2289434625-1+2*2^9*c.k,98238319072913+c.lower,98238698369054+c.upper)) = pointBounds17437 := by
 decide +kernel
def cuts17438 : List PrefixCut := [⟨52,300948974,300949161⟩,
⟨122,703186833,703187274⟩,
⟨128,740189138,740189602⟩]
theorem checked17438 : checkPrefixCuts (2^48) 2289565697 9 Manual.Count131072.C017438.packed 128 cuts17438 = true := by
 decide +kernel
def pointBounds17438 : List (Nat × Nat × Nat) := [(2289618944,98239371441312,98239750738104),(2289690624,98239773679171,98240152976217)]
theorem point_links_checked17438 : (cuts17438.take 2).map (fun c => (2289565697-1+2*2^9*c.k,98239070492338+c.lower,98239449788943+c.upper)) = pointBounds17438 := by
 decide +kernel
def cuts17439 : List PrefixCut := [⟨64,370754800,370755028⟩,
⟨128,742974192,742974651⟩]
theorem checked17439 : checkPrefixCuts (2^48) 2289696769 9 Manual.Count131072.C017439.packed 128 cuts17439 = true := by
 decide +kernel
def pointBounds17439 : List (Nat × Nat × Nat) := [(2289762304,98240181436276,98240560733573)]
theorem point_links_checked17439 : (cuts17439.take 1).map (fun c => (2289696769-1+2*2^9*c.k,98239810681476+c.lower,98240189978545+c.upper)) = pointBounds17439 := by
 decide +kernel
def cuts17440 : List PrefixCut := [⟨6,36631313,36631335⟩,
⟨76,440429447,440429721⟩,
⟨128,743300450,743300909⟩]
theorem checked17440 : checkPrefixCuts (2^48) 2289827841 9 Manual.Count131072.C017440.packed 128 cuts17440 = true := by
 decide +kernel
def pointBounds17440 : List (Nat × Nat × Nat) := [(2289833984,98240590286981,98240969584531),(2289905664,98240994085115,98241373382917)]
theorem point_links_checked17440 : (cuts17440.take 2).map (fun c => (2289827841-1+2*2^9*c.k,98240553655668+c.lower,98240932953196+c.upper)) = pointBounds17440 := by
 decide +kernel
def cuts17441 : List PrefixCut := [⟨18,108781112,108781178⟩,
⟨88,521280793,521281118⟩,
⟨128,755057648,755058115⟩]
theorem checked17441 : checkPrefixCuts (2^48) 2289958913 9 Manual.Count131072.C017441.packed 128 cuts17441 = true := by
 decide +kernel
def pointBounds17441 : List (Nat × Nat × Nat) := [(2289977344,98241405737230,98241785035283),(2290049024,98241818236911,98242197535223)]
theorem point_links_checked17441 : (cuts17441.take 2).map (fun c => (2289958913-1+2*2^9*c.k,98241296956118+c.lower,98241676254105+c.upper)) = pointBounds17441 := by
 decide +kernel
def cuts17442 : List PrefixCut := [⟨30,166787719,166787821⟩,
⟨100,575943109,575943459⟩,
⟨128,739773740,739774196⟩]
theorem checked17442 : checkPrefixCuts (2^48) 2290089985 9 Manual.Count131072.C017442.packed 128 cuts17442 = true := by
 decide +kernel
def pointBounds17442 : List (Nat × Nat × Nat) := [(2290120704,98242218801485,98242598100041),(2290192384,98242627956875,98243007255679)]
theorem point_links_checked17442 : (cuts17442.take 2).map (fun c => (2290089985-1+2*2^9*c.k,98242052013766+c.lower,98242431312220+c.upper)) = pointBounds17442 := by
 decide +kernel
def cuts17443 : List PrefixCut := [⟨42,244820373,244820521⟩,
⟨112,648419594,648419992⟩,
⟨128,736044677,736045131⟩]
theorem checked17443 : checkPrefixCuts (2^48) 2290221057 9 Manual.Count131072.C017443.packed 128 cuts17443 = true := by
 decide +kernel
def pointBounds17443 : List (Nat × Nat × Nat) := [(2290264064,98243036607879,98243415906937),(2290335744,98243440207100,98243819506408)]
theorem point_links_checked17443 : (cuts17443.take 2).map (fun c => (2290221057-1+2*2^9*c.k,98242791787506+c.lower,98243171086416+c.upper)) = pointBounds17443 := by
 decide +kernel
def cuts17444 : List PrefixCut := [⟨54,312151810,312152002⟩,
⟨124,715725839,715726283⟩,
⟨128,740795190,740795649⟩]
theorem checked17444 : checkPrefixCuts (2^48) 2290352129 9 Manual.Count131072.C017444.packed 128 cuts17444 = true := by
 decide +kernel
def pointBounds17444 : List (Nat × Nat × Nat) := [(2290407424,98243839983993,98244219283549),(2290479104,98244243558022,98244622857830)]
theorem point_links_checked17444 : (cuts17444.take 2).map (fun c => (2290352129-1+2*2^9*c.k,98243527832183+c.lower,98243907131547+c.upper)) = pointBounds17444 := by
 decide +kernel
def cuts17445 : List PrefixCut := [⟨66,389920569,389920812⟩,
⟨128,753164311,753164776⟩]
theorem checked17445 : checkPrefixCuts (2^48) 2290483201 9 Manual.Count131072.C017445.packed 128 cuts17445 = true := by
 decide +kernel
def pointBounds17445 : List (Nat × Nat × Nat) := [(2290550784,98244658547942,98245037848008)]
theorem point_links_checked17445 : (cuts17445.take 1).map (fun c => (2290483201-1+2*2^9*c.k,98244268627373+c.lower,98244647927196+c.upper)) = pointBounds17445 := by
 decide +kernel
def cuts17446 : List PrefixCut := [⟨8,48906885,48906914⟩,
⟨78,461290373,461290665⟩,
⟨128,751892497,751892969⟩]
theorem checked17446 : checkPrefixCuts (2^48) 2290614273 9 Manual.Count131072.C017446.packed 128 cuts17446 = true := by
 decide +kernel
def pointBounds17446 : List (Nat × Nat × Nat) := [(2290622464,98245070698569,98245449998886),(2290694144,98245483082057,98245862382637)]
theorem point_links_checked17446 : (cuts17446.take 2).map (fun c => (2290614273-1+2*2^9*c.k,98245021791684+c.lower,98245401091972+c.upper)) = pointBounds17446 := by
 decide +kernel
def cuts17447 : List PrefixCut := [⟨20,116361924,116361996⟩,
⟨90,523559002,523559323⟩,
⟨128,742756977,742757434⟩]
theorem checked17447 : checkPrefixCuts (2^48) 2290745345 9 Manual.Count131072.C017447.packed 128 cuts17447 = true := by
 decide +kernel
def pointBounds17447 : List (Nat × Nat × Nat) := [(2290765824,98245890046105,98246269346937),(2290837504,98246297243183,98246676544264)]
theorem point_links_checked17447 : (cuts17447.take 2).map (fun c => (2290745345-1+2*2^9*c.k,98245773684181+c.lower,98246152984941+c.upper)) = pointBounds17447 := by
 decide +kernel
def cuts17448 : List PrefixCut := [⟨32,191180919,191181037⟩,
⟨102,597124039,597124411⟩,
⟨128,749103673,749104135⟩]
theorem checked17448 : checkPrefixCuts (2^48) 2290876417 9 Manual.Count131072.C017448.packed 128 cuts17448 = true := by
 decide +kernel
def pointBounds17448 : List (Nat × Nat × Nat) := [(2290909184,98246707622077,98247086923412),(2290980864,98247113565197,98247492866786)]
theorem point_links_checked17448 : (cuts17448.take 2).map (fun c => (2290876417-1+2*2^9*c.k,98246516441158+c.lower,98246895742375+c.upper)) = pointBounds17448 := by
 decide +kernel
def cuts17449 : List PrefixCut := [⟨44,256162145,256162306⟩,
⟨114,666748221,666748641⟩,
⟨128,747340512,747340981⟩]
theorem checked17449 : checkPrefixCuts (2^48) 2291007489 9 Manual.Count131072.C017449.packed 128 cuts17449 = true := by
 decide +kernel
def pointBounds17449 : List (Nat × Nat × Nat) := [(2291052544,98247521706976,98247901008816),(2291124224,98247932293052,98248311595151)]
theorem point_links_checked17449 : (cuts17449.take 2).map (fun c => (2291007489-1+2*2^9*c.k,98247265544831+c.lower,98247644846510+c.upper)) = pointBounds17449 := by
 decide +kernel
def cuts17450 : List PrefixCut := [⟨56,329243791,329243995⟩,
⟨126,737470041,737470496⟩,
⟨128,747174934,747175395⟩]
theorem checked17450 : checkPrefixCuts (2^48) 2291138561 9 Manual.Count131072.C017450.packed 128 cuts17450 = true := by
 decide +kernel
def pointBounds17450 : List (Nat × Nat × Nat) := [(2291195904,98248342129134,98248721431486),(2291267584,98248750355384,98249129657987)]
theorem point_links_checked17450 : (cuts17450.take 2).map (fun c => (2291138561-1+2*2^9*c.k,98248012885343+c.lower,98248392187491+c.upper)) = pointBounds17450 := by
 decide +kernel
def cuts17451 : List PrefixCut := [⟨68,402193956,402194205⟩,
⟨128,749220611,749221071⟩]
theorem checked17451 : checkPrefixCuts (2^48) 2291269633 9 Manual.Count131072.C017451.packed 128 cuts17451 = true := by
 decide +kernel
def pointBounds17451 : List (Nat × Nat × Nat) := [(2291339264,98249162254233,98249541557091)]
theorem point_links_checked17451 : (cuts17451.take 1).map (fun c => (2291269633-1+2*2^9*c.k,98248760060277+c.lower,98249139362886+c.upper)) = pointBounds17451 := by
 decide +kernel
def cuts17452 : List PrefixCut := [⟨10,57243158,57243194⟩,
⟨80,467273648,467273936⟩,
⟨128,751634283,751634749⟩]
theorem checked17452 : checkPrefixCuts (2^48) 2291400705 9 Manual.Count131072.C017452.packed 128 cuts17452 = true := by
 decide +kernel
def pointBounds17452 : List (Nat × Nat × Nat) := [(2291410944,98249566524046,98249945827151),(2291482624,98249976554536,98250355857893)]
theorem point_links_checked17452 : (cuts17452.take 2).map (fun c => (2291400705-1+2*2^9*c.k,98249509280888+c.lower,98249888583957+c.upper)) = pointBounds17452 := by
 decide +kernel
def cuts17453 : List PrefixCut := [⟨22,125043009,125043089⟩,
⟨92,544997162,544997496⟩,
⟨128,750486050,750486513⟩]
theorem checked17453 : checkPrefixCuts (2^48) 2291531777 9 Manual.Count131072.C017453.packed 128 cuts17453 = true := by
 decide +kernel
def pointBounds17453 : List (Nat × Nat × Nat) := [(2291554304,98250385958180,98250765261795),(2291625984,98250805912333,98251185216202)]
theorem point_links_checked17453 : (cuts17453.take 2).map (fun c => (2291531777-1+2*2^9*c.k,98250260915171+c.lower,98250640218706+c.upper)) = pointBounds17453 := by
 decide +kernel
def cuts17454 : List PrefixCut := [⟨34,197870567,197870687⟩,
⟨104,612762609,612762985⟩,
⟨128,752408095,752408558⟩]
theorem checked17454 : checkPrefixCuts (2^48) 2291662849 9 Manual.Count131072.C017454.packed 128 cuts17454 = true := by
 decide +kernel
def pointBounds17454 : List (Nat × Nat × Nat) := [(2291697664,98251209271788,98251588575906),(2291769344,98251624163830,98252003468204)]
theorem point_links_checked17454 : (cuts17454.take 2).map (fun c => (2291662849-1+2*2^9*c.k,98251011401221+c.lower,98251390705219+c.upper)) = pointBounds17454 := by
 decide +kernel
def cuts17455 : List PrefixCut := [⟨46,267987382,267987551⟩,
⟨116,676958465,676958891⟩,
⟨128,749663101,749663574⟩]
theorem checked17455 : checkPrefixCuts (2^48) 2291793921 9 Manual.Count131072.C017455.packed 128 cuts17455 = true := by
 decide +kernel
def pointBounds17455 : List (Nat × Nat × Nat) := [(2291841024,98252031796698,98252411101328),(2291912704,98252440767781,98252820072668)]
theorem point_links_checked17455 : (cuts17455.take 2).map (fun c => (2291793921-1+2*2^9*c.k,98251763809316+c.lower,98252143113777+c.upper)) = pointBounds17455 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000232
