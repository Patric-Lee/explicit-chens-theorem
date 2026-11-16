import PlattAssemblyKernel
import PlattCertificates.Count131072.C019536
import PlattCertificates.Count131072.C019537
import PlattCertificates.Count131072.C019538
import PlattCertificates.Count131072.C019539
import PlattCertificates.Count131072.C019540
import PlattCertificates.Count131072.C019541
import PlattCertificates.Count131072.C019542
import PlattCertificates.Count131072.C019543
import PlattCertificates.Count131072.C019544
import PlattCertificates.Count131072.C019545
import PlattCertificates.Count131072.C019546
import PlattCertificates.Count131072.C019547
import PlattCertificates.Count131072.C019548
import PlattCertificates.Count131072.C019549
import PlattCertificates.Count131072.C019550
import PlattCertificates.Count131072.C019551
import PlattCertificates.Count131072.C019552
import PlattCertificates.Count131072.C019553
import PlattCertificates.Count131072.C019554
import PlattCertificates.Count131072.C019555
import PlattCertificates.Count131072.C019556
import PlattCertificates.Count131072.C019557
import PlattCertificates.Count131072.C019558
import PlattCertificates.Count131072.C019559
import PlattCertificates.Count131072.C019560
import PlattCertificates.Count131072.C019561
import PlattCertificates.Count131072.C019562
import PlattCertificates.Count131072.C019563
import PlattCertificates.Count131072.C019564
import PlattCertificates.Count131072.C019565
import PlattCertificates.Count131072.C019566
import PlattCertificates.Count131072.C019567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000298
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19536 : List PrefixCut := [⟨55,285142599,285142770⟩,
⟨128,669164276,669164673⟩]
theorem checked19536 : checkPrefixCuts (2^48) 2564554753 9 Manual.Count131072.C019536.packed 128 cuts19536 = true := by
 decide +kernel
def pointBounds19536 : List (Nat × Nat × Nat) := [(2564611072,99716786114092,99717166304432)]
theorem point_links_checked19536 : (cuts19536.take 1).map (fun c => (2564554753-1+2*2^9*c.k,99716500971493+c.lower,99716881161662+c.upper)) = pointBounds19536 := by
 decide +kernel
def cuts19537 : List PrefixCut := [⟨6,29303279,29303297⟩,
⟨85,437347310,437347565⟩,
⟨128,656180002,656180386⟩]
theorem checked19537 : checkPrefixCuts (2^48) 2564685825 9 Manual.Count131072.C019537.packed 128 cuts19537 = true := by
 decide +kernel
def pointBounds19537 : List (Nat × Nat × Nat) := [(2564691968,99717199439048,99717579629632),(2564772864,99717607483079,99717987673900)]
theorem point_links_checked19537 : (cuts19537.take 2).map (fun c => (2564685825-1+2*2^9*c.k,99717170135769+c.lower,99717550326335+c.upper)) = pointBounds19537 := by
 decide +kernel
def cuts19538 : List PrefixCut := [⟨36,183820965,183821078⟩,
⟨115,605117873,605118234⟩,
⟨128,676009471,676009873⟩]
theorem checked19538 : checkPrefixCuts (2^48) 2564816897 9 Manual.Count131072.C019538.packed 128 cuts19538 = true := by
 decide +kernel
def pointBounds19538 : List (Nat × Nat × Nat) := [(2564853760,99718010136736,99718390327799),(2564934656,99718431433644,99718811624955)]
theorem point_links_checked19538 : (cuts19538.take 2).map (fun c => (2564816897-1+2*2^9*c.k,99717826315771+c.lower,99718206506721+c.upper)) = pointBounds19538 := by
 decide +kernel
def cuts19539 : List PrefixCut := [⟨66,338430656,338430860⟩,
⟨128,659075661,659076054⟩]
theorem checked19539 : checkPrefixCuts (2^48) 2564947969 9 Manual.Count131072.C019539.packed 128 cuts19539 = true := by
 decide +kernel
def pointBounds19539 : List (Nat × Nat × Nat) := [(2565015552,99718840755898,99719220947454)]
theorem point_links_checked19539 : (cuts19539.take 1).map (fun c => (2564947969-1+2*2^9*c.k,99718502325242+c.lower,99718882516594+c.upper)) = pointBounds19539 := by
 decide +kernel
def cuts19540 : List PrefixCut := [⟨17,88993500,88993553⟩,
⟨96,501362389,501362683⟩,
⟨128,666942729,666943122⟩]
theorem checked19540 : checkPrefixCuts (2^48) 2565079041 9 Manual.Count131072.C019540.packed 128 cuts19540 = true := by
 decide +kernel
def pointBounds19540 : List (Nat × Nat × Nat) := [(2565096448,99719250394403,99719630586201),(2565177344,99719662763292,99720042955331)]
theorem point_links_checked19540 : (cuts19540.take 2).map (fun c => (2565079041-1+2*2^9*c.k,99719161400903+c.lower,99719541592648+c.upper)) = pointBounds19540 := by
 decide +kernel
def cuts19541 : List PrefixCut := [⟨47,242825426,242825572⟩,
⟨126,645732108,645732496⟩,
⟨128,656155722,656156116⟩]
theorem checked19541 : checkPrefixCuts (2^48) 2565210113 9 Manual.Count131072.C019541.packed 128 cuts19541 = true := by
 decide +kernel
def pointBounds19541 : List (Nat × Nat × Nat) := [(2565258240,99720071169058,99720451361342),(2565339136,99720474075740,99720854268266)]
theorem point_links_checked19541 : (cuts19541.take 2).map (fun c => (2565210113-1+2*2^9*c.k,99719828343632+c.lower,99720208535770+c.upper)) = pointBounds19541 := by
 decide +kernel
def cuts19542 : List PrefixCut := [⟨77,407063118,407063355⟩,
⟨128,672031403,672031795⟩]
theorem checked19542 : checkPrefixCuts (2^48) 2565341185 9 Manual.Count131072.C019542.packed 128 cuts19542 = true := by
 decide +kernel
def pointBounds19542 : List (Nat × Nat × Nat) := [(2565420032,99720891562472,99721271755241)]
theorem point_links_checked19542 : (cuts19542.take 1).map (fun c => (2565341185-1+2*2^9*c.k,99720484499354+c.lower,99720864691886+c.upper)) = pointBounds19542 := by
 decide +kernel
def cuts19543 : List PrefixCut := [⟨28,143618235,143618319⟩,
⟨107,552959859,552960190⟩,
⟨128,662342178,662342574⟩]
theorem checked19543 : checkPrefixCuts (2^48) 2565472257 9 Manual.Count131072.C019543.packed 128 cuts19543 = true := by
 decide +kernel
def pointBounds19543 : List (Nat × Nat × Nat) := [(2565500928,99721300148992,99721680342000),(2565581824,99721709490616,99722089683871)]
theorem point_links_checked19543 : (cuts19543.take 2).map (fun c => (2565472257-1+2*2^9*c.k,99721156530757+c.lower,99721536723681+c.upper)) = pointBounds19543 := by
 decide +kernel
def cuts19544 : List PrefixCut := [⟨58,301592015,301592190⟩,
⟨128,669219907,669220295⟩]
theorem checked19544 : checkPrefixCuts (2^48) 2565603329 9 Manual.Count131072.C019544.packed 128 cuts19544 = true := by
 decide +kernel
def pointBounds19544 : List (Nat × Nat × Nat) := [(2565662720,99722120464950,99722500658445)]
theorem point_links_checked19544 : (cuts19544.take 1).map (fun c => (2565603329-1+2*2^9*c.k,99721818872935+c.lower,99722199066255+c.upper)) = pointBounds19544 := by
 decide +kernel
def cuts19545 : List PrefixCut := [⟨9,47392644,47392671⟩,
⟨88,461303105,461303375⟩,
⟨128,671050771,671051163⟩]
theorem checked19545 : checkPrefixCuts (2^48) 2565734401 9 Manual.Count131072.C019545.packed 128 cuts19545 = true := by
 decide +kernel
def pointBounds19545 : List (Nat × Nat × Nat) := [(2565743616,99722535485486,99722915679221),(2565824512,99722949395947,99723329589925)]
theorem point_links_checked19545 : (cuts19545.take 2).map (fun c => (2565734401-1+2*2^9*c.k,99722488092842+c.lower,99722868286550+c.upper)) = pointBounds19545 := by
 decide +kernel
def cuts19546 : List PrefixCut := [⟨39,199322961,199323079⟩,
⟨118,610574594,610574962⟩,
⟨128,663227913,663228311⟩]
theorem checked19546 : checkPrefixCuts (2^48) 2565865473 9 Manual.Count131072.C019546.packed 128 cuts19546 = true := by
 decide +kernel
def pointBounds19546 : List (Nat × Nat × Nat) := [(2565905408,99723358466574,99723738660792),(2565986304,99723769718207,99724149912675)]
theorem point_links_checked19546 : (cuts19546.take 2).map (fun c => (2565865473-1+2*2^9*c.k,99723159143613+c.lower,99723539337713+c.upper)) = pointBounds19546 := by
 decide +kernel
def cuts19547 : List PrefixCut := [⟨69,363082745,363082955⟩,
⟨128,664400814,664401203⟩]
theorem checked19547 : checkPrefixCuts (2^48) 2565996545 9 Manual.Count131072.C019547.packed 128 cuts19547 = true := by
 decide +kernel
def pointBounds19547 : List (Nat × Nat × Nat) := [(2566067200,99724185454271,99724565648979)]
theorem point_links_checked19547 : (cuts19547.take 1).map (fun c => (2565996545-1+2*2^9*c.k,99723822371526+c.lower,99724202566024+c.upper)) = pointBounds19547 := by
 decide +kernel
def cuts19548 : List PrefixCut := [⟨20,107384679,107384743⟩,
⟨99,516074611,516074918⟩,
⟨128,666779888,666780283⟩]
theorem checked19548 : checkPrefixCuts (2^48) 2566127617 9 Manual.Count131072.C019548.packed 128 cuts19548 = true := by
 decide +kernel
def pointBounds19548 : List (Nat × Nat × Nat) := [(2566148096,99724594157019,99724974351970),(2566228992,99725002846951,99725383042145)]
theorem point_links_checked19548 : (cuts19548.take 2).map (fun c => (2566127617-1+2*2^9*c.k,99724486772340+c.lower,99724866967227+c.upper)) = pointBounds19548 := by
 decide +kernel
def cuts19549 : List PrefixCut := [⟨50,252268348,252268502⟩,
⟨128,654680851,654681241⟩]
theorem checked19549 : checkPrefixCuts (2^48) 2566258689 9 Manual.Count131072.C019549.packed 128 cuts19549 = true := by
 decide +kernel
def pointBounds19549 : List (Nat × Nat × Nat) := [(2566309888,99725405820576,99725786016012)]
theorem point_links_checked19549 : (cuts19549.take 1).map (fun c => (2566258689-1+2*2^9*c.k,99725153552228+c.lower,99725533747510+c.upper)) = pointBounds19549 := by
 decide +kernel
def cuts19550 : List PrefixCut := [⟨1,4277417,4277419⟩,
⟨80,422689878,422690125⟩,
⟨128,668905394,668905786⟩]
theorem checked19550 : checkPrefixCuts (2^48) 2566389761 9 Manual.Count131072.C019550.packed 128 cuts19550 = true := by
 decide +kernel
def pointBounds19550 : List (Nat × Nat × Nat) := [(2566390784,99725812510496,99726192706170),(2566471680,99726230922957,99726611118876)]
theorem point_links_checked19550 : (cuts19550.take 2).map (fun c => (2566389761-1+2*2^9*c.k,99725808233079+c.lower,99726188428751+c.upper)) = pointBounds19550 := by
 decide +kernel
def cuts19551 : List PrefixCut := [⟨31,164287301,164287399⟩,
⟨110,572035486,572035826⟩,
⟨128,665142397,665142793⟩]
theorem checked19551 : checkPrefixCuts (2^48) 2566520833 9 Manual.Count131072.C019551.packed 128 cuts19551 = true := by
 decide +kernel
def pointBounds19551 : List (Nat × Nat × Nat) := [(2566552576,99726641425774,99727021621936),(2566633472,99727049173959,99727429370363)]
theorem point_links_checked19551 : (cuts19551.take 2).map (fun c => (2566520833-1+2*2^9*c.k,99726477138473+c.lower,99726857334537+c.upper)) = pointBounds19551 := by
 decide +kernel
def cuts19552 : List PrefixCut := [⟨61,317918345,317918531⟩,
⟨128,664231127,664231520⟩]
theorem checked19552 : checkPrefixCuts (2^48) 2566651905 9 Manual.Count131072.C019552.packed 128 cuts19552 = true := by
 decide +kernel
def pointBounds19552 : List (Nat × Nat × Nat) := [(2566714368,99727460199215,99727840395861)]
theorem point_links_checked19552 : (cuts19552.take 1).map (fun c => (2566651905-1+2*2^9*c.k,99727142280870+c.lower,99727522477330+c.upper)) = pointBounds19552 := by
 decide +kernel
def cuts19553 : List PrefixCut := [⟨12,63164343,63164380⟩,
⟨91,472189864,472190138⟩,
⟨128,663977824,663978212⟩]
theorem checked19553 : checkPrefixCuts (2^48) 2566782977 9 Manual.Count131072.C019553.packed 128 cuts19553 = true := by
 decide +kernel
def pointBounds19553 : List (Nat × Nat × Nat) := [(2566795264,99727869676340,99728249873230),(2566876160,99728278701861,99728658898988)]
theorem point_links_checked19553 : (cuts19553.take 2).map (fun c => (2566782977-1+2*2^9*c.k,99727806511997+c.lower,99728186708850+c.upper)) = pointBounds19553 := by
 decide +kernel
def cuts19554 : List PrefixCut := [⟨42,217444034,217444161⟩,
⟨121,618877842,618878208⟩,
⟨128,655062185,655062573⟩]
theorem checked19554 : checkPrefixCuts (2^48) 2566914049 9 Manual.Count131072.C019554.packed 128 cuts19554 = true := by
 decide +kernel
def pointBounds19554 : List (Nat × Nat × Nat) := [(2566957056,99728687933855,99729068131223),(2567037952,99729089367663,99729469565270)]
theorem point_links_checked19554 : (cuts19554.take 2).map (fun c => (2566914049-1+2*2^9*c.k,99728470489821+c.lower,99728850687062+c.upper)) = pointBounds19554 := by
 decide +kernel
def cuts19555 : List PrefixCut := [⟨72,372035066,372035282⟩,
⟨128,660620676,660621065⟩]
theorem checked19555 : checkPrefixCuts (2^48) 2567045121 9 Manual.Count131072.C019555.packed 128 cuts19555 = true := by
 decide +kernel
def pointBounds19555 : List (Nat × Nat × Nat) := [(2567118848,99729497587072,99729877784917)]
theorem point_links_checked19555 : (cuts19555.take 1).map (fun c => (2567045121-1+2*2^9*c.k,99729125552006+c.lower,99729505749635+c.upper)) = pointBounds19555 := by
 decide +kernel
def cuts19556 : List PrefixCut := [⟨23,121484751,121484822⟩,
⟨102,530665097,530665412⟩,
⟨128,665411122,665411517⟩]
theorem checked19556 : checkPrefixCuts (2^48) 2567176193 9 Manual.Count131072.C019556.packed 128 cuts19556 = true := by
 decide +kernel
def pointBounds19556 : List (Nat × Nat × Nat) := [(2567199744,99729907657433,99730287855522),(2567280640,99730316837779,99730697036112)]
theorem point_links_checked19556 : (cuts19556.take 2).map (fun c => (2567176193-1+2*2^9*c.k,99729786172682+c.lower,99730166370700+c.upper)) = pointBounds19556 := by
 decide +kernel
def cuts19557 : List PrefixCut := [⟨53,275737042,275737203⟩,
⟨128,669214231,669214623⟩]
theorem checked19557 : checkPrefixCuts (2^48) 2567307265 9 Manual.Count131072.C019557.packed 128 cuts19557 = true := by
 decide +kernel
def pointBounds19557 : List (Nat × Nat × Nat) := [(2567361536,99730727320846,99731107519420)]
theorem point_links_checked19557 : (cuts19557.take 1).map (fun c => (2567307265-1+2*2^9*c.k,99730451583804+c.lower,99730831782217+c.upper)) = pointBounds19557 := by
 decide +kernel
def cuts19558 : List PrefixCut := [⟨4,20282010,20282023⟩,
⟨83,427011802,427012056⟩,
⟨128,661177143,661177535⟩]
theorem checked19558 : checkPrefixCuts (2^48) 2567438337 9 Manual.Count131072.C019558.packed 128 cuts19558 = true := by
 decide +kernel
def pointBounds19558 : List (Nat × Nat × Nat) := [(2567442432,99731141080045,99731521278863),(2567523328,99731547809837,99731928008896)]
theorem point_links_checked19558 : (cuts19558.take 2).map (fun c => (2567438337-1+2*2^9*c.k,99731120798035+c.lower,99731500996840+c.upper)) = pointBounds19558 := by
 decide +kernel
def cuts19559 : List PrefixCut := [⟨34,171016933,171017034⟩,
⟨113,587587312,587587655⟩,
⟨128,662458944,662459332⟩]
theorem checked19559 : checkPrefixCuts (2^48) 2567569409 9 Manual.Count131072.C019559.packed 128 cuts19559 = true := by
 decide +kernel
def pointBounds19559 : List (Nat × Nat × Nat) := [(2567604224,99731952992111,99732333191409),(2567685120,99732369562490,99732749762030)]
theorem point_links_checked19559 : (cuts19559.take 2).map (fun c => (2567569409-1+2*2^9*c.k,99731781975178+c.lower,99732162174375+c.upper)) = pointBounds19559 := by
 decide +kernel
def cuts19560 : List PrefixCut := [⟨64,332915915,332916111⟩,
⟨128,660671321,660671713⟩]
theorem checked19560 : checkPrefixCuts (2^48) 2567700481 9 Manual.Count131072.C019560.packed 128 cuts19560 = true := by
 decide +kernel
def pointBounds19560 : List (Nat × Nat × Nat) := [(2567766016,99732777350037,99733157549818)]
theorem point_links_checked19560 : (cuts19560.take 1).map (fun c => (2567700481-1+2*2^9*c.k,99732444434122+c.lower,99732824633707+c.upper)) = pointBounds19560 := by
 decide +kernel
def cuts19561 : List PrefixCut := [⟨15,79471217,79471261⟩,
⟨94,496111794,496112081⟩,
⟨128,668420179,668420571⟩]
theorem checked19561 : checkPrefixCuts (2^48) 2567831553 9 Manual.Count131072.C019561.packed 128 cuts19561 = true := by
 decide +kernel
def pointBounds19561 : List (Nat × Nat × Nat) := [(2567846912,99733184576660,99733564776681),(2567927808,99733601217237,99733981417501)]
theorem point_links_checked19561 : (cuts19561.take 2).map (fun c => (2567831553-1+2*2^9*c.k,99733105105443+c.lower,99733485305420+c.upper)) = pointBounds19561 := by
 decide +kernel
def cuts19562 : List PrefixCut := [⟨45,236427050,236427188⟩,
⟨124,642738376,642738760⟩,
⟨128,665207337,665207734⟩]
theorem checked19562 : checkPrefixCuts (2^48) 2567962625 9 Manual.Count131072.C019562.packed 128 cuts19562 = true := by
 decide +kernel
def pointBounds19562 : List (Nat × Nat × Nat) := [(2568008704,99734009952672,99734390153179),(2568089600,99734416263998,99734796464751)]
theorem point_links_checked19562 : (cuts19562.take 2).map (fun c => (2567962625-1+2*2^9*c.k,99733773525622+c.lower,99734153725991+c.upper)) = pointBounds19562 := by
 decide +kernel
def cuts19563 : List PrefixCut := [⟨75,384925634,384925863⟩,
⟨128,661446852,661447243⟩]
theorem checked19563 : checkPrefixCuts (2^48) 2568093697 9 Manual.Count131072.C019563.packed 128 cuts19563 = true := by
 decide +kernel
def pointBounds19563 : List (Nat × Nat × Nat) := [(2568170496,99734823658593,99735203859588)]
theorem point_links_checked19563 : (cuts19563.take 1).map (fun c => (2568093697-1+2*2^9*c.k,99734438732959+c.lower,99734818933725+c.upper)) = pointBounds19563 := by
 decide +kernel
def cuts19564 : List PrefixCut := [⟨26,129874146,129874221⟩,
⟨105,543161186,543161509⟩,
⟨128,659769119,659769510⟩]
theorem checked19564 : checkPrefixCuts (2^48) 2568224769 9 Manual.Count131072.C019564.packed 128 cuts19564 = true := by
 decide +kernel
def pointBounds19564 : List (Nat × Nat × Nat) := [(2568251392,99735230053957,99735610255189),(2568332288,99735643340997,99736023542477)]
theorem point_links_checked19564 : (cuts19564.take 2).map (fun c => (2568224769-1+2*2^9*c.k,99735100179811+c.lower,99735480380968+c.upper)) = pointBounds19564 := by
 decide +kernel
def cuts19565 : List PrefixCut := [⟨56,292501563,292501735⟩,
⟨128,663680912,663681305⟩]
theorem checked19565 : checkPrefixCuts (2^48) 2568355841 9 Manual.Count131072.C019565.packed 128 cuts19565 = true := by
 decide +kernel
def pointBounds19565 : List (Nat × Nat × Nat) := [(2568413184,99736052450493,99736432652213)]
theorem point_links_checked19565 : (cuts19565.take 1).map (fun c => (2568355841-1+2*2^9*c.k,99735759948930+c.lower,99736140150478+c.upper)) = pointBounds19565 := by
 decide +kernel
def cuts19566 : List PrefixCut := [⟨7,36163932,36163954⟩,
⟨86,446233972,446234234⟩,
⟨128,665290707,665291102⟩]
theorem checked19566 : checkPrefixCuts (2^48) 2568486913 9 Manual.Count131072.C019566.packed 128 cuts19566 = true := by
 decide +kernel
def pointBounds19566 : List (Nat × Nat × Nat) := [(2568494080,99736459793774,99736839995737),(2568574976,99736869863814,99737250066017)]
theorem point_links_checked19566 : (cuts19566.take 2).map (fun c => (2568486913-1+2*2^9*c.k,99736423629842+c.lower,99736803831783+c.upper)) = pointBounds19566 := by
 decide +kernel
def cuts19567 : List PrefixCut := [⟨37,187822547,187822661⟩,
⟨116,602907314,602907675⟩,
⟨128,662407574,662407969⟩]
theorem checked19567 : checkPrefixCuts (2^48) 2568617985 9 Manual.Count131072.C019567.packed 128 cuts19567 = true := by
 decide +kernel
def pointBounds19567 : List (Nat × Nat × Nat) := [(2568655872,99737276743096,99737656945546),(2568736768,99737691827863,99738072030560)]
theorem point_links_checked19567 : (cuts19567.take 2).map (fun c => (2568617985-1+2*2^9*c.k,99737088920549+c.lower,99737469122885+c.upper)) = pointBounds19567 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000298
