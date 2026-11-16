import PlattAssemblyKernel
import PlattCertificates.Count131072.C013520
import PlattCertificates.Count131072.C013521
import PlattCertificates.Count131072.C013522
import PlattCertificates.Count131072.C013523
import PlattCertificates.Count131072.C013524
import PlattCertificates.Count131072.C013525
import PlattCertificates.Count131072.C013526
import PlattCertificates.Count131072.C013527
import PlattCertificates.Count131072.C013528
import PlattCertificates.Count131072.C013529
import PlattCertificates.Count131072.C013530
import PlattCertificates.Count131072.C013531
import PlattCertificates.Count131072.C013532
import PlattCertificates.Count131072.C013533
import PlattCertificates.Count131072.C013534
import PlattCertificates.Count131072.C013535
import PlattCertificates.Count131072.C013536
import PlattCertificates.Count131072.C013537
import PlattCertificates.Count131072.C013538
import PlattCertificates.Count131072.C013539
import PlattCertificates.Count131072.C013540
import PlattCertificates.Count131072.C013541
import PlattCertificates.Count131072.C013542
import PlattCertificates.Count131072.C013543
import PlattCertificates.Count131072.C013544
import PlattCertificates.Count131072.C013545
import PlattCertificates.Count131072.C013546
import PlattCertificates.Count131072.C013547
import PlattCertificates.Count131072.C013548
import PlattCertificates.Count131072.C013549
import PlattCertificates.Count131072.C013550
import PlattCertificates.Count131072.C013551
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000110
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13520 : List PrefixCut := [⟨5,38353515,38353542⟩,
⟨60,455480358,455480680⟩,
⟨115,876872886,876873507⟩,
⟨128,972591613,972592305⟩]
theorem checked13520 : checkPrefixCuts (2^48) 1776025601 9 Manual.Count131072.C013520.packed 128 cuts13520 = true := by
 decide +kernel
def pointBounds13520 : List (Nat × Nat × Nat) := [(1776030720,94902183742532,94902560838564),(1776087040,94902600869375,94902977965702),(1776143360,94903022261903,94903399358529)]
theorem point_links_checked13520 : (cuts13520.take 3).map (fun c => (1776025601-1+2*2^9*c.k,94902145389017+c.lower,94902522485022+c.upper)) = pointBounds13520 := by
 decide +kernel
def cuts13521 : List PrefixCut := [⟨42,328195951,328196184⟩,
⟨97,750829577,750830111⟩,
⟨128,989159209,989159911⟩]
theorem checked13521 : checkPrefixCuts (2^48) 1776156673 9 Manual.Count131072.C013521.packed 128 cuts13521 = true := by
 decide +kernel
def pointBounds13521 : List (Nat × Nat × Nat) := [(1776199680,94903446176581,94903823273511),(1776256000,94903868810207,94904245907438)]
theorem point_links_checked13521 : (cuts13521.take 2).map (fun c => (1776156673-1+2*2^9*c.k,94903117980630+c.lower,94903495077327+c.upper)) = pointBounds13521 := by
 decide +kernel
def cuts13522 : List PrefixCut := [⟨24,186033597,186033731⟩,
⟨79,609907943,609908380⟩,
⟨128,978786518,978787219⟩]
theorem checked13522 : checkPrefixCuts (2^48) 1776287745 9 Manual.Count131072.C013522.packed 128 cuts13522 = true := by
 decide +kernel
def pointBounds13522 : List (Nat × Nat × Nat) := [(1776312320,94904293173436,94904670270969),(1776368640,94904717047782,94905094145618)]
theorem point_links_checked13522 : (cuts13522.take 2).map (fun c => (1776287745-1+2*2^9*c.k,94904107139839+c.lower,94904484237238+c.upper)) = pointBounds13522 := by
 decide +kernel
def cuts13523 : List PrefixCut := [⟨6,45950636,45950670⟩,
⟨61,456013201,456013528⟩,
⟨116,873034184,873034809⟩,
⟨128,969682333,969683028⟩]
theorem checked13523 : checkPrefixCuts (2^48) 1776418817 9 Manual.Count131072.C013523.packed 128 cuts13523 = true := by
 decide +kernel
def pointBounds13523 : List (Nat × Nat × Nat) := [(1776424960,94905131876993,94905508975127),(1776481280,94905541939558,94905919037985),(1776537600,94905958960541,94906336059266)]
theorem point_links_checked13523 : (cuts13523.take 3).map (fun c => (1776418817-1+2*2^9*c.k,94905085926357+c.lower,94905463024457+c.upper)) = pointBounds13523 := by
 decide +kernel
def cuts13524 : List PrefixCut := [⟨43,331767280,331767515⟩,
⟨98,751930502,751931037⟩,
⟨128,982761185,982761881⟩]
theorem checked13524 : checkPrefixCuts (2^48) 1776549889 9 Manual.Count131072.C013524.packed 128 cuts13524 = true := by
 decide +kernel
def pointBounds13524 : List (Nat × Nat × Nat) := [(1776593920,94906387375970,94906764475000),(1776650240,94906807539192,94907184638522)]
theorem point_links_checked13524 : (cuts13524.take 2).map (fun c => (1776549889-1+2*2^9*c.k,94906055608690+c.lower,94906432707485+c.upper)) = pointBounds13524 := by
 decide +kernel
def cuts13525 : List PrefixCut := [⟨25,186626104,186626236⟩,
⟨80,611515441,611515872⟩,
⟨128,983005439,983006132⟩]
theorem checked13525 : checkPrefixCuts (2^48) 1776680961 9 Manual.Count131072.C013525.packed 128 cuts13525 = true := by
 decide +kernel
def pointBounds13525 : List (Nat × Nat × Nat) := [(1776706560,94907224995979,94907602095602),(1776762880,94907649885316,94908026985238)]
theorem point_links_checked13525 : (cuts13525.take 2).map (fun c => (1776680961-1+2*2^9*c.k,94907038369875+c.lower,94907415469366+c.upper)) = pointBounds13525 := by
 decide +kernel
def cuts13526 : List PrefixCut := [⟨7,53702804,53702841⟩,
⟨62,468109914,468110247⟩,
⟨117,879019023,879019645⟩,
⟨128,963923820,963924502⟩]
theorem checked13526 : checkPrefixCuts (2^48) 1776812033 9 Manual.Count131072.C013526.packed 128 cuts13526 = true := by
 decide +kernel
def pointBounds13526 : List (Nat × Nat × Nat) := [(1776819200,94908075078118,94908452178339),(1776875520,94908489485228,94908866585745),(1776931840,94908900394337,94909277495143)]
theorem point_links_checked13526 : (cuts13526.take 3).map (fun c => (1776812033-1+2*2^9*c.k,94908021375314+c.lower,94908398475498+c.upper)) = pointBounds13526 := by
 decide +kernel
def cuts13527 : List PrefixCut := [⟨44,333119363,333119598⟩,
⟨99,745744787,745745312⟩,
⟨128,970188565,970189251⟩]
theorem checked13527 : checkPrefixCuts (2^48) 1776943105 9 Manual.Count131072.C013527.packed 128 cuts13527 = true := by
 decide +kernel
def pointBounds13527 : List (Nat × Nat × Nat) := [(1776988160,94909318418497,94909695519598),(1777044480,94909731043921,94910108145312)]
theorem point_links_checked13527 : (cuts13527.take 2).map (fun c => (1776943105-1+2*2^9*c.k,94908985299134+c.lower,94909362400000+c.upper)) = pointBounds13527 := by
 decide +kernel
def cuts13528 : List PrefixCut := [⟨26,202740604,202740744⟩,
⟨81,629594616,629595058⟩,
⟨128,987698084,987698776⟩]
theorem checked13528 : checkPrefixCuts (2^48) 1777074177 9 Manual.Count131072.C013528.packed 128 cuts13528 = true := by
 decide +kernel
def pointBounds13528 : List (Nat × Nat × Nat) := [(1777100800,94910158228303,94910535329995),(1777157120,94910585082315,94910962184309)]
theorem point_links_checked13528 : (cuts13528.take 2).map (fun c => (1777074177-1+2*2^9*c.k,94909955487699+c.lower,94910332589251+c.upper)) = pointBounds13528 := by
 decide +kernel
def cuts13529 : List PrefixCut := [⟨8,62243442,62243486⟩,
⟨63,486853124,486853470⟩,
⟨118,893394948,893395579⟩,
⟨128,969729002,969729685⟩]
theorem checked13529 : checkPrefixCuts (2^48) 1777205249 9 Manual.Count131072.C013529.packed 128 cuts13529 = true := by
 decide +kernel
def pointBounds13529 : List (Nat × Nat × Nat) := [(1777213440,94911005429225,94911382531513),(1777269760,94911430038907,94911807141497),(1777326080,94911836580731,94912213683606)]
theorem point_links_checked13529 : (cuts13529.take 3).map (fun c => (1777205249-1+2*2^9*c.k,94910943185783+c.lower,94911320288027+c.upper)) = pointBounds13529 := by
 decide +kernel
def cuts13530 : List PrefixCut := [⟨45,342230850,342231087⟩,
⟨100,755714805,755715339⟩,
⟨128,970607339,970608026⟩]
theorem checked13530 : checkPrefixCuts (2^48) 1777336321 9 Manual.Count131072.C013530.packed 128 cuts13530 = true := by
 decide +kernel
def pointBounds13530 : List (Nat × Nat × Nat) := [(1777382400,94912255145635,94912632248799),(1777438720,94912668629590,94913045733051)]
theorem point_links_checked13530 : (cuts13530.take 2).map (fun c => (1777336321-1+2*2^9*c.k,94911912914785+c.lower,94912290017712+c.upper)) = pointBounds13530 := by
 decide +kernel
def cuts13531 : List PrefixCut := [⟨27,206179551,206179698⟩,
⟨82,619954160,619954600⟩,
⟨128,974336233,974336926⟩]
theorem checked13531 : checkPrefixCuts (2^48) 1777467393 9 Manual.Count131072.C013531.packed 128 cuts13531 = true := by
 decide +kernel
def pointBounds13531 : List (Nat × Nat × Nat) := [(1777495040,94913089701675,94913466805436),(1777551360,94913503476284,94913880580338)]
theorem point_links_checked13531 : (cuts13531.take 2).map (fun c => (1777467393-1+2*2^9*c.k,94912883522124+c.lower,94913260625738+c.upper)) = pointBounds13531 := by
 decide +kernel
def cuts13532 : List PrefixCut := [⟨9,67138355,67138405⟩,
⟨64,493237341,493237691⟩,
⟨119,901430787,901431425⟩,
⟨128,969672887,969673575⟩]
theorem checked13532 : checkPrefixCuts (2^48) 1777598465 9 Manual.Count131072.C013532.packed 128 cuts13532 = true := by
 decide +kernel
def pointBounds13532 : List (Nat × Nat × Nat) := [(1777607680,94913924996712,94914302101069),(1777664000,94914351095698,94914728200355),(1777720320,94914759289144,94915136394089)]
theorem point_links_checked13532 : (cuts13532.take 3).map (fun c => (1777598465-1+2*2^9*c.k,94913857858357+c.lower,94914234962664+c.upper)) = pointBounds13532 := by
 decide +kernel
def cuts13533 : List PrefixCut := [⟨46,350229951,350230193⟩,
⟨101,763147299,763147833⟩,
⟨128,965326427,965327101⟩]
theorem checked13533 : checkPrefixCuts (2^48) 1777729537 9 Manual.Count131072.C013533.packed 128 cuts13533 = true := by
 decide +kernel
def pointBounds13533 : List (Nat × Nat × Nat) := [(1777776640,94915177761195,94915554866432),(1777832960,94915590678543,94915967784072)]
theorem point_links_checked13533 : (cuts13533.take 2).map (fun c => (1777729537-1+2*2^9*c.k,94914827531244+c.lower,94915204636239+c.upper)) = pointBounds13533 := by
 decide +kernel
def cuts13534 : List PrefixCut := [⟨28,209458611,209458757⟩,
⟨83,629474119,629474563⟩,
⟨128,975703837,975704523⟩]
theorem checked13534 : checkPrefixCuts (2^48) 1777860609 9 Manual.Count131072.C013534.packed 128 cuts13534 = true := by
 decide +kernel
def pointBounds13534 : List (Nat × Nat × Nat) := [(1777889280,94916002316282,94916379422097),(1777945600,94916422331790,94916799437903)]
theorem point_links_checked13534 : (cuts13534.take 2).map (fun c => (1777860609-1+2*2^9*c.k,94915792857671+c.lower,94916169963340+c.upper)) = pointBounds13534 := by
 decide +kernel
def cuts13535 : List PrefixCut := [⟨10,72347728,72347781⟩,
⟨65,489803692,489804040⟩,
⟨120,909304431,909305074⟩,
⟨128,973890533,973891222⟩]
theorem checked13535 : checkPrefixCuts (2^48) 1777991681 9 Manual.Count131072.C013535.packed 128 cuts13535 = true := by
 decide +kernel
def pointBounds13535 : List (Nat × Nat × Nat) := [(1778001920,94916840909236,94917218015644),(1778058240,94917258365200,94917635471903),(1778114560,94917677865939,94918054972937)]
theorem point_links_checked13535 : (cuts13535.take 3).map (fun c => (1777991681-1+2*2^9*c.k,94916768561508+c.lower,94917145667863+c.upper)) = pointBounds13535 := by
 decide +kernel
def cuts13536 : List PrefixCut := [⟨47,363924202,363924458⟩,
⟨102,787038989,787039539⟩,
⟨128,983158375,983159065⟩]
theorem checked13536 : checkPrefixCuts (2^48) 1778122753 9 Manual.Count131072.C013536.packed 128 cuts13536 = true := by
 decide +kernel
def pointBounds13536 : List (Nat × Nat × Nat) := [(1778170880,94918106376243,94918483483543),(1778227200,94918529491030,94918906598624)]
theorem point_links_checked13536 : (cuts13536.take 2).map (fun c => (1778122753-1+2*2^9*c.k,94917742452041+c.lower,94918119559085+c.upper)) = pointBounds13536 := by
 decide +kernel
def cuts13537 : List PrefixCut := [⟨29,228881388,228881548⟩,
⟨84,645479820,645480272⟩,
⟨128,983560639,983561332⟩]
theorem checked13537 : checkPrefixCuts (2^48) 1778253825 9 Manual.Count131072.C013537.packed 128 cuts13537 = true := by
 decide +kernel
def pointBounds13537 : List (Nat × Nat × Nat) := [(1778283520,94918954491804,94919331599698),(1778339840,94919371090236,94919748198422)]
theorem point_links_checked13537 : (cuts13537.take 2).map (fun c => (1778253825-1+2*2^9*c.k,94918725610416+c.lower,94919102718150+c.upper)) = pointBounds13537 := by
 decide +kernel
def cuts13538 : List PrefixCut := [⟨11,79137533,79137591⟩,
⟨66,504414544,504414899⟩,
⟨121,913851428,913852069⟩,
⟨128,968294319,968294998⟩]
theorem checked13538 : checkPrefixCuts (2^48) 1778384897 9 Manual.Count131072.C013538.packed 128 cuts13538 = true := by
 decide +kernel
def pointBounds13538 : List (Nat × Nat × Nat) := [(1778396160,94919788308588,94920165417073),(1778452480,94920213585599,94920590694381),(1778508800,94920623022483,94921000131551)]
theorem point_links_checked13538 : (cuts13538.take 3).map (fun c => (1778384897-1+2*2^9*c.k,94919709171055+c.lower,94920086279482+c.upper)) = pointBounds13538 := by
 decide +kernel
def cuts13539 : List PrefixCut := [⟨48,364476721,364476978⟩,
⟨103,789396802,789397356⟩,
⟨128,983731933,983732625⟩]
theorem checked13539 : checkPrefixCuts (2^48) 1778515969 9 Manual.Count131072.C013539.packed 128 cuts13539 = true := by
 decide +kernel
def pointBounds13539 : List (Nat × Nat × Nat) := [(1778565120,94921041942095,94921419051458),(1778621440,94921466862176,94921843971836)]
theorem point_links_checked13539 : (cuts13539.take 2).map (fun c => (1778515969-1+2*2^9*c.k,94920677465374+c.lower,94921054574480+c.upper)) = pointBounds13539 := by
 decide +kernel
def cuts13540 : List PrefixCut := [⟨30,231362771,231362932⟩,
⟨85,637741065,637741514⟩,
⟨128,968467939,968468622⟩]
theorem checked13540 : checkPrefixCuts (2^48) 1778647041 9 Manual.Count131072.C013540.packed 128 cuts13540 = true := by
 decide +kernel
def pointBounds13540 : List (Nat × Nat × Nat) := [(1778677760,94921892560078,94922269670037),(1778734080,94922298938372,94922676048619)]
theorem point_links_checked13540 : (cuts13540.take 2).map (fun c => (1778647041-1+2*2^9*c.k,94921661197307+c.lower,94922038307105+c.upper)) = pointBounds13540 := by
 decide +kernel
def cuts13541 : List PrefixCut := [⟨12,88139692,88139755⟩,
⟨67,509050058,509050418⟩,
⟨122,929314148,929314806⟩,
⟨128,974093008,974093697⟩]
theorem checked13541 : checkPrefixCuts (2^48) 1778778113 9 Manual.Count131072.C013541.packed 128 cuts13541 = true := by
 decide +kernel
def pointBounds13541 : List (Nat × Nat × Nat) := [(1778790400,94922717804938,94923094915482),(1778846720,94923138715304,94923515826145),(1778903040,94923558979394,94923936090533)]
theorem point_links_checked13541 : (cuts13541.take 3).map (fun c => (1778778113-1+2*2^9*c.k,94922629665246+c.lower,94923006775727+c.upper)) = pointBounds13541 := by
 decide +kernel
def cuts13542 : List PrefixCut := [⟨49,373098526,373098787⟩,
⟨104,781469396,781469947⟩,
⟨128,975128657,975129347⟩]
theorem checked13542 : checkPrefixCuts (2^48) 1778909185 9 Manual.Count131072.C013542.packed 128 cuts13542 = true := by
 decide +kernel
def pointBounds13542 : List (Nat × Nat × Nat) := [(1778959360,94923976856780,94924353968211),(1779015680,94924385227650,94924762339371)]
theorem point_links_checked13542 : (cuts13542.take 2).map (fun c => (1778909185-1+2*2^9*c.k,94923603758254+c.lower,94923980869424+c.upper)) = pointBounds13542 := by
 decide +kernel
def cuts13543 : List PrefixCut := [⟨31,234950503,234950671⟩,
⟨86,650889580,650890046⟩,
⟨128,974582164,974582858⟩]
theorem checked13543 : checkPrefixCuts (2^48) 1779040257 9 Manual.Count131072.C013543.packed 128 cuts13543 = true := by
 decide +kernel
def pointBounds13543 : List (Nat × Nat × Nat) := [(1779072000,94924813837414,94925190949442),(1779128320,94925229776491,94925606888817)]
theorem point_links_checked13543 : (cuts13543.take 2).map (fun c => (1779040257-1+2*2^9*c.k,94924578886911+c.lower,94924955998771+c.upper)) = pointBounds13543 := by
 decide +kernel
def cuts13544 : List PrefixCut := [⟨13,96188650,96188718⟩,
⟨68,517322158,517322524⟩,
⟨123,943346441,943347105⟩,
⟨128,978465551,978466239⟩]
theorem checked13544 : checkPrefixCuts (2^48) 1779171329 9 Manual.Count131072.C013544.packed 128 cuts13544 = true := by
 decide +kernel
def pointBounds13544 : List (Nat × Nat × Nat) := [(1779184640,94925649657725,94926026770347),(1779240960,94926070791233,94926447904153),(1779297280,94926496815516,94926873928734)]
theorem point_links_checked13544 : (cuts13544.take 3).map (fun c => (1779171329-1+2*2^9*c.k,94925553469075+c.lower,94925930581629+c.upper)) = pointBounds13544 := by
 decide +kernel
def cuts13545 : List PrefixCut := [⟨50,381400142,381400409⟩,
⟨105,794109778,794110335⟩,
⟨128,966213282,966213961⟩]
theorem checked13545 : checkPrefixCuts (2^48) 1779302401 9 Manual.Count131072.C013545.packed 128 cuts13545 = true := by
 decide +kernel
def pointBounds13545 : List (Nat × Nat × Nat) := [(1779353600,94926913334768,94927290448277),(1779409920,94927326044404,94927703158203)]
theorem point_links_checked13545 : (cuts13545.take 2).map (fun c => (1779302401-1+2*2^9*c.k,94926531934626+c.lower,94926909047868+c.upper)) = pointBounds13545 := by
 decide +kernel
def cuts13546 : List PrefixCut := [⟨32,247869376,247869550⟩,
⟨87,670676245,670676716⟩,
⟨128,982750597,982751288⟩]
theorem checked13546 : checkPrefixCuts (2^48) 1779433473 9 Manual.Count131072.C013546.packed 128 cuts13546 = true := by
 decide +kernel
def pointBounds13546 : List (Nat × Nat × Nat) := [(1779466240,94927746017284,94928123131379),(1779522560,94928168824153,94928545938545)]
theorem point_links_checked13546 : (cuts13546.take 2).map (fun c => (1779433473-1+2*2^9*c.k,94927498147908+c.lower,94927875261829+c.upper)) = pointBounds13546 := by
 decide +kernel
def cuts13547 : List PrefixCut := [⟨14,106290255,106290328⟩,
⟨69,530968305,530968678⟩,
⟨124,946617746,946618411⟩,
⟨128,977775104,977775790⟩]
theorem checked13547 : checkPrefixCuts (2^48) 1779564545 9 Manual.Count131072.C013547.packed 128 cuts13547 = true := by
 decide +kernel
def pointBounds13547 : List (Nat × Nat × Nat) := [(1779578880,94928587188760,94928964303445),(1779635200,94929011866810,94929388981795),(1779691520,94929427516251,94929804631528)]
theorem point_links_checked13547 : (cuts13547.take 3).map (fun c => (1779564545-1+2*2^9*c.k,94928480898505+c.lower,94928858013117+c.upper)) = pointBounds13547 := by
 decide +kernel
def cuts13548 : List PrefixCut := [⟨51,394284547,394284822⟩,
⟨106,821927207,821927781⟩,
⟨128,989880781,989881472⟩]
theorem checked13548 : checkPrefixCuts (2^48) 1779695617 9 Manual.Count131072.C013548.packed 128 cuts13548 = true := by
 decide +kernel
def pointBounds13548 : List (Nat × Nat × Nat) := [(1779747840,94929852958156,94930230073729),(1779804160,94930280600816,94930657716688)]
theorem point_links_checked13548 : (cuts13548.take 2).map (fun c => (1779695617-1+2*2^9*c.k,94929458673609+c.lower,94929835788907+c.upper)) = pointBounds13548 := by
 decide +kernel
def cuts13549 : List PrefixCut := [⟨33,243702707,243702879⟩,
⟨88,662778575,662779044⟩,
⟨128,965611897,965612583⟩]
theorem checked13549 : checkPrefixCuts (2^48) 1779826689 9 Manual.Count131072.C013549.packed 128 cuts13549 = true := by
 decide +kernel
def pointBounds13549 : List (Nat × Nat × Nat) := [(1779860480,94930692257097,94931069373258),(1779916800,94931111332965,94931488449423)]
theorem point_links_checked13549 : (cuts13549.take 2).map (fun c => (1779826689-1+2*2^9*c.k,94930448554390+c.lower,94930825670379+c.upper)) = pointBounds13549 := by
 decide +kernel
def cuts13550 : List PrefixCut := [⟨15,112117730,112117810⟩,
⟨70,526264947,526265319⟩,
⟨125,942138607,942139280⟩,
⟨128,966805982,966806672⟩]
theorem checked13550 : checkPrefixCuts (2^48) 1779957761 9 Manual.Count131072.C013550.packed 128 cuts13550 = true := by
 decide +kernel
def pointBounds13550 : List (Nat × Nat × Nat) := [(1779973120,94931526284017,94931903400772),(1780029440,94931940431234,94932317548281),(1780085760,94932356304894,94932733422242)]
theorem point_links_checked13550 : (cuts13550.take 3).map (fun c => (1779957761-1+2*2^9*c.k,94931414166287+c.lower,94931791282962+c.upper)) = pointBounds13550 := by
 decide +kernel
def cuts13551 : List PrefixCut := [⟨52,396569270,396569551⟩,
⟨107,823010448,823011029⟩,
⟨128,981440051,981440745⟩]
theorem checked13551 : checkPrefixCuts (2^48) 1780088833 9 Manual.Count131072.C013551.packed 128 cuts13551 = true := by
 decide +kernel
def pointBounds13551 : List (Nat × Nat × Nat) := [(1780142080,94932777541539,94933154659185),(1780198400,94933203982717,94933581100663)]
theorem point_links_checked13551 : (cuts13551.take 2).map (fun c => (1780088833-1+2*2^9*c.k,94932380972269+c.lower,94932758089634+c.upper)) = pointBounds13551 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000110
