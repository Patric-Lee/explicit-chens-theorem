import PlattAssemblyKernel
import PlattCertificates.Count131072.C020704
import PlattCertificates.Count131072.C020705
import PlattCertificates.Count131072.C020706
import PlattCertificates.Count131072.C020707
import PlattCertificates.Count131072.C020708
import PlattCertificates.Count131072.C020709
import PlattCertificates.Count131072.C020710
import PlattCertificates.Count131072.C020711
import PlattCertificates.Count131072.C020712
import PlattCertificates.Count131072.C020713
import PlattCertificates.Count131072.C020714
import PlattCertificates.Count131072.C020715
import PlattCertificates.Count131072.C020716
import PlattCertificates.Count131072.C020717
import PlattCertificates.Count131072.C020718
import PlattCertificates.Count131072.C020719
import PlattCertificates.Count131072.C020720
import PlattCertificates.Count131072.C020721
import PlattCertificates.Count131072.C020722
import PlattCertificates.Count131072.C020723
import PlattCertificates.Count131072.C020724
import PlattCertificates.Count131072.C020725
import PlattCertificates.Count131072.C020726
import PlattCertificates.Count131072.C020727
import PlattCertificates.Count131072.C020728
import PlattCertificates.Count131072.C020729
import PlattCertificates.Count131072.C020730
import PlattCertificates.Count131072.C020731
import PlattCertificates.Count131072.C020732
import PlattCertificates.Count131072.C020733
import PlattCertificates.Count131072.C020734
import PlattCertificates.Count131072.C020735
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20704 : List PrefixCut := [⟨30,148108567,148108652⟩,
⟨113,558660988,558661302⟩,
⟨128,631883788,631884148⟩]
theorem checked20704 : checkPrefixCuts (2^48) 2717646849 9 Manual.Count131072.C020704.packed 128 cuts20704 = true := by
 decide +kernel
def pointBounds20704 : List (Nat × Nat × Nat) := [(2717677568,100468953919314,100469334551019),(2717762560,100469364471735,100469745103669)]
theorem point_links_checked20704 : (cuts20704.take 2).map (fun c => (2717646849-1+2*2^9*c.k,100468805810747+c.lower,100469186442367+c.upper)) = pointBounds20704 := by
 decide +kernel
def cuts20705 : List PrefixCut := [⟨68,331931285,331931482⟩,
⟨128,622428877,622429244⟩]
theorem checked20705 : checkPrefixCuts (2^48) 2717777921 9 Manual.Count131072.C020705.packed 128 cuts20705 = true := by
 decide +kernel
def pointBounds20705 : List (Nat × Nat × Nat) := [(2717847552,100469769625820,100470150257997)]
theorem point_links_checked20705 : (cuts20705.take 1).map (fun c => (2717777921-1+2*2^9*c.k,100469437694535+c.lower,100469818326515+c.upper)) = pointBounds20705 := by
 decide +kernel
def cuts20706 : List PrefixCut := [⟨23,111640477,111640543⟩,
⟨106,516976340,516976642⟩,
⟨128,624677142,624677510⟩]
theorem checked20706 : checkPrefixCuts (2^48) 2717908993 9 Manual.Count131072.C020706.packed 128 cuts20706 = true := by
 decide +kernel
def pointBounds20706 : List (Nat × Nat × Nat) := [(2717932544,100470171763889,100470552396302),(2718017536,100470577099752,100470957732401)]
theorem point_links_checked20706 : (cuts20706.take 2).map (fun c => (2717908993-1+2*2^9*c.k,100470060123412+c.lower,100470440755759+c.upper)) = pointBounds20706 := by
 decide +kernel
def cuts20707 : List PrefixCut := [⟨61,296793951,296794128⟩,
⟨128,621643928,621644292⟩]
theorem checked20707 : checkPrefixCuts (2^48) 2718040065 9 Manual.Count131072.C020707.packed 128 cuts20707 = true := by
 decide +kernel
def pointBounds20707 : List (Nat × Nat × Nat) := [(2718102528,100470981594505,100471362227397)]
theorem point_links_checked20707 : (cuts20707.take 1).map (fun c => (2718040065-1+2*2^9*c.k,100470684800554+c.lower,100471065433269+c.upper)) = pointBounds20707 := by
 decide +kernel
def cuts20708 : List PrefixCut := [⟨16,75904151,75904197⟩,
⟨99,483376569,483376850⟩,
⟨128,624823975,624824338⟩]
theorem checked20708 : checkPrefixCuts (2^48) 2718171137 9 Manual.Count131072.C020708.packed 128 cuts20708 = true := by
 decide +kernel
def pointBounds20708 : List (Nat × Nat × Nat) := [(2718187520,100471382348633,100471762981758),(2718272512,100471789821051,100472170454411)]
theorem point_links_checked20708 : (cuts20708.take 2).map (fun c => (2718171137-1+2*2^9*c.k,100471306444482+c.lower,100471687077561+c.upper)) = pointBounds20708 := by
 decide +kernel
def cuts20709 : List PrefixCut := [⟨54,262180956,262181111⟩,
⟨128,622515808,622516172⟩]
theorem checked20709 : checkPrefixCuts (2^48) 2718302209 9 Manual.Count131072.C020709.packed 128 cuts20709 = true := by
 decide +kernel
def pointBounds20709 : List (Nat × Nat × Nat) := [(2718357504,100472193449413,100472574083010)]
theorem point_links_checked20709 : (cuts20709.take 1).map (fun c => (2718302209-1+2*2^9*c.k,100471931268457+c.lower,100472311901899+c.upper)) = pointBounds20709 := by
 decide +kernel
def cuts20710 : List PrefixCut := [⟨9,41002984,41003009⟩,
⟨92,451750519,451750778⟩,
⟨128,627869965,627870328⟩]
theorem checked20710 : checkPrefixCuts (2^48) 2718433281 9 Manual.Count131072.C020710.packed 128 cuts20710 = true := by
 decide +kernel
def pointBounds20710 : List (Nat × Nat × Nat) := [(2718442496,100472594787249,100472975421080),(2718527488,100473005534784,100473386168849)]
theorem point_links_checked20710 : (cuts20710.take 2).map (fun c => (2718433281-1+2*2^9*c.k,100472553784265+c.lower,100472934418071+c.upper)) = pointBounds20710 := by
 decide +kernel
def cuts20711 : List PrefixCut := [⟨47,227367605,227367739⟩,
⟨128,615311959,615312321⟩]
theorem checked20711 : checkPrefixCuts (2^48) 2718564353 9 Manual.Count131072.C020711.packed 128 cuts20711 = true := by
 decide +kernel
def pointBounds20711 : List (Nat × Nat × Nat) := [(2718612480,100473409021835,100473789656138)]
theorem point_links_checked20711 : (cuts20711.take 1).map (fun c => (2718564353-1+2*2^9*c.k,100473181654230+c.lower,100473562288399+c.upper)) = pointBounds20711 := by
 decide +kernel
def cuts20712 : List PrefixCut := [⟨2,9732106,9732111⟩,
⟨85,416196282,416196520⟩,
⟨128,626670575,626670938⟩]
theorem checked20712 : checkPrefixCuts (2^48) 2718695425 9 Manual.Count131072.C020712.packed 128 cuts20712 = true := by
 decide +kernel
def pointBounds20712 : List (Nat × Nat × Nat) := [(2718697472,100473806698295,100474187332831),(2718782464,100474213162471,100474593797240)]
theorem point_links_checked20712 : (cuts20712.take 2).map (fun c => (2718695425-1+2*2^9*c.k,100473796966189+c.lower,100474177600720+c.upper)) = pointBounds20712 := by
 decide +kernel
def cuts20713 : List PrefixCut := [⟨40,196184240,196184352⟩,
⟨123,597032697,597033042⟩,
⟨128,621257124,621257484⟩]
theorem checked20713 : checkPrefixCuts (2^48) 2718826497 9 Manual.Count131072.C020713.packed 128 cuts20713 = true := by
 decide +kernel
def pointBounds20713 : List (Nat × Nat × Nat) := [(2718867456,100474619821004,100475000456010),(2718952448,100475020669461,100475401304700)]
theorem point_links_checked20713 : (cuts20713.take 2).map (fun c => (2718826497-1+2*2^9*c.k,100474423636764+c.lower,100474804271658+c.upper)) = pointBounds20713 := by
 decide +kernel
def cuts20714 : List PrefixCut := [⟨78,381580485,381580705⟩,
⟨128,637790197,637790563⟩]
theorem checked20714 : checkPrefixCuts (2^48) 2718957569 9 Manual.Count131072.C020714.packed 128 cuts20714 = true := by
 decide +kernel
def pointBounds20714 : List (Nat × Nat × Nat) := [(2719037440,100475426474373,100475807109847)]
theorem point_links_checked20714 : (cuts20714.take 1).map (fun c => (2718957569-1+2*2^9*c.k,100475044893888+c.lower,100475425529142+c.upper)) = pointBounds20714 := by
 decide +kernel
def cuts20715 : List PrefixCut := [⟨33,160245011,160245105⟩,
⟨116,561987525,561987851⟩,
⟨128,622542833,622543194⟩]
theorem checked20715 : checkPrefixCuts (2^48) 2719088641 9 Manual.Count131072.C020715.packed 128 cuts20715 = true := by
 decide +kernel
def pointBounds20715 : List (Nat × Nat × Nat) := [(2719122432,100475842929096,100476223564810),(2719207424,100476244671610,100476625307556)]
theorem point_links_checked20715 : (cuts20715.take 2).map (fun c => (2719088641-1+2*2^9*c.k,100475682684085+c.lower,100476063319705+c.upper)) = pointBounds20715 := by
 decide +kernel
def cuts20716 : List PrefixCut := [⟨71,349352058,349352260⟩,
⟨128,628309418,628309782⟩]
theorem checked20716 : checkPrefixCuts (2^48) 2719219713 9 Manual.Count131072.C020716.packed 128 cuts20716 = true := by
 decide +kernel
def pointBounds20716 : List (Nat × Nat × Nat) := [(2719292416,100476654578976,100477035215159)]
theorem point_links_checked20716 : (cuts20716.take 1).map (fun c => (2719219713-1+2*2^9*c.k,100476305226918+c.lower,100476685862899+c.upper)) = pointBounds20716 := by
 decide +kernel
def cuts20717 : List PrefixCut := [⟨26,125347740,125347811⟩,
⟨109,530675250,530675560⟩,
⟨128,627554540,627554906⟩]
theorem checked20717 : checkPrefixCuts (2^48) 2719350785 9 Manual.Count131072.C020717.packed 128 cuts20717 = true := by
 decide +kernel
def pointBounds20717 : List (Nat × Nat × Nat) := [(2719377408,100477058884076,100477439520492),(2719462400,100477464211586,100477844848241)]
theorem point_links_checked20717 : (cuts20717.take 2).map (fun c => (2719350785-1+2*2^9*c.k,100476933536336+c.lower,100477314172681+c.upper)) = pointBounds20717 := by
 decide +kernel
def cuts20718 : List PrefixCut := [⟨64,314024784,314024971⟩,
⟨128,627110438,627110808⟩]
theorem checked20718 : checkPrefixCuts (2^48) 2719481857 9 Manual.Count131072.C020718.packed 128 cuts20718 = true := by
 decide +kernel
def pointBounds20718 : List (Nat × Nat × Nat) := [(2719547392,100477875115660,100478255752558)]
theorem point_links_checked20718 : (cuts20718.take 1).map (fun c => (2719481857-1+2*2^9*c.k,100477561090876+c.lower,100477941727587+c.upper)) = pointBounds20718 := by
 decide +kernel
def cuts20719 : List PrefixCut := [⟨19,87662619,87662671⟩,
⟨102,491710144,491710432⟩,
⟨128,618800367,618800727⟩]
theorem checked20719 : checkPrefixCuts (2^48) 2719612929 9 Manual.Count131072.C020719.packed 128 cuts20719 = true := by
 decide +kernel
def pointBounds20719 : List (Nat × Nat × Nat) := [(2719632384,100478275863933,100478656501066),(2719717376,100478679911458,100479060548827)]
theorem point_links_checked20719 : (cuts20719.take 2).map (fun c => (2719612929-1+2*2^9*c.k,100478188201314+c.lower,100478568838395+c.upper)) = pointBounds20719 := by
 decide +kernel
def cuts20720 : List PrefixCut := [⟨57,275081841,275082000⟩,
⟨128,622082353,622082710⟩]
theorem checked20720 : checkPrefixCuts (2^48) 2719744001 9 Manual.Count131072.C020720.packed 128 cuts20720 = true := by
 decide +kernel
def pointBounds20720 : List (Nat × Nat × Nat) := [(2719802368,100479082083522,100479462721122)]
theorem point_links_checked20720 : (cuts20720.take 1).map (fun c => (2719744001-1+2*2^9*c.k,100478807001681+c.lower,100479187639122+c.upper)) = pointBounds20720 := by
 decide +kernel
def cuts20721 : List PrefixCut := [⟨13,65818316,65818354⟩,
⟨97,475829960,475830239⟩,
⟨128,630641705,630642072⟩]
theorem checked20721 : checkPrefixCuts (2^48) 2719875073 9 Manual.Count131072.C020721.packed 128 cuts20721 = true := by
 decide +kernel
def pointBounds20721 : List (Nat × Nat × Nat) := [(2719888384,100479494902350,100479875540186),(2719974400,100479904913994,100480285552071)]
theorem point_links_checked20721 : (cuts20721.take 2).map (fun c => (2719875073-1+2*2^9*c.k,100479429084034+c.lower,100479809721832+c.upper)) = pointBounds20721 := by
 decide +kernel
def cuts20722 : List PrefixCut := [⟨53,260257606,260257757⟩,
⟨128,627920840,627921208⟩]
theorem checked20722 : checkPrefixCuts (2^48) 2720006145 9 Manual.Count131072.C020722.packed 128 cuts20722 = true := by
 decide +kernel
def pointBounds20722 : List (Nat × Nat × Nat) := [(2720060416,100480319983345,100480700621661)]
theorem point_links_checked20722 : (cuts20722.take 1).map (fun c => (2720006145-1+2*2^9*c.k,100480059725739+c.lower,100480440363904+c.upper)) = pointBounds20722 := by
 decide +kernel
def cuts20723 : List PrefixCut := [⟨9,44599028,44599052⟩,
⟨93,443396370,443396627⟩,
⟨128,616301243,616301598⟩]
theorem checked20723 : checkPrefixCuts (2^48) 2720137217 9 Manual.Count131072.C020723.packed 128 cuts20723 = true := by
 decide +kernel
def pointBounds20723 : List (Nat × Nat × Nat) := [(2720146432,100480732245607,100481112884164),(2720232448,100481131042949,100481511681739)]
theorem point_links_checked20723 : (cuts20723.take 2).map (fun c => (2720137217-1+2*2^9*c.k,100480687646579+c.lower,100481068285112+c.upper)) = pointBounds20723 := by
 decide +kernel
def cuts20724 : List PrefixCut := [⟨49,231260495,231260633⟩,
⟨128,620306827,620307188⟩]
theorem checked20724 : checkPrefixCuts (2^48) 2720268289 9 Manual.Count131072.C020724.packed 128 cuts20724 = true := by
 decide +kernel
def pointBounds20724 : List (Nat × Nat × Nat) := [(2720318464,100481535208317,100481915847343)]
theorem point_links_checked20724 : (cuts20724.take 1).map (fun c => (2720268289-1+2*2^9*c.k,100481303947822+c.lower,100481684586710+c.upper)) = pointBounds20724 := by
 decide +kernel
def cuts20725 : List PrefixCut := [⟨5,24521947,24521960⟩,
⟨89,433421125,433421374⟩,
⟨128,622346371,622346727⟩]
theorem checked20725 : checkPrefixCuts (2^48) 2720399361 9 Manual.Count131072.C020725.packed 128 cuts20725 = true := by
 decide +kernel
def pointBounds20725 : List (Nat × Nat × Nat) := [(2720404480,100481948776596,100482329415858),(2720490496,100482357675774,100482738315272)]
theorem point_links_checked20725 : (cuts20725.take 2).map (fun c => (2720399361-1+2*2^9*c.k,100481924254649+c.lower,100482304893898+c.upper)) = pointBounds20725 := by
 decide +kernel
def cuts20726 : List PrefixCut := [⟨45,217891746,217891876⟩,
⟨128,623247486,623247853⟩]
theorem checked20726 : checkPrefixCuts (2^48) 2720530433 9 Manual.Count131072.C020726.packed 128 cuts20726 = true := by
 decide +kernel
def pointBounds20726 : List (Nat × Nat × Nat) := [(2720576512,100482764492766,100483145132501)]
theorem point_links_checked20726 : (cuts20726.take 1).map (fun c => (2720530433-1+2*2^9*c.k,100482546601020+c.lower,100482927240625+c.upper)) = pointBounds20726 := by
 decide +kernel
def cuts20727 : List PrefixCut := [⟨1,4862537,4862540⟩,
⟨85,409791573,409791815⟩,
⟨128,623527789,623528156⟩]
theorem checked20727 : checkPrefixCuts (2^48) 2720661505 9 Manual.Count131072.C020727.packed 128 cuts20727 = true := by
 decide +kernel
def pointBounds20727 : List (Nat × Nat × Nat) := [(2720662528,100483174711043,100483555351018),(2720748544,100483579640079,100483960280293)]
theorem point_links_checked20727 : (cuts20727.take 2).map (fun c => (2720661505-1+2*2^9*c.k,100483169848506+c.lower,100483550488478+c.upper)) = pointBounds20727 := by
 decide +kernel
def cuts20728 : List PrefixCut := [⟨41,196456247,196456365⟩,
⟨125,602083922,602084271⟩,
⟨128,616152898,616153255⟩]
theorem checked20728 : checkPrefixCuts (2^48) 2720792577 9 Manual.Count131072.C020728.packed 128 cuts20728 = true := by
 decide +kernel
def pointBounds20728 : List (Nat × Nat × Nat) := [(2720834560,100483989832542,100484370472999),(2720920576,100484395460217,100484776100905)]
theorem point_links_checked20728 : (cuts20728.take 2).map (fun c => (2720792577-1+2*2^9*c.k,100483793376295+c.lower,100484174016634+c.upper)) = pointBounds20728 := by
 decide +kernel
def cuts20729 : List PrefixCut := [⟨81,392683716,392683944⟩,
⟨128,625536677,625537036⟩]
theorem checked20729 : checkPrefixCuts (2^48) 2720923649 9 Manual.Count131072.C020729.packed 128 cuts20729 = true := by
 decide +kernel
def pointBounds20729 : List (Nat × Nat × Nat) := [(2721006592,100484802212909,100485182853833)]
theorem point_links_checked20729 : (cuts20729.take 1).map (fun c => (2720923649-1+2*2^9*c.k,100484409529193+c.lower,100484790169889+c.upper)) = pointBounds20729 := by
 decide +kernel
def cuts20730 : List PrefixCut := [⟨37,178438456,178438563⟩,
⟨121,590544365,590544718⟩,
⟨128,624885933,624886306⟩]
theorem checked20730 : checkPrefixCuts (2^48) 2721054721 9 Manual.Count131072.C020730.packed 128 cuts20730 = true := by
 decide +kernel
def pointBounds20730 : List (Nat × Nat × Nat) := [(2721092608,100485213504326,100485594145488),(2721178624,100485625610235,100486006251643)]
theorem point_links_checked20730 : (cuts20730.take 2).map (fun c => (2721054721-1+2*2^9*c.k,100485035065870+c.lower,100485415706925+c.upper)) = pointBounds20730 := by
 decide +kernel
def cuts20731 : List PrefixCut := [⟨77,371958834,371959048⟩,
⟨128,619270326,619270684⟩]
theorem checked20731 : checkPrefixCuts (2^48) 2721185793 9 Manual.Count131072.C020731.packed 128 cuts20731 = true := by
 decide +kernel
def pointBounds20731 : List (Nat × Nat × Nat) := [(2721264640,100486031910637,100486412552279)]
theorem point_links_checked20731 : (cuts20731.take 1).map (fun c => (2721185793-1+2*2^9*c.k,100485659951803+c.lower,100486040593231+c.upper)) = pointBounds20731 := by
 decide +kernel
def cuts20732 : List PrefixCut := [⟨33,157528008,157528099⟩,
⟨117,563492490,563492817⟩,
⟨128,620585065,620585424⟩]
theorem checked20732 : checkPrefixCuts (2^48) 2721316865 9 Manual.Count131072.C020732.packed 128 cuts20732 = true := by
 decide +kernel
def pointBounds20732 : List (Nat × Nat × Nat) := [(2721350656,100486436750137,100486817392014),(2721436672,100486842714619,100487223356732)]
theorem point_links_checked20732 : (cuts20732.take 2).map (fun c => (2721316865-1+2*2^9*c.k,100486279222129+c.lower,100486659863915+c.upper)) = pointBounds20732 := by
 decide +kernel
def cuts20733 : List PrefixCut := [⟨73,358270971,358271176⟩,
⟨128,626243730,626244087⟩]
theorem checked20733 : checkPrefixCuts (2^48) 2721447937 9 Manual.Count131072.C020733.packed 128 cuts20733 = true := by
 decide +kernel
def pointBounds20733 : List (Nat × Nat × Nat) := [(2721522688,100487258078165,100487638720515)]
theorem point_links_checked20733 : (cuts20733.take 1).map (fun c => (2721447937-1+2*2^9*c.k,100486899807194+c.lower,100487280449339+c.upper)) = pointBounds20733 := by
 decide +kernel
def cuts20734 : List PrefixCut := [⟨29,141896098,141896182⟩,
⟨113,556509381,556509709⟩,
⟨128,629316133,629316505⟩]
theorem checked20734 : checkPrefixCuts (2^48) 2721579009 9 Manual.Count131072.C020734.packed 128 cuts20734 = true := by
 decide +kernel
def pointBounds20734 : List (Nat × Nat × Nat) := [(2721608704,100487667947022,100488048589608),(2721694720,100488082560305,100488463203135)]
theorem point_links_checked20734 : (cuts20734.take 2).map (fun c => (2721579009-1+2*2^9*c.k,100487526050924+c.lower,100487906693426+c.upper)) = pointBounds20734 := by
 decide +kernel
def cuts20735 : List PrefixCut := [⟨69,339207958,339208156⟩,
⟨128,627941432,627941797⟩]
theorem checked20735 : checkPrefixCuts (2^48) 2721710081 9 Manual.Count131072.C020735.packed 128 cuts20735 = true := by
 decide +kernel
def pointBounds20735 : List (Nat × Nat × Nat) := [(2721780736,100488494575015,100488875218087)]
theorem point_links_checked20735 : (cuts20735.take 1).map (fun c => (2721710081-1+2*2^9*c.k,100488155367057+c.lower,100488536009931+c.upper)) = pointBounds20735 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000022
