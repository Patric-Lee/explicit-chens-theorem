import PlattAssemblyKernel
import PlattCertificates.Count131072.C017648
import PlattCertificates.Count131072.C017649
import PlattCertificates.Count131072.C017650
import PlattCertificates.Count131072.C017651
import PlattCertificates.Count131072.C017652
import PlattCertificates.Count131072.C017653
import PlattCertificates.Count131072.C017654
import PlattCertificates.Count131072.C017655
import PlattCertificates.Count131072.C017656
import PlattCertificates.Count131072.C017657
import PlattCertificates.Count131072.C017658
import PlattCertificates.Count131072.C017659
import PlattCertificates.Count131072.C017660
import PlattCertificates.Count131072.C017661
import PlattCertificates.Count131072.C017662
import PlattCertificates.Count131072.C017663
import PlattCertificates.Count131072.C017664
import PlattCertificates.Count131072.C017665
import PlattCertificates.Count131072.C017666
import PlattCertificates.Count131072.C017667
import PlattCertificates.Count131072.C017668
import PlattCertificates.Count131072.C017669
import PlattCertificates.Count131072.C017670
import PlattCertificates.Count131072.C017671
import PlattCertificates.Count131072.C017672
import PlattCertificates.Count131072.C017673
import PlattCertificates.Count131072.C017674
import PlattCertificates.Count131072.C017675
import PlattCertificates.Count131072.C017676
import PlattCertificates.Count131072.C017677
import PlattCertificates.Count131072.C017678
import PlattCertificates.Count131072.C017679
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000239
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17648 : List PrefixCut := [⟨22,130344950,130345033⟩,
⟨93,545909617,545909959⟩,
⟨128,747188357,747188822⟩]
theorem checked17648 : checkPrefixCuts (2^48) 2317090817 9 Manual.Count131072.C017648.packed 128 cuts17648 = true := by
 decide +kernel
def pointBounds17648 : List (Nat × Nat × Nat) := [(2317113344,98395253226384,98395632619411),(2317186048,98395668791051,98396048184337)]
theorem point_links_checked17648 : (cuts17648.take 2).map (fun c => (2317090817-1+2*2^9*c.k,98395122881434+c.lower,98395502274378+c.upper)) = pointBounds17648 := by
 decide +kernel
def cuts17649 : List PrefixCut := [⟨36,200060874,200061005⟩,
⟨107,607582739,607583117⟩,
⟨128,727468224,727468675⟩]
theorem checked17649 : checkPrefixCuts (2^48) 2317221889 9 Manual.Count131072.C017649.packed 128 cuts17649 = true := by
 decide +kernel
def pointBounds17649 : List (Nat × Nat × Nat) := [(2317258752,98396070130665,98396449524205),(2317331456,98396477652530,98396857046317)]
theorem point_links_checked17649 : (cuts17649.take 2).map (fun c => (2317221889-1+2*2^9*c.k,98395870069791+c.lower,98396249463200+c.upper)) = pointBounds17649 := by
 decide +kernel
def cuts17650 : List PrefixCut := [⟨50,292239067,292239248⟩,
⟨121,695970011,695970439⟩,
⟨128,736658202,736658655⟩]
theorem checked17650 : checkPrefixCuts (2^48) 2317352961 9 Manual.Count131072.C017650.packed 128 cuts17650 = true := by
 decide +kernel
def pointBounds17650 : List (Nat × Nat × Nat) := [(2317404160,98396889777082,98397269171123),(2317476864,98397293508026,98397672902314)]
theorem point_links_checked17650 : (cuts17650.take 2).map (fun c => (2317352961-1+2*2^9*c.k,98396597538015+c.lower,98396976931875+c.upper)) = pointBounds17650 := by
 decide +kernel
def cuts17651 : List PrefixCut := [⟨64,359507956,359508183⟩,
⟨128,728357504,728357959⟩]
theorem checked17651 : checkPrefixCuts (2^48) 2317484033 9 Manual.Count131072.C017651.packed 128 cuts17651 = true := by
 decide +kernel
def pointBounds17651 : List (Nat × Nat × Nat) := [(2317549568,98397693704173,98398073098713)]
theorem point_links_checked17651 : (cuts17651.take 1).map (fun c => (2317484033-1+2*2^9*c.k,98397334196217+c.lower,98397713590530+c.upper)) = pointBounds17651 := by
 decide +kernel
def cuts17652 : List PrefixCut := [⟨7,38499666,38499690⟩,
⟨78,447779263,447779537⟩,
⟨128,728802286,728802733⟩]
theorem checked17652 : checkPrefixCuts (2^48) 2317615105 9 Manual.Count131072.C017652.packed 128 cuts17652 = true := by
 decide +kernel
def pointBounds17652 : List (Nat × Nat × Nat) := [(2317622272,98398101053387,98398480448179),(2317694976,98398510332984,98398889728026)]
theorem point_links_checked17652 : (cuts17652.take 2).map (fun c => (2317615105-1+2*2^9*c.k,98398062553721+c.lower,98398441948489+c.upper)) = pointBounds17652 := by
 decide +kernel
def cuts17653 : List PrefixCut := [⟨21,123264437,123264514⟩,
⟨92,522560223,522560549⟩,
⟨128,731311213,731311668⟩]
theorem checked17653 : checkPrefixCuts (2^48) 2317746177 9 Manual.Count131072.C017653.packed 128 cuts17653 = true := by
 decide +kernel
def pointBounds17653 : List (Nat × Nat × Nat) := [(2317767680,98398914620444,98399294015736),(2317840384,98399313916230,98399693311771)]
theorem point_links_checked17653 : (cuts17653.take 2).map (fun c => (2317746177-1+2*2^9*c.k,98398791356007+c.lower,98399170751222+c.upper)) = pointBounds17653 := by
 decide +kernel
def cuts17654 : List PrefixCut := [⟨35,206319015,206319143⟩,
⟨106,607775618,607775988⟩,
⟨128,735763064,735763515⟩]
theorem checked17654 : checkPrefixCuts (2^48) 2317877249 9 Manual.Count131072.C017654.packed 128 cuts17654 = true := by
 decide +kernel
def pointBounds17654 : List (Nat × Nat × Nat) := [(2317913088,98399728986235,98400108382033),(2317985792,98400130442838,98400509838878)]
theorem point_links_checked17654 : (cuts17654.take 2).map (fun c => (2317877249-1+2*2^9*c.k,98399522667220+c.lower,98399902062890+c.upper)) = pointBounds17654 := by
 decide +kernel
def cuts17655 : List PrefixCut := [⟨49,287177991,287178171⟩,
⟨120,697959081,697959510⟩,
⟨128,740578547,740579002⟩]
theorem checked17655 : checkPrefixCuts (2^48) 2318008321 9 Manual.Count131072.C017655.packed 128 cuts17655 = true := by
 decide +kernel
def pointBounds17655 : List (Nat × Nat × Nat) := [(2318058496,98400545608275,98400925004576),(2318131200,98400956389365,98401335785915)]
theorem point_links_checked17655 : (cuts17655.take 2).map (fun c => (2318008321-1+2*2^9*c.k,98400258430284+c.lower,98400637826405+c.upper)) = pointBounds17655 := by
 decide +kernel
def cuts17656 : List PrefixCut := [⟨63,361834877,361835101⟩,
⟨128,732522921,732523370⟩]
theorem checked17656 : checkPrefixCuts (2^48) 2318139393 9 Manual.Count131072.C017656.packed 128 cuts17656 = true := by
 decide +kernel
def pointBounds17656 : List (Nat × Nat × Nat) := [(2318203904,98401360843708,98401740240508)]
theorem point_links_checked17656 : (cuts17656.take 1).map (fun c => (2318139393-1+2*2^9*c.k,98400999008831+c.lower,98401378405407+c.upper)) = pointBounds17656 := by
 decide +kernel
def cuts17657 : List PrefixCut := [⟨6,33025079,33025099⟩,
⟨77,439396606,439396883⟩,
⟨128,735516544,735517002⟩]
theorem checked17657 : checkPrefixCuts (2^48) 2318270465 9 Manual.Count131072.C017657.packed 128 cuts17657 = true := by
 decide +kernel
def pointBounds17657 : List (Nat × Nat × Nat) := [(2318276608,98401764556831,98402143953876),(2318349312,98402170928358,98402550325660)]
theorem point_links_checked17657 : (cuts17657.take 2).map (fun c => (2318270465-1+2*2^9*c.k,98401731531752+c.lower,98402110928777+c.upper)) = pointBounds17657 := by
 decide +kernel
def cuts17658 : List PrefixCut := [⟨20,113031307,113031374⟩,
⟨91,528847085,528847407⟩,
⟨128,746522957,746523418⟩]
theorem checked17658 : checkPrefixCuts (2^48) 2318401537 9 Manual.Count131072.C017658.packed 128 cuts17658 = true := by
 decide +kernel
def pointBounds17658 : List (Nat × Nat × Nat) := [(2318422016,98402580079603,98402959477153),(2318494720,98402995895381,98403375293186)]
theorem point_links_checked17658 : (cuts17658.take 2).map (fun c => (2318401537-1+2*2^9*c.k,98402467048296+c.lower,98402846445779+c.upper)) = pointBounds17658 := by
 decide +kernel
def cuts17659 : List PrefixCut := [⟨34,195334645,195334766⟩,
⟨105,598377405,598377772⟩,
⟨128,726814307,726814753⟩]
theorem checked17659 : checkPrefixCuts (2^48) 2318532609 9 Manual.Count131072.C017659.packed 128 cuts17659 = true := by
 decide +kernel
def pointBounds17659 : List (Nat × Nat × Nat) := [(2318567424,98403408905898,98403788303963),(2318640128,98403811948658,98404191346969)]
theorem point_links_checked17659 : (cuts17659.take 2).map (fun c => (2318532609-1+2*2^9*c.k,98403213571253+c.lower,98403592969197+c.upper)) = pointBounds17659 := by
 decide +kernel
def cuts17660 : List PrefixCut := [⟨48,273015173,273015346⟩,
⟨119,675668604,675669026⟩,
⟨128,729807958,729808413⟩]
theorem checked17660 : checkPrefixCuts (2^48) 2318663681 9 Manual.Count131072.C017660.packed 128 cuts17660 = true := by
 decide +kernel
def pointBounds17660 : List (Nat × Nat × Nat) := [(2318712832,98404213400733,98404592799296),(2318785536,98404616054164,98404995452976)]
theorem point_links_checked17660 : (cuts17660.take 2).map (fun c => (2318663681-1+2*2^9*c.k,98403940385560+c.lower,98404319783950+c.upper)) = pointBounds17660 := by
 decide +kernel
def cuts17661 : List PrefixCut := [⟨62,355541884,355542100⟩,
⟨128,733893845,733894290⟩]
theorem checked17661 : checkPrefixCuts (2^48) 2318794753 9 Manual.Count131072.C017661.packed 128 cuts17661 = true := by
 decide +kernel
def pointBounds17661 : List (Nat × Nat × Nat) := [(2318858240,98405025735402,98405405134463)]
theorem point_links_checked17661 : (cuts17661.take 1).map (fun c => (2318794753-1+2*2^9*c.k,98404670193518+c.lower,98405049592363+c.upper)) = pointBounds17661 := by
 decide +kernel
def cuts17662 : List PrefixCut := [⟨5,28524639,28524657⟩,
⟨76,432718124,432718392⟩,
⟨128,728997244,728997696⟩]
theorem checked17662 : checkPrefixCuts (2^48) 2318925825 9 Manual.Count131072.C017662.packed 128 cuts17662 = true := by
 decide +kernel
def pointBounds17662 : List (Nat × Nat × Nat) := [(2318930944,98405432612002,98405812011310),(2319003648,98405836805487,98406216205045)]
theorem point_links_checked17662 : (cuts17662.take 2).map (fun c => (2318925825-1+2*2^9*c.k,98405404087363+c.lower,98405783486653+c.upper)) = pointBounds17662 := by
 decide +kernel
def cuts17663 : List PrefixCut := [⟨19,112635274,112635342⟩,
⟨90,514497356,514497675⟩,
⟨128,738665705,738666163⟩]
theorem checked17663 : checkPrefixCuts (2^48) 2319056897 9 Manual.Count131072.C017663.packed 128 cuts17663 = true := by
 decide +kernel
def pointBounds17663 : List (Nat × Nat × Nat) := [(2319076352,98406245719881,98406625119691),(2319149056,98406647581963,98407026982024)]
theorem point_links_checked17663 : (cuts17663.take 2).map (fun c => (2319056897-1+2*2^9*c.k,98406133084607+c.lower,98406512484349+c.upper)) = pointBounds17663 := by
 decide +kernel
def cuts17664 : List PrefixCut := [⟨33,187997427,187997540⟩,
⟨104,601727920,601728295⟩,
⟨128,744570593,744571057⟩]
theorem checked17664 : checkPrefixCuts (2^48) 2319187969 9 Manual.Count131072.C017664.packed 128 cuts17664 = true := by
 decide +kernel
def pointBounds17664 : List (Nat × Nat × Nat) := [(2319221760,98407059747739,98407439148052),(2319294464,98407473478232,98407852878807)]
theorem point_links_checked17664 : (cuts17664.take 2).map (fun c => (2319187969-1+2*2^9*c.k,98406871750312+c.lower,98407251150512+c.upper)) = pointBounds17664 := by
 decide +kernel
def cuts17665 : List PrefixCut := [⟨47,262865177,262865340⟩,
⟨118,662370999,662371410⟩,
⟨128,718558091,718558534⟩]
theorem checked17665 : checkPrefixCuts (2^48) 2319319041 9 Manual.Count131072.C017665.packed 128 cuts17665 = true := by
 decide +kernel
def pointBounds17665 : List (Nat × Nat × Nat) := [(2319367168,98407879186082,98408258586909),(2319439872,98408278691904,98408658092979)]
theorem point_links_checked17665 : (cuts17665.take 2).map (fun c => (2319319041-1+2*2^9*c.k,98407616320905+c.lower,98407995721569+c.upper)) = pointBounds17665 := by
 decide +kernel
def cuts17666 : List PrefixCut := [⟨61,352164964,352165184⟩,
⟨128,740360704,740361160⟩]
theorem checked17666 : checkPrefixCuts (2^48) 2319450113 9 Manual.Count131072.C017666.packed 128 cuts17666 = true := by
 decide +kernel
def pointBounds17666 : List (Nat × Nat × Nat) := [(2319512576,98408687043960,98409066445287)]
theorem point_links_checked17666 : (cuts17666.take 1).map (fun c => (2319450113-1+2*2^9*c.k,98408334878996+c.lower,98408714280103+c.upper)) = pointBounds17666 := by
 decide +kernel
def cuts17667 : List PrefixCut := [⟨4,21357104,21357117⟩,
⟨75,422645566,422645819⟩,
⟨128,734130108,734130550⟩]
theorem checked17667 : checkPrefixCuts (2^48) 2319581185 9 Manual.Count131072.C017667.packed 128 cuts17667 = true := by
 decide +kernel
def pointBounds17667 : List (Nat × Nat × Nat) := [(2319585280,98409096596804,98409475998380),(2319657984,98409497885266,98409877287082)]
theorem point_links_checked17667 : (cuts17667.take 2).map (fun c => (2319581185-1+2*2^9*c.k,98409075239700+c.lower,98409454641263+c.upper)) = pointBounds17667 := by
 decide +kernel
def cuts17668 : List PrefixCut := [⟨18,102653596,102653661⟩,
⟨89,510833134,510833446⟩,
⟨128,738092903,738093349⟩]
theorem checked17668 : checkPrefixCuts (2^48) 2319712257 9 Manual.Count131072.C017668.packed 128 cuts17668 = true := by
 decide +kernel
def pointBounds17668 : List (Nat × Nat × Nat) := [(2319730688,98409912023404,98410291425474),(2319803392,98410320202942,98410699605259)]
theorem point_links_checked17668 : (cuts17668.take 2).map (fun c => (2319712257-1+2*2^9*c.k,98409809369808+c.lower,98410188771813+c.upper)) = pointBounds17668 := by
 decide +kernel
def cuts17669 : List PrefixCut := [⟨32,181149732,181149849⟩,
⟨103,590031637,590032003⟩,
⟨128,733197978,733198432⟩]
theorem checked17669 : checkPrefixCuts (2^48) 2319843329 9 Manual.Count131072.C017669.packed 128 cuts17669 = true := by
 decide +kernel
def pointBounds17669 : List (Nat × Nat × Nat) := [(2319876096,98410728612443,98411108015011),(2319948800,98411137494348,98411516897165)]
theorem point_links_checked17669 : (cuts17669.take 2).map (fun c => (2319843329-1+2*2^9*c.k,98410547462711+c.lower,98410926865162+c.upper)) = pointBounds17669 := by
 decide +kernel
def cuts17670 : List PrefixCut := [⟨46,267037410,267037572⟩,
⟨117,682930469,682930886⟩,
⟨128,748200720,748201177⟩]
theorem checked17670 : checkPrefixCuts (2^48) 2319974401 9 Manual.Count131072.C017670.packed 128 cuts17670 = true := by
 decide +kernel
def pointBounds17670 : List (Nat × Nat × Nat) := [(2320021504,98411547698099,98411927101166),(2320094208,98411963591158,98412342994480)]
theorem point_links_checked17670 : (cuts17670.take 2).map (fun c => (2319974401-1+2*2^9*c.k,98411280660689+c.lower,98411660063594+c.upper)) = pointBounds17670 := by
 decide +kernel
def cuts17671 : List PrefixCut := [⟨60,348547374,348547591⟩,
⟨128,749250263,749250724⟩]
theorem checked17671 : checkPrefixCuts (2^48) 2320105473 9 Manual.Count131072.C017671.packed 128 cuts17671 = true := by
 decide +kernel
def pointBounds17671 : List (Nat × Nat × Nat) := [(2320166912,98412377408783,98412756812362)]
theorem point_links_checked17671 : (cuts17671.take 1).map (fun c => (2320105473-1+2*2^9*c.k,98412028861409+c.lower,98412408264771+c.upper)) = pointBounds17671 := by
 decide +kernel
def cuts17672 : List PrefixCut := [⟨3,18075627,18075638⟩,
⟨74,427257403,427257665⟩,
⟨128,739745817,739746275⟩]
theorem checked17672 : checkPrefixCuts (2^48) 2320236545 9 Manual.Count131072.C017672.packed 128 cuts17672 = true := by
 decide +kernel
def pointBounds17672 : List (Nat × Nat × Nat) := [(2320239616,98412796187299,98413175591133),(2320312320,98413205369075,98413584773160)]
theorem point_links_checked17672 : (cuts17672.take 2).map (fun c => (2320236545-1+2*2^9*c.k,98412778111672+c.lower,98413157515495+c.upper)) = pointBounds17672 := by
 decide +kernel
def cuts17673 : List PrefixCut := [⟨17,95346280,95346340⟩,
⟨88,508990698,508991015⟩,
⟨128,738854945,738855404⟩]
theorem checked17673 : checkPrefixCuts (2^48) 2320367617 9 Manual.Count131072.C017673.packed 128 cuts17673 = true := by
 decide +kernel
def pointBounds17673 : List (Nat × Nat × Nat) := [(2320385024,98413613203769,98413992608110),(2320457728,98414026848187,98414406252785)]
theorem point_links_checked17673 : (cuts17673.take 2).map (fun c => (2320367617-1+2*2^9*c.k,98413517857489+c.lower,98413897261770+c.upper)) = pointBounds17673 := by
 decide +kernel
def cuts17674 : List PrefixCut := [⟨31,175518897,175519004⟩,
⟨102,588894747,588895108⟩,
⟨128,738327909,738328363⟩]
theorem checked17674 : checkPrefixCuts (2^48) 2320498689 9 Manual.Count131072.C017674.packed 128 cuts17674 = true := by
 decide +kernel
def pointBounds17674 : List (Nat × Nat × Nat) := [(2320530432,98414432231331,98414811636178),(2320603136,98414845607181,98415225012282)]
theorem point_links_checked17674 : (cuts17674.take 2).map (fun c => (2320498689-1+2*2^9*c.k,98414256712434+c.lower,98414636117174+c.upper)) = pointBounds17674 := by
 decide +kernel
def cuts17675 : List PrefixCut := [⟨45,265506573,265506731⟩,
⟨116,680312025,680312435⟩,
⟨128,747504428,747504880⟩]
theorem checked17675 : checkPrefixCuts (2^48) 2320629761 9 Manual.Count131072.C017675.packed 128 cuts17675 = true := by
 decide +kernel
def pointBounds17675 : List (Nat × Nat × Nat) := [(2320675840,98415260546916,98415639952268),(2320748544,98415675352368,98416054757972)]
theorem point_links_checked17675 : (cuts17675.take 2).map (fun c => (2320629761-1+2*2^9*c.k,98414995040343+c.lower,98415374445537+c.upper)) = pointBounds17675 := by
 decide +kernel
def cuts17676 : List PrefixCut := [⟨59,341171997,341172206⟩,
⟨128,737516987,737517443⟩]
theorem checked17676 : checkPrefixCuts (2^48) 2320760833 9 Manual.Count131072.C017676.packed 128 cuts17676 = true := by
 decide +kernel
def pointBounds17676 : List (Nat × Nat × Nat) := [(2320821248,98416083716768,98416463122623)]
theorem point_links_checked17676 : (cuts17676.take 1).map (fun c => (2320760833-1+2*2^9*c.k,98415742544771+c.lower,98416121950417+c.upper)) = pointBounds17676 := by
 decide +kernel
def cuts17677 : List PrefixCut := [⟨2,12127870,12127878⟩,
⟨73,427500734,427501001⟩,
⟨128,746813538,746814000⟩]
theorem checked17677 : checkPrefixCuts (2^48) 2320891905 9 Manual.Count131072.C017677.packed 128 cuts17677 = true := by
 decide +kernel
def pointBounds17677 : List (Nat × Nat × Nat) := [(2320893952,98416492189628,98416871595738),(2320966656,98416907562492,98417286968861)]
theorem point_links_checked17677 : (cuts17677.take 2).map (fun c => (2320891905-1+2*2^9*c.k,98416480061758+c.lower,98416859467860+c.upper)) = pointBounds17677 := by
 decide +kernel
def cuts17678 : List PrefixCut := [⟨16,94713031,94713086⟩,
⟨87,495871337,495871642⟩,
⟨128,728581116,728581565⟩]
theorem checked17678 : checkPrefixCuts (2^48) 2321022977 9 Manual.Count131072.C017678.packed 128 cuts17678 = true := by
 decide +kernel
def pointBounds17678 : List (Nat × Nat × Nat) := [(2321039360,98417321588327,98417700994946),(2321112064,98417722746633,98418102153502)]
theorem point_links_checked17678 : (cuts17678.take 2).map (fun c => (2321022977-1+2*2^9*c.k,98417226875296+c.lower,98417606281860+c.upper)) = pointBounds17678 := by
 decide +kernel
def cuts17679 : List PrefixCut := [⟨30,170618821,170618926⟩,
⟨101,581331771,581332126⟩,
⟨128,734118033,734118480⟩]
theorem checked17679 : checkPrefixCuts (2^48) 2321154049 9 Manual.Count131072.C017679.packed 128 cuts17679 = true := by
 decide +kernel
def pointBounds17679 : List (Nat × Nat × Nat) := [(2321184768,98418126075233,98418505482351),(2321257472,98418536788183,98418916195551)]
theorem point_links_checked17679 : (cuts17679.take 2).map (fun c => (2321154049-1+2*2^9*c.k,98417955456412+c.lower,98418334863425+c.upper)) = pointBounds17679 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000239
